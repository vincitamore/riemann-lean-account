"""Build references.bib from researched reference records, re-checking each against its source.

Inputs: JSON Lines files. A line is either a reference object, or a literature-row object with a
"refs" list of reference objects. Fields used: key, authors, title, year, type, venue, booktitle,
volume, number, pages, doi, zbl, mr, arxiv, url, fetched, note.

Every record was researched against a fetched source. This script checks each one a second time:

* a reference with a DOI: the Crossref record is fetched (and kept under evidence/crossref/) and
  compared with the researched fields: title words, year, volume and first page. A disagreement is
  reported for inspection by hand;
* a reference without a DOI: its recorded page (zbMATH, arXiv, publisher) is fetched and must
  contain the first author's family name and a word of the title.

The bibliography takes its fields from the researched record, which carries the judgment made
where the databases disagree. Outcomes are written to evidence/report.tsv. Three optional files
beside the inputs adjust the result: same.json (two keys for one source), aliases.json (short keys
used in the text), overrides.json (fields set by hand, each with its reason in the file).

Usage: python tools/build_bib.py out.bib evidence_dir in1.jsonl [in2.jsonl ...]

Where two inputs describe one source, the record read first is the one used and gives the entry
its key, so the order of the inputs matters. The paper's bibliography is built, in the paper's
directory, with
    python tools/build_bib.py references.bib refs/evidence \
        refs/rows-A.jsonl refs/rows-B.jsonl refs/rows-C.jsonl refs/account.jsonl
"""
import html
import json
import os
import re
import sys
import time
import unicodedata
import urllib.parse
import urllib.request

UA = {"User-Agent": "riemann-lean-account/1.0 (mailto:vincit_amore@amore.build)"}


def fetch(url: str, tries: int = 3) -> tuple[int, bytes]:
    last = (0, b"")
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers=UA)
            with urllib.request.urlopen(req, timeout=40) as r:
                return r.status, r.read()
        except Exception as e:  # noqa: BLE001
            code = getattr(e, "code", 0) or 0
            last = (code, str(e).encode())
            time.sleep(2 + 3 * i)
    return last


def ascii_fold(s: str) -> str:
    return "".join(c for c in unicodedata.normalize("NFKD", s) if not unicodedata.combining(c))


def words(s: str) -> list[str]:
    return re.findall(r"[a-z]{4,}", ascii_fold(s).lower())


MATH = {
    "μ": r"$\mu$", "θ": r"$\theta$", "ψ": r"$\psi$", "λ": r"$\lambda$", "ζ": r"$\zeta$", "Γ": r"$\Gamma$",
    "π": r"$\pi$", "ℓ": r"$\ell$", "ℤ": r"$\mathbb{Z}$", "ℚ": r"$\mathbb{Q}$", "∞": r"$\infty$",
    "𝜃": r"$\theta$", "𝑥": r"$x$", "𝜓": r"$\psi$", "𝑝": r"$p$", "𝐿": r"$L$", "≤": r"$\le$",
    "–": "--", "—": "---", "’": "'", "‘": "`", "“": "``", "”": "''", "\u00a0": "~", "\u2009": " ",
    "\u200b": "", "\ufffd": "", "ε": r"$\varepsilon$", "²": r"$^2$",
}
TEX = {"&": r"\&", "%": r"\%", "#": r"\#", "_": r"\_"}


def tex(s: str) -> str:
    """Plain text to BibTeX field text. Keeps `$...$` and existing TeX commands as they are."""
    s = html.unescape(html.unescape(s or ""))
    s = re.sub(r"<[^>]+>", "", s)
    s = re.sub(r"\s+", " ", s).strip()
    out = []
    for part in re.split(r"(\$[^$]*\$)", s):
        if part.startswith("$") and part.endswith("$") and len(part) > 1:
            out.append(part)
            continue
        part = "".join(TEX.get(c, c) for c in part)
        for a, b in MATH.items():
            part = part.replace(a, b)
        out.append(part)
    return "".join(out)

# Mathematics in titles, which the records carry as plain text.
TITLE_MATH = [
    (re.compile(r"GL\\_2\(Z\\_p\[\[X\]\]\)"), r"$\\mathrm{GL}_2(\\mathbb{Z}_p[[X]])$"),
    (re.compile(r"Z\\_\$\\ell\$-extensions"), r"$\\mathbb{Z}_\\ell$-extensions"),
    (re.compile(r"Q\(\$\\mu\$\\_p\)"), r"$\\mathbb{Q}(\\mu_p)$"),
    (re.compile(r"\$\\mu\$\\_p"), r"$\\mu_p$"),
    (re.compile(r"L\$\^2\$"), r"$L^2$"),
    (re.compile(r"\$\\(theta|psi)\$\(x\)"), r"$\\\1(x)$"),
    (re.compile(r"\b(GL|SL|Sp|GSp|PGL|SU|U)\(([A-Za-z0-9,]+)\)"), r"$\\mathrm{\1}(\2)$"),
    (re.compile(r"\b(GL|SL|Sp|GSp)\\_([A-Za-z0-9])"), r"$\\mathrm{\1}_\2$"),
    (re.compile(r"\bwhere ([FK]) is\b"), r"where $\1$ is"),
    (re.compile(r"(?<!\$)\bl-(adic|adiques?)\b"), r"$\\ell$-\1"),
    (re.compile(r"(?<!\$)\b([pP])-(adic|adiques?|divisible|extensions?|invariant)\b"), r"$\1$-\2"),
    (re.compile(r"(?<!\$)\b([LK])-(functions?|series|values?|types?|Functions?)\b"), r"$\1$-\2"),
    (re.compile(r"\bfonctions L\b"), r"fonctions $L$"),
    (re.compile(r"(?<!\$)\bF-crystals\b"), r"$F$-crystals"),
    (re.compile(r"\bfor l ?= ?p\b"), r"for $\\ell=p$"),
]


def title_math(s: str) -> str:
    for rx, to in TITLE_MATH:
        s = rx.sub(to, s)
    return s


def name(a: dict | str) -> str:
    if isinstance(a, str):
        return tex(a)
    fam, giv = a.get("family", ""), a.get("given", "")
    if not fam and a.get("name"):
        return "{" + tex(a["name"]) + "}"
    return tex(f"{fam}, {giv}" if giv else fam)


def crossref(doi: str, evdir: str) -> dict | None:
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", doi)
    path = os.path.join(evdir, "crossref", safe + ".json")
    if os.path.exists(path):
        data = json.load(open(path, encoding="utf-8"))
    else:
        code, body = fetch("https://api.crossref.org/works/" + urllib.parse.quote(doi, safe="/"))
        if code != 200:
            return None
        data = json.loads(body)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        json.dump(data, open(path, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
        time.sleep(0.3)
    m = data.get("message", {})
    years = []
    for k in ("published-print", "issued", "published-online"):
        parts = (m.get(k) or {}).get("date-parts") or [[None]]
        if parts[0] and parts[0][0]:
            years.append(int(parts[0][0]))
    return {
        "title": html.unescape((m.get("title") or [""])[0]),
        "years": years,
        "volume": str(m.get("volume", "") or ""),
        "issue": str(m.get("issue", "") or ""),
        "page": str(m.get("page", "") or ""),
    }


def first_page(p: str) -> str:
    m = re.match(r"\s*([A-Za-z]?\d+)", str(p or ""))
    return m.group(1) if m else ""


def compare(ref: dict, cr: dict) -> list[str]:
    """Disagreements between the researched record and the Crossref record."""
    out = []
    tw, cw = set(words(ref.get("title", ""))), set(words(cr["title"]))
    if tw and cw and len(tw & cw) / min(len(tw), len(cw)) < 0.5:
        out.append("title")
    try:
        y = int(ref.get("year") or 0)
    except ValueError:
        y = 0
    if y and cr["years"] and all(abs(y - c) > 1 for c in cr["years"]):
        out.append(f"year {y} vs {cr['years']}")
    rv = str(ref.get("volume", "") or "")
    # Crossref files some journals with the year as volume and the volume as issue.
    if rv and cr["volume"] and rv != cr["volume"] and rv != cr["issue"] and not rv.isalpha():
        if re.fullmatch(r"\d+", rv) and re.fullmatch(r"\d+", cr["volume"]):
            out.append(f"volume {rv} vs {cr['volume']}")
    rp, cp = first_page(ref.get("pages", "")), first_page(cr["page"])
    if rp and cp and rp != cp:
        out.append(f"first page {rp} vs {cp}")
    return out


def check_url(ref: dict) -> str:
    urls = [u for u in (ref.get("fetched") or []) if u.startswith("http")] or ([ref["url"]] if ref.get("url") else [])
    if ref.get("zbl") and not str(ref["zbl"]).startswith("JFM"):
        urls.insert(0, "https://zbmath.org/?q=an%3A" + urllib.parse.quote(str(ref["zbl"])))
    if ref.get("arxiv"):
        urls.insert(0, "https://arxiv.org/abs/" + str(ref["arxiv"]))
    fam = ""
    if ref.get("authors"):
        a0 = ref["authors"][0]
        fam = ascii_fold(a0.split(",")[0] if isinstance(a0, str) else a0.get("family", "")).lower()
    tw = words(ref.get("title", ""))
    seen200 = ""
    for u in urls[:6]:
        code, body = fetch(u, tries=2)
        if code != 200:
            continue
        seen200 = seen200 or u
        text = ascii_fold(html.unescape(body.decode("utf-8", "replace"))).lower()
        if (not fam or fam in text) and (not tw or any(w in text for w in tw[:6])):
            return "url-confirmed\t" + u
    return ("url-200-no-match\t" + seen200) if seen200 else ("unconfirmed\t" + (urls[0] if urls else ""))


def entry(key: str, ref: dict, ids: list[str]) -> str:
    kind = ref.get("type", "article")
    f: dict[str, str] = {}
    if ids:
        f["ids"] = ", ".join(sorted(ids))
    authors = [name(a) for a in ref.get("authors", [])]
    if authors:
        f["author"] = " and ".join(authors)
    title = title_math(tex(ref.get("title", ""))).rstrip(".")
    f["title"] = "{" + title + "}"
    f["year"] = str(ref.get("year", ""))
    venue = tex(ref.get("venue", ""))
    if kind == "article":
        f["journal"] = venue
    elif kind == "incollection":
        f["booktitle"] = title_math(tex(ref.get("booktitle", ""))) or venue
        if ref.get("booktitle") and venue:
            f["publisher"] = venue
    elif kind in ("book", "thesis"):
        f["publisher"] = venue
        if kind == "thesis":
            f["type"] = "phdthesis"
    else:
        f["howpublished"] = venue
    for k in ("volume", "number", "pages"):
        v = str(ref.get(k, "") or "")
        if v:
            f[k] = tex(v) if k != "pages" else v.replace("–", "--").replace("—", "--")
    if kind in ("book", "incollection") and f.get("volume") and not f["volume"].isdigit():
        f["series"] = f.pop("volume")
    if ref.get("doi"):
        f["doi"] = ref["doi"]
    elif ref.get("url"):
        f["url"] = ref["url"]
    if ref.get("arxiv"):
        f["eprint"] = str(ref["arxiv"])
        f["eprinttype"] = "arxiv"
    ident = []
    if ref.get("zbl"):
        z = str(ref["zbl"])
        ident.append(z if z.startswith("JFM") else "Zbl " + z)
    if ref.get("mr"):
        ident.append("MR " + str(ref["mr"]))
    if ref.get("bibnote"):
        ident.append(tex(ref["bibnote"]))
    if ident:
        f["note"] = ", ".join(ident)
    btype = {"article": "article", "book": "book", "incollection": "incollection",
             "thesis": "thesis", "misc": "misc"}.get(kind, "misc")
    body = ",\n".join(f"  {k} = {v}" if (v.startswith("{") and k == "title") else f"  {k} = {{{v}}}"
                      for k, v in f.items() if v)
    return f"@{btype}{{{key},\n{body}\n}}\n"


def ident_of(r: dict) -> str:
    """One identity per source: DOI if there is one, else the Zbl number, else the proposed key."""
    if r.get("doi"):
        return "doi:" + r["doi"].lower()
    if r.get("zbl"):
        return "zbl:" + str(r["zbl"])
    return "key:" + r.get("key", "")


def main() -> None:
    out, evdir, inputs = sys.argv[1], sys.argv[2], sys.argv[3:]
    refs: dict[str, dict] = {}
    by_ident: dict[str, str] = {}
    for p in inputs:
        for line in open(p, encoding="utf-8"):
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            for r in (obj.get("refs") if "refs" in obj else [obj]) or []:
                k = r.get("key")
                if not k:
                    continue
                ident = ident_of(r)
                if ident in by_ident:
                    continue
                canon = k
                while canon in refs:  # one key proposed for two different sources
                    canon += "x"
                by_ident[ident] = canon
                refs[canon] = r
    os.makedirs(evdir, exist_ok=True)
    refsdir = os.path.dirname(inputs[0])

    def load(name: str) -> dict:
        p = os.path.join(refsdir, name)
        return json.load(open(p, encoding="utf-8")) if os.path.exists(p) else {}

    for drop, keep in load("same.json").items():
        if drop in refs and keep in refs:
            del refs[drop]
            for ident, key in list(by_ident.items()):
                if key == drop:
                    by_ident[ident] = keep
    json.dump(by_ident, open(os.path.join(evdir, "identmap.json"), "w", encoding="utf-8"), indent=1, sort_keys=True)
    aliases: dict[str, list[str]] = {}
    for short, key in load("aliases.json").items():
        if key not in refs:
            print(f"  alias {short} -> {key}: no such entry")
            continue
        aliases.setdefault(key, []).append(short)
    overrides = load("overrides.json")
    inspected = load("inspected.json")
    cache_path = os.path.join(evdir, "urlcheck.json")
    urlcache = json.load(open(cache_path, encoding="utf-8")) if os.path.exists(cache_path) else {}

    report = ["key\tstatus\tdetail"]
    entries = []
    for k in sorted(refs):
        r = dict(refs[k])
        if r.get("doi"):
            cr = crossref(r["doi"], evdir)
            if cr is None:
                status = "doi-not-resolved\t" + r["doi"]
            else:
                diff = compare(r, cr)
                status = ("crossref-agrees\t" + r["doi"]) if not diff else ("crossref-differs\t" + "; ".join(diff))
        else:
            status = urlcache.get(ident_of(r)) or check_url(r)
            if status.startswith("url-confirmed"):
                urlcache[ident_of(r)] = status
                json.dump(urlcache, open(cache_path, "w", encoding="utf-8"), indent=1, sort_keys=True)
        if k in inspected and not status.startswith(("crossref-agrees", "url-confirmed")):
            status = "inspected-by-hand\t" + inspected[k] + " [was: " + status.replace("\t", " ") + "]"
        report.append(f"{k}\t{status}")
        for field, value in (overrides.get(k) or {}).items():
            if field != "reason":
                r[field] = value
        entries.append(entry(k, r, aliases.get(k, [])))
    open(out, "w", encoding="utf-8", newline="\n").write(
        "% Generated by tools/build_bib.py; do not edit by hand. Each entry was researched against a\n"
        "% fetched record and checked a second time by the script; see refs/evidence/report.tsv.\n\n"
        + "\n".join(entries))
    open(os.path.join(evdir, "report.tsv"), "w", encoding="utf-8", newline="\n").write("\n".join(report) + "\n")
    ok = ("crossref-agrees", "url-confirmed", "inspected-by-hand")
    bad = [l for l in report[1:] if not l.split("\t")[1].startswith(ok)]
    print(f"{len(entries)} entries; {len(bad)} need attention")
    for l in bad:
        print("  " + l)


if __name__ == "__main__":
    main()
