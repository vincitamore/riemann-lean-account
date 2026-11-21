# Review B of the kernel replay program

**Reviewed.** `verify/replay/ReplayMain.lean`, sha256 `23bfda99917b90a89324a1ae8a06aec2fbc50bcdc987f86cdf8e9d98be731e39`, the version committed at `fbc765453` (blob `3b91abc66`). The recorded run in `verify/results/replay-*.txt` was made by the earlier blob `9df3afd18` (commit `0d6d0f121`): its summary has no `root`, `threads`, `quotient-constants` or `sum-of-the-kinds` lines, and `git diff 0d6d0f121 HEAD` shows the two versions differ only in those report lines. Everything below applies to both. Line numbers are those of the reviewed file.

**Read.** Lean at tag `v4.33.1`, from `https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/`: `src/Lean/Replay.lean`, `src/LeanChecker.lean` (where `leanchecker` lives at this tag), `src/Lean/Environment.lean`, `src/Lean/AddDecl.lean`, `src/Lean/Declaration.lean`, `src/Lean/Expr.lean`, `src/Lean/Setup.lean`, `src/Lean/Elab/Frontend.lean`, `src/Lean/Elab/BuiltinEvalCommand.lean`, `src/Lean/Util/FoldConsts.lean`, `src/Lean/Util/PtrSet.lean`, `src/kernel/{environment.cpp, environment.h, quot.cpp, inductive.cpp, inductive.h, type_checker.cpp, kernel_exception.h}`, `src/library/ir_interpreter.cpp`.

**Limits.** No Lean toolchain was available, so nothing here was compiled or run. Every outcome below is a prediction from the source, and the fixture code is untested. `[INFERENCE]` marks a prediction that rests on behaviour I could not read directly. I did not read review A.

## Verdict

Yes. There are inputs on which the program prints `failed 0` and exits 0 although the kernel rejects a declaration of the stored environment, and on which Lean's own `Environment.replay` (so `leanchecker` and `leanchecker --fresh`) fails.

- The strongest is **T12**: a stored inductive type whose constructor list names a constructor that exists nowhere in the closure, together with a theorem that is true only if the type has one constructor. The program builds the type without the missing constructor, accepts the theorem, and leaves no trace in any count (finding 1).
- The second is **T9**: a constant stored under a key that differs from its own name, which makes line 185 skip an inductive type of that name (finding 2). The `sum-of-the-kinds` line shows it; the exit code does not.

Both need a hand-written `.olean`. Lean's front end cannot write either: `mkModuleData` derives `constNames` from the constants (Environment.lean:1881), and a compiled file's inductive metadata comes from the kernel. Every front-end bypass I could build is reported as a failure. This covers `debug.skipKernelTC`, `Environment.addDeclCore (doCheck := false)`, `Kernel.Environment.addDeclWithoutChecking`, theorems that use unsafe or partial constants, unknown constants and duplicate names; a tampered recursor in a crafted file (T6) is reported too. A malicious `.olean` is still the threat model that matters here: the Mathlib files came from the community cache, and in this pipeline the replay is the only kernel pass they received.

**The recorded run.** Its counts close exactly: 2,084,256 + 556,318 + 3,882 + 7 + 15,769 + 19,159 + 15,897 = 2,695,288, which is 2,695,292 minus the four quotient constants. That rules out the T9 and T11 patterns in the published files `[INFERENCE: each adds one to that residue, and no other path changes it without a reported failure]`. It does not rule out T12, which changes no count. The audit program in Step 1 of the protocol settles T12 for the published files in minutes, without a new replay.

## Findings

**1. A constructor named by an inductive type but absent from the closure is dropped silently** (lines 186-195, especially 190-191; also 86-89). Severity: **unsound** (crafted `.olean`).

- **What goes wrong.** The constructor list sent to the kernel is built with `filterMap`, so a name in `w.ctors` with no entry in `all` disappears. The kernel then builds a type with fewer constructors than the stored `InductiveVal` lists. The stored `InductiveVal` is never compared with the one the kernel generated, and later checks use the kernel's.
- **Scenario (T12).** The stored module holds `inductive Ph12 : Type` with `ctors = [Ph12.a, Ph12.b]`. Its `Ph12.a`, `Ph12.rec` and auxiliary definitions are copied from a compiled one-constructor `inductive Ph12 | a`. No `Ph12.b` exists anywhere. A downstream module holds `allEq : ∀ x y : Ph12, x = y := fun x y => Eq.refl x`.
  - The program adds `Ph12` with one constructor. The stored `Ph12.a` and `Ph12.rec` equal the generated ones, so lines 267-274 pass.
  - `allEq` is accepted by unit-like eta: `is_def_eq_unit_like`, type_checker.cpp:1159-1169, reads the kernel's own one-constructor `InductiveVal` through `is_non_rec_structure`, inductive.cpp:28-33.
  - In the stored environment `Ph12` has two constructors, is not unit-like, and the kernel rejects `allEq`.
  - Lean's replay reads constructors with `newConstants[n]!` (Replay.lean:111). It panics on `Ph12.b`, substitutes the default `ConstantInfo` (an axiom of type `.const _inhabitedExprDummy []`, Expr.lean:516-518), and the kernel rejects the block.
- **Fix.** Fail when `all[c]?` is `none`, or is not a `ctorInfo` whose `induct` is `w.name`. More generally, apply the fix of finding 3.

**2. A key that differs from the stored name hides an inductive type** (lines 221-231 and 185). Severity: **unsound** (crafted `.olean`).

- **What goes wrong.** `all` is keyed by `md.constNames[j]`, but the kernel adds the declaration under `md.constants[j].name` (lines 224-225, 140-146). Line 185 then reads "some constant named `n` is in the kernel environment" as "the mutual block of `n` was added".
- **Scenario (T9).** One stored module holds three entries, in this order:
  1. key `phantomBody`, holding `def Phantom : Type := Nat`;
  2. key `Phantom`, holding an `InductiveVal` for `Phantom : Type` with no constructors;
  3. `phantom_nonempty : Nonempty Phantom := Nonempty.intro 0`, with `0` a raw literal.

  `phantomBody` is emitted first and adds the definition `Phantom`. At `Phantom`, line 185 finds that constant and returns without adding or counting anything. `phantom_nonempty` is then checked against `Phantom := Nat` and accepted. The result is `failed 0` and exit 0, with `sum-of-the-kinds ... (equals replayed: false)` in the current summary.

  In the stored environment `Phantom` is an inductive type with no constructors, and the kernel rejects the theorem. Lean's replay sends both declarations under the name `Phantom` and gets `already declared`, or a type mismatch, depending on the order (environment.cpp:102, inductive.cpp:259).
- **Fix.** When building `all`, fail unless `ci.name == n`. At line 185, test membership in a set of the names of blocks actually added at line 195, not `find?`.

**3. The replayed environment is compared with the stored one only at constructors and recursors** (lines 183-203, 266-274). Severity: **gap** (shared with Lean's replay, Replay.lean:129-133, 148-168).

- **What is not checked.** Stored `inductInfo` and `quotInfo` constants are never compared with what the kernel built. Constants the kernel generated that are missing from the stored environment are not reported.
- **Scenarios.**
  - (a) **T11.** A stored `quotInfo` named `cheat` with type `False` is counted at line 200 and never added. If nothing uses it, the run passes and only `quotient-constants 5` shows it. If a theorem uses it (T10), that theorem fails with an unknown constant, so no theorem can rest on it.
  - (b) A stored inductive type without its `.rec`, plus a theorem whose proof uses `T.rec`. The program adds `T`, the kernel generates `T.rec`, and the theorem is accepted. In the stored environment `T.rec` does not exist.
  - (c) A stored `InductiveVal` whose derived fields (`isRec`, `numIndices`, `isReflexive`) differ from the kernel's. Checks run against the kernel's.

  (b) and (c) also pass Lean's replay. (b) and (c) change no statement's truth; (a) is a constant no kernel declaration produces.
- **Fix.** After `drain`, check both directions:
  - for every name `n` that was not skipped, `kenv.find? n` must equal `all[n]` field for field;
  - every constant in `kenv` must be a key of `all`.

  `InductiveVal` and `QuotVal` derive no `BEq` at this tag (Declaration.lean:261-302, 418-420), so compare their fields by hand, and compare `QuotKind` with a `match`. This replaces lines 266-274, closes findings 1 and 2 and the three cases above, and costs one pass over 2.7 million names.

**4. A duplicated name keeps the last version read, not the one Lean keeps** (lines 226-231; also 160-165 and 181). Severity: **fragile**.

- **Which version wins.** `finalizeImport` keeps a theorem over an axiom of the same name and type, whichever comes later (`subsumesInfo`, Environment.lean:2268-2283, applied at 2335-2343). Line 231 keeps the later one. For a theorem followed by an axiom, the replayed environment therefore holds an axiom where Lean presents a theorem, and `replay-axioms.txt` lists it.
- **Axiom versions.** An axiom alternate is neither checked nor listed (line 165). That is harmless, because the main version has the same type. Equal types are guaranteed at import, so `nAltDiff` is always 0 and that summary field tests nothing.
- **Rejected axioms.** Line 181 records an axiom before its check, so an axiom the kernel rejects still appears in `replay-axioms.txt` (T8).
- **Fix.** Take the main table from `env.constants.map₁`, which is the environment Lean presents, and treat the other module-data versions as alternates. Record an axiom only after its check succeeds.

**5. `constNames` and `constants` are indexed separately** (lines 223-225). Severity: **fragile**.

If `constants` is shorter than `constNames`, `md.constants[j]!` panics and yields the default `ConstantInfo`, which then fails its check. `finalizeImport` zips the two arrays and would have ignored the extra names. The program fails closed, but only through a panic. Fix: zip the arrays, and fail when their sizes differ.

**6. The self-test covers one path** (lines 276-282). Severity: **note**.

It shows that `spawnCheck` rejects one false proof against the final environment. It does not exercise the window and drain of `checkedLater`, the alternates, the inductive blocks or the comparisons. Fix: run the fixtures below as a regression suite, with the expected outcome of each, before every published run.

**7. Statements in the header comment and in the paper that the source does not bear out** (lines 1-29). Severity: **note**.

- (a) **The `getUsedConstants` claim.** The header says `--fresh` "orders the declarations with `Expr.getUsedConstants`, which keeps only a small cache of visited subterms and does not terminate in practical time". At v4.33.1, `foldConsts` keeps every visited node in an unbounded `PtrSet` (FoldConsts.lean:19, PtrSet.lean), so that traversal is linear, like `usedConstsImpl`. What `--fresh` costs is its single thread: the run's 3,427 s on 28 threads is roughly 27 thread-hours. CutMain.lean makes the same claim.
- (b) **The paper's description of what reaches `addDeclCore`.** The paper says "each of them, other than a constructor or a recursor, is passed to ... `addDeclCore`" (verification.tex:91-95). In fact inductive types go once per mutual block, the four quotient constants go as one `quotDecl`, and neither is compared with what the kernel generated (finding 3).
- (c) **What `replay-axioms.txt` lists.** It lists the axioms declared in the closure, not the ones used: `sorryAx` and `Lean.ofReduceBool` appear because Init declares them. A theorem proved with `sorry` replays without failure (T14). The evidence about `sorry` is `#print axioms` (`axioms.txt`), and the paper uses it correctly.

**8. Trust this program shares with every stock tool.** Severity: **note**.

- **Hard-wired names.** The kernel recognises `Nat.add`, `Nat.sub`, ... and the literal constructors by name and never checks their definitions (type_checker.cpp:702-735, inductive.cpp:1352-1395). A tampered `Init/Prelude.olean` that redefines `Nat.add` would let this program and `leanchecker` alike accept a proof of `False`. The toolchain's own files should be compared with the release archive.
- **Compiled-code evaluation.** A proof that needs `Lean.reduceBool` evaluation fails here, because the fresh environment holds no compiled code (type_checker.cpp:614-635, ir_interpreter.cpp:872-875) `[INFERENCE]`. With 0 failures recorded, no such proof is in the closure, which agrees with `#print axioms`.
- **The `oom_kill 2` line.** The last line of `replay-log.txt`, `oom_kill 2`, is not printed by this program. A process that had been killed would not have printed `REPLAY-DONE`.

**Parts I conclude are sound.**

- **Parallel checking** (lines 100-104, 131-137, 140-147, 264). For an axiom, definition, theorem or opaque constant, `addDeclWithoutChecking` is exactly `add(constant_info(d))`, the environment a successful checked add produces (environment.cpp:152-223). Every task is awaited and every error recorded. The snapshot is a persistent value, so each declaration is checked against exactly the declarations emitted before it. An unchecked add overwrites on a name clash, because `check_name` runs only under `check` (environment.cpp:102, 127). The task for that same declaration then reports `already declared`.
- **Skip rule** (lines 230, 240). `isUnsafe` and `isPartial` are false for every `thmInfo` (Declaration.lean:453-465), so no theorem is ever skipped. A skipped constant is never added, so any declaration that mentions it fails with an unknown constant, where the kernel would have said "uses unsafe declaration" (type_checker.cpp:110-117). Measured: 5,008 of the 5,840 skipped names end in `._unsafe_rec`, including all 557 that start with one of the archive's namespaces (Formalism, GroundTheory, PositivityTheory, ReciprocityTheory, CompanionTheory, UpperTheory and others).
- **Ordering** (lines 241-263). Every name in `order` is emitted once. A dependency that is missing, still on the stack (a cycle) or skipped can only produce an unknown-constant failure, never an acceptance.
- **Inductive blocks and the quotient** (lines 149-152, 195, 203). `add_inductive` and `add_quot` check whatever the flag says (environment.cpp:271-283). `add_quot` also refuses to overwrite any of the four names (quot.cpp:47-56).
- **Constructors and recursors** (lines 266-274). Each is compared with the derived `BEq` over every field, recursor rules included.
- **Duplicate names** (lines 158-169). Every theorem version is checked. That is more than `--fresh` does, since it sees one version per name, and more than default `leanchecker` does, since it skips a re-declared theorem (Replay.lean:85-93). In the recorded run duplicates and checked alternates are both 40,595.
- **Exit status** (line 300). It is 0 only with no failures and both self-test outcomes right. An exception during import or replay ends the process with a non-zero code and no summary.

## Hostile test modules

### Layout

A Lake project with `lean-toolchain` set to `leanprover/lean4:v4.33.1` and this `lakefile.toml`:

```toml
name = "replayfixtures"
defaultTargets = ["Hostile", "craft"]

[[lean_lib]]
name = "Hostile"
globs = ["Hostile.+"]

[[lean_exe]]
name = "craft"
root = "Craft"
```

Every test `Tk` has a root module `Hostile.Tk`, and its parts are `Hostile.Tk.*`. So `leanchecker Hostile.Tk` covers the parts (its target rule is a name prefix, LeanChecker.lean:93), and `leanchecker --fresh Hostile.Tk` and `replay out Hostile.Tk` cover the whole closure.

The tests come in two groups:

- **Front-end tests** (T1-T5, T7, T7b, T8, T14, T15) are compiled by `lake build`.
- **Crafted tests** (T6, T9-T12, and the root of T7) have no source. `lake exe craft` writes them with the public `saveModuleData` (Environment.lean:1792). `importModules` accepts the result, because `finalizeImport` checks only duplicate keys, not whether a key equals the stored name and not inductive metadata (Environment.lean:2330-2345).

Run `lake exe craft` after `lake build`, and run the tools through `lake env`, which does not rebuild.

**Why the front-end tests compile.**

- `run_cmd` is a built-in command (BuiltinEvalCommand.lean:274-279).
- `debug.skipKernelTC` is registered at Environment.lean:76, and `addDecl` honours it by adding without a check (AddDecl.lean:30-33).
- Skipping the kernel logs no error, so the front end writes the `.olean` (Frontend.lean:378-385). A kernel rejection, by contrast, is an error, and then no `.olean` is written at all.

### Front-end modules

```lean
-- Hostile/T1.lean : skipKernelTC with addDecl; a false theorem, then a theorem that uses it
import Lean
open Lean Elab Command

set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl
  { name := `Hostile.T1.bad, levelParams := [], type := mkConst ``False,
    value := mkConst ``True.intro, all := [`Hostile.T1.bad] }

theorem Hostile.T1.useBad : False := Hostile.T1.bad
```

```lean
-- Hostile/T2.lean : the public wrapper of Kernel.Environment.addDeclWithoutChecking
import Lean
open Lean Elab Command

run_cmd do
  let d : Declaration := .thmDecl
    { name := `Hostile.T2.bad, levelParams := [], type := mkConst ``False,
      value := mkConst ``True.intro, all := [`Hostile.T2.bad] }
  match (← getEnv).addDeclCore 0 0 d none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "refused"
```

```lean
-- Hostile/T2b.lean : Kernel.Environment.addDeclWithoutChecking through modifyEnv (keep it the last command)
import Lean
open Lean Elab Command

run_cmd modifyEnv fun env =>
  match env.toKernelEnv.addDeclWithoutChecking (.thmDecl
      { name := `Hostile.T2b.bad, levelParams := [], type := mkConst ``False,
        value := mkConst ``True.intro, all := [`Hostile.T2b.bad] }) with
  | .ok k => Environment.ofKernelEnv k
  | .error _ => env
```

T2 compiles, because `Environment.addDeclCore` with `doCheck` is public (Environment.lean:701-711, inside the file's `public section`). T2b compiles as well: `Kernel.Environment.addDeclWithoutChecking`, `toKernelEnv` and `ofKernelEnv` are public (Environment.lean:308, 645-650). `ofKernelEnv` drops the elaborator's asynchronous bookkeeping and realization context, and its docstring says it must not leak into elaboration. So keep T2b as the last command; later commands that realize imported definitions may fail `[INFERENCE]`. The constant reaches the `.olean` either way, because `mkModuleData` reads `env.toKernelEnv` (Environment.lean:1867).

```lean
-- Hostile/T3.lean : a definition whose value does not have its declared type
import Lean
open Lean Elab Command

set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .defnDecl
  { name := `Hostile.T3.cheat, levelParams := [], type := mkConst ``False,
    value := mkConst ``True.intro, hints := .abbrev, safety := .safe, all := [`Hostile.T3.cheat] }

theorem Hostile.T3.t : False := Hostile.T3.cheat
```

```lean
-- Hostile/T4.lean : a theorem resting on an unsafe constant that inhabits False
import Lean
open Lean Elab Command

-- the kernel accepts this: an unsafe definition may refer to itself (environment.cpp:160-176)
run_cmd liftCoreM <| addDecl <| .defnDecl
  { name := `Hostile.T4.bogus, levelParams := [], type := mkConst ``False,
    value := mkConst `Hostile.T4.bogus, hints := .opaque, safety := .unsafe, all := [`Hostile.T4.bogus] }

set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl
  { name := `Hostile.T4.t, levelParams := [], type := mkConst ``False,
    value := mkConst `Hostile.T4.bogus, all := [`Hostile.T4.t] }
```

```lean
-- Hostile/T5.lean : the same with a partial constant
import Lean
open Lean Elab Command

-- the kernel accepts this: a partial block may refer to itself (environment.cpp:225-269)
run_cmd liftCoreM <| addDecl <| .mutualDefnDecl [
  { name := `Hostile.T5.loopF, levelParams := [], type := mkConst ``False,
    value := mkConst `Hostile.T5.loopF, hints := .opaque, safety := .partial, all := [`Hostile.T5.loopF] }]

set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl
  { name := `Hostile.T5.t, levelParams := [], type := mkConst ``False,
    value := mkConst `Hostile.T5.loopF, all := [`Hostile.T5.t] }
```

```lean
-- Hostile/T7/D1.lean          (T7: one name, two types; the root is crafted)
def Hostile.T7.foo : Nat := 0
-- Hostile/T7/D2.lean
def Hostile.T7.foo : Bool := true
```

```lean
-- Hostile/T7b/D3.lean         (T7b: one theorem name, same type, one bogus version)
theorem Hostile.T7b.dup : True := trivial
-- Hostile/T7b/D4.lean
import Lean
open Lean Elab Command
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl
  { name := `Hostile.T7b.dup, levelParams := [], type := mkConst ``True,
    value := mkConst ``Nat.zero, all := [`Hostile.T7b.dup] }
-- Hostile/T7b.lean
import Hostile.T7b.D3
import Hostile.T7b.D4
-- Hostile/T7c.lean
import Hostile.T7b.D4
import Hostile.T7b.D3
```

T7b and T7c compile, because `finalizeImport` allows two theorems that agree on name, type, universe parameters and `all` (Environment.lean:2272-2273). Each keeps the later of the two versions, so T7b keeps the bogus one and T7c the valid one.

```lean
-- Hostile/T8.lean : a type that mentions a constant no module declares
import Lean
open Lean Elab Command
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .axiomDecl
  { name := `Hostile.T8.ghost, levelParams := [], type := mkConst `Hostile.T8.NoSuchConstant,
    isUnsafe := false }
```

```lean
-- Hostile/T14.lean : calibration; the kernel accepts this, and only #print axioms shows sorryAx
theorem Hostile.T14.cheat : False := sorry
-- Hostile/T15.lean : calibration; a proof that needs compiled code
theorem Hostile.T15.t : 2 ^ 10 = 1024 := by native_decide
-- Hostile/Src/Two.lean and Hostile/Src/Ph12.lean : templates read by Craft, imported by nothing
inductive Two | a | b
inductive Ph12 | a
```

### Crafted modules

```lean
-- Craft.lean
import Lean
open Lean

def lib : System.FilePath := ".lake/build/lib/lean"

/-- Write a non-`module` olean. Each entry is (key, stored constant): the key is what `constNames`
holds and is normally the stored constant's own name. -/
def writeMod (mod : Name) (imports : Array Name) (cs : Array (Name × ConstantInfo)) : IO Unit := do
  let path := modToFilePath lib mod "olean"
  if let some dir := path.parent then IO.FS.createDirAll dir
  saveModuleData path mod
    { isModule := false, imports := imports.map fun m => ({ module := m } : Import),
      constNames := cs.map (·.1), constants := cs.map (·.2),
      extraConstNames := #[], entries := #[] }

/-- The constants of a module Lake compiled from source. -/
def readMod (mod : Name) : IO (Array (Name × ConstantInfo)) := do
  let (md, _) ← readModuleData (modToFilePath lib mod "olean")
  return md.constNames.zip md.constants

def nat0 := mkRawNatLit 0
def nat1 := mkRawNatLit 1
def eq1 (ty a b : Expr) := mkApp3 (mkConst ``Eq [levelOne]) ty a b
def refl1 (ty a : Expr) := mkApp2 (mkConst ``Eq.refl [levelOne]) ty a
def thm (n : Name) (ty val : Expr) : Name × ConstantInfo :=
  (n, .thmInfo { name := n, levelParams := [], type := ty, value := val, all := [n] })

/-- T6: the recursor of `Two` with the right-hand sides of its two rules swapped, and a theorem
true only under the swapped rules: `Two.rec 0 1 Two.b = 0`. -/
def t6 : IO Unit := do
  let cs ← readMod `Hostile.Src.Two
  let cs := cs.map fun (n, ci) => match ci with
    | .recInfo r => match r.rules with
      | [ra, rb] => (n, .recInfo { r with rules := [{ ra with rhs := rb.rhs }, { rb with rhs := ra.rhs }] })
      | _ => (n, ci)
    | _ => (n, ci)
  writeMod `Hostile.T6.Def #[`Init] cs
  let lhs := mkApp4 (mkConst `Two.rec [levelOne]) (.lam `x (mkConst `Two) (mkConst ``Nat) .default)
    nat0 nat1 (mkConst `Two.b)
  writeMod `Hostile.T6.Use #[`Hostile.T6.Def]
    #[thm `Hostile.T6.t6 (eq1 (mkConst ``Nat) lhs nat0) (refl1 (mkConst ``Nat) nat0)]
  writeMod `Hostile.T6 #[`Hostile.T6.Use] #[]

/-- T7: a root importing two modules that declare one name with two types. -/
def t7 : IO Unit := writeMod `Hostile.T7 #[`Hostile.T7.D1, `Hostile.T7.D2] #[]

/-- T9: key `phantomBody` stores `def Phantom := Nat`; key `Phantom` stores an empty inductive. -/
def t9 : IO Unit := do
  let ty := mkSort levelOne
  let ph := mkConst `Hostile.T9.Phantom
  writeMod `Hostile.T9 #[`Init] #[
    (`Hostile.T9.phantomBody, .defnInfo { name := `Hostile.T9.Phantom, levelParams := [],
        type := ty, value := mkConst ``Nat, hints := .abbrev, safety := .safe,
        all := [`Hostile.T9.Phantom] }),
    (`Hostile.T9.Phantom, .inductInfo { name := `Hostile.T9.Phantom, levelParams := [],
        type := ty, numParams := 0, numIndices := 0, all := [`Hostile.T9.Phantom], ctors := [],
        numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }),
    thm `Hostile.T9.phantom_nonempty (mkApp (mkConst ``Nonempty [levelOne]) ph)
      (mkApp2 (mkConst ``Nonempty.intro [levelOne]) ph nat0) ]

/-- T10 and T11: a quotient constant the kernel never generates, of type `False`. -/
def rogueQuot (n : Name) : Name × ConstantInfo :=
  (n, .quotInfo { name := n, levelParams := [], type := mkConst ``False, kind := .type })

def t10 : IO Unit := do
  writeMod `Hostile.T10.Def #[`Init] #[rogueQuot `Hostile.T10.cheat]
  writeMod `Hostile.T10.Use #[`Hostile.T10.Def]
    #[thm `Hostile.T10.t10 (mkConst ``False) (mkConst `Hostile.T10.cheat)]
  writeMod `Hostile.T10 #[`Hostile.T10.Use] #[]
  writeMod `Hostile.T11.Def #[`Init] #[rogueQuot `Hostile.T11.cheat]
  writeMod `Hostile.T11 #[`Hostile.T11.Def] #[]

/-- T12: `Ph12` stored as having a second constructor that exists nowhere, and a theorem that is
true only of the one-constructor type the kernel builds. -/
def t12 : IO Unit := do
  let cs ← readMod `Hostile.Src.Ph12
  let cs := cs.map fun (n, ci) => match ci with
    | .inductInfo v => (n, .inductInfo { v with ctors := v.ctors ++ [`Ph12.b] })
    | _ => (n, ci)
  writeMod `Hostile.T12.Def #[`Init] cs
  let p := mkConst `Ph12
  let ty := Expr.forallE `x p (.forallE `y p (eq1 p (.bvar 1) (.bvar 0)) .default) .default
  let val := Expr.lam `x p (.lam `y p (refl1 p (.bvar 1)) .default) .default
  writeMod `Hostile.T12.Use #[`Hostile.T12.Def] #[thm `Hostile.T12.allEq ty val]
  writeMod `Hostile.T12 #[`Hostile.T12.Use] #[]

def main : IO Unit := do t6; t7; t9; t10; t12
```

### Predicted outcomes

These are predicted from the source, with exit codes. "PASS" means exit 0 with no failure recorded.

| Test | Program (lines) | `leanchecker Hostile.Tk` | `leanchecker --fresh Hostile.Tk` |
|---|---|---|---|
| T1, T2, T2b: false theorem | FAIL `bad`, declaration type mismatch (174-176, 131-137); `useBad` accepted against the unchecked `bad` (141-145); exit 1 | FAIL, exit 1 | FAIL, exit 1 |
| T3: ill-typed definition | FAIL `cheat` (171-173) | FAIL | FAIL |
| T4: unsafe dependency | `bogus` skipped (230, 240); FAIL `t`, unknown constant `bogus` | FAIL, unknown constant | FAIL |
| T5: partial dependency | `loopF` skipped; FAIL `t`, unknown constant | FAIL | FAIL |
| T6: recursor rules swapped | FAIL `t6`, type mismatch (it is checked against the generated rules); FAIL `Two.rec`, "recursor differs" (271-274) | FAIL on `T6.Def`, "Invalid recursor Two.rec" (Replay.lean:159-168). `leanchecker Hostile.T6.Use` alone: **PASS** (its imports carry the swapped rules) | FAIL |
| T7: one name, two types | line 213 throws "import ... failed, environment already contains 'Hostile.T7.foo'" (Environment.lean:2343); exit 1, no summary written | error importing the root, exit 1 (D1 and D2 alone pass) | error at import, exit 1 |
| T7b / T7c: bogus duplicate | FAIL `dup` in both orders, as main version (174-176) or as alternate (160-169) | `Hostile.T7b`: FAIL (D4 is checked against its own imports, which lack `dup`); `Hostile.T7c`: PASS (it covers only that root) | T7b FAIL; T7c **PASS**, since the merged map keeps D3's valid version (Environment.lean:2340-2341) |
| T8: unknown constant | FAIL `ghost`, unknown constant; `ghost` still appears in `replay-axioms.txt` (181) | FAIL | FAIL |
| T9: key/name mismatch | **PASS**, `sum-of-the-kinds` false (185, 289) | FAIL, already declared or type mismatch | FAIL |
| T10: rogue quotient constant, used | FAIL `t10`, unknown constant `cheat` (198-203) | **PASS**: in `T10.Def`, `add_quot` returns at once because `finalizeImport` set `quotInit` (quot.cpp:47-49, Environment.lean:2365), and `cheat` is never compared; `t10` is checked against the imported `cheat : False` | FAIL, unknown constant |
| T11: rogue quotient constant, unused | **PASS**, `quotient-constants 5` | PASS | PASS |
| T12: phantom constructor | **PASS**, nothing in the summary differs | FAIL: a panic on `Ph12.b` (Replay.lean:111), then the kernel rejects the default stand-in | FAIL, same |
| T14: `sorry` | PASS | PASS | PASS |
| T15: `native_decide` | FAIL, no compiled code in a fresh environment `[INFERENCE]` | FAIL `[INFERENCE]` | FAIL `[INFERENCE]` |

The program fails closed on every front-end test. It is stronger than a stock mode on T6 (against a per-module `leanchecker` that skips the defining module), on T7c (against `--fresh`) and on T10 (against default `leanchecker`). It is weaker than both stock modes on T9 and T12. If a run deviates from this table, my reading of the source is wrong at that point.

## What the stock tools do at v4.33.1

**`leanchecker` default mode** (LeanChecker.lean:12-34, 105-113).

- For each target module (every module whose name has the argument as a prefix, line 93), it imports that module's imports from their `.olean` files, unchecked, and replays only the module's own constants. Lean's `Environment.replay` does the replay (Replay.lean:176-189).
- A constant is therefore checked against the stored versions of its dependencies, not regenerated ones. That is why T10, and T6 run on the using module alone, pass.
- It skips a theorem that an import already declares with the same type (Replay.lean:85-93).
- It starts one task per target at once (line 108), which fits the paper's report that the first batch of 2,012 modules exhausted 128 GB.

**`leanchecker --fresh`** (LeanChecker.lean:36-38) runs on exactly one module. It replays `env.constants.map₁`, the merged map `finalizeImport` built, into `mkEmptyEnvironment`, on one thread. So it checks one version per duplicated name (T7c), and like this program it regenerates every inductive type and the quotient (T10).

**Both modes** compare constructors and recursors after replay (Replay.lean:148-168). Neither compares inductive types or quotient constants. Both panic and then fail on a missing constructor (T12), and both stop with `already declared` at the name collision of T9; those are the places where they are stricter than this program. Both share the kernel, the olean reader and `finalizeImport` with this program.

## Cross-check protocol

**Setup.** Run inside the archive's v4.33.1 project, the `lean/` directory of `replay.sh`:

```bash
VERIFY=/path/to/verify                               # this repository's verify
TC=$(lean --print-prefix); export LC="$TC/bin/leanchecker"
R=$VERIFY/replay/.lake/build/bin/replay               # cd $VERIFY/replay && lake build replay
AUDIT=$VERIFY/replay/.lake/build/bin/audit            # the program of Step 1, as a second lean_exe
```

**Step 0: provenance.**

- Record `sha256sum "$R"` and the commit of `ReplayMain.lean`.
- Check that `lean --version` reports commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, as `build-summary.txt` does.
- Compare the toolchain's `lib/lean` with the v4.33.1 release archive (finding 8).

**Step 1: audit the published files** (minutes; settles findings 1, 2, 3(a) and 3(b) for the recorded run). Add this as a second executable beside `replay` and run `lake env "$AUDIT" Main`. Expected output: `AUDIT-PROBLEMS 0` and `replayable 2695292`.

```lean
import Lean
open Lean

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := (args.getD 0 "Main").toName }] {}
  let mut bad : Array String := #[]
  for md in env.header.moduleData do
    if md.constNames.size != md.constants.size then
      bad := bad.push s!"{md.constNames.size} names for {md.constants.size} constants"
    for n in md.constNames, ci in md.constants do
      if ci.name != n then bad := bad.push s!"key {n} stores {ci.name}"
  let mut quots : Array Name := #[]
  let mut replayable := 0
  for (n, ci) in env.constants.map₁ do
    unless ci.isUnsafe || ci.isPartial do replayable := replayable + 1
    match ci with
    | .quotInfo _ => quots := quots.push n
    | .inductInfo v =>
      for c in v.ctors do
        match env.find? c with
        | some (.ctorInfo cv) =>
          if cv.induct != n then bad := bad.push s!"{n} lists {c}, a constructor of {cv.induct}"
        | _ => bad := bad.push s!"{n} lists {c}, which is not a constructor"
      for o in v.all do
        match env.find? o with
        | some (.inductInfo w) => if w.all != v.all then bad := bad.push s!"{n} and {o} disagree on their block"
        | _ => bad := bad.push s!"{n} lists {o} in its block, which is not an inductive type"
      unless v.isUnsafe do
        match env.find? (.str n "rec") with
        | some (.recInfo _) => pure ()
        | _ => bad := bad.push s!"{n} has no recursor"
    | _ => pure ()
  unless quots.size == 4 && [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind].all quots.contains do
    bad := bad.push s!"quotient constants {quots}"
  for b in bad do IO.println b
  IO.println s!"replayable {replayable}"
  IO.println s!"AUDIT-PROBLEMS {bad.size}"
  return if bad.isEmpty then 0 else 1
```

**Step 2: calibration on the fixtures** (under an hour).

```bash
cd replay-fixtures && lake build && lake exe craft
for t in T1 T2 T2b T3 T4 T5 T6 T7 T7b T7c T8 T9 T10 T11 T12 T14 T15; do
  mkdir -p out/$t
  lake env "$R" out/$t Hostile.$t   > out/$t/replay.log 2>&1; echo "$t replay=$?"
  lake env "$LC" Hostile.$t         > out/$t/lc.log     2>&1; echo "$t leanchecker=$?"
  lake env "$LC" --fresh Hostile.$t > out/$t/fresh.log  2>&1; echo "$t fresh=$?"
done
lake env "$LC" Hostile.T6.Use; echo "T6.Use leanchecker=$?"
```

Compare the results with the table, and rerun the suite after any change to the program.

**Step 3: a mid-size closure where `--fresh` is practical.**

```bash
lake env "$R" out/rz Mathlib.NumberTheory.LSeries.RiemannZeta                           # where RiemannHypothesis is defined
lake env "$LC" --fresh Mathlib.NumberTheory.LSeries.RiemannZeta; echo "fresh=$?"        # one thread; hours
lake env "$AUDIT" Mathlib.NumberTheory.LSeries.RiemannZeta    # its "replayable" must equal the replay's "replayed"
```

**Step 4: default mode over a sample of the archive.** This uses one module per process with bounded parallelism and a memory cap per process, because each process imports that module's whole closure.

```bash
xz -dc $VERIFY/results/cut-modules.txt.xz | shuf -n 500 --random-source=<(yes) > sample.txt; echo Main >> sample.txt
xargs -P 8 -I{} systemd-run --user --scope -q -p MemoryMax=16G \
  sh -c 'lake env "$LC" "$1" >/dev/null 2>&1; echo "$1 $?"' _ {} < sample.txt > lc-sample.txt
```

**Step 5: an independent kernel.** If versions built for this toolchain exist, run lean4lean (its command line matches `leanchecker`, per the comment in LeanChecker.lean) with `--fresh` on the Step 3 root, or export the cone with lean4export and check it with nanoda.

**Step 6: independence from the schedule.** Run `LEAN_NUM_THREADS=4 REPLAY_WINDOW=1000` on the Step 3 root. The summary must match Step 3 except for the `seconds` and `threads` lines.

### What agreement would and would not establish

- **The kind of witness.** The program and `leanchecker` share the C++ kernel, `importModules` and `finalizeImport`, the compacted-region reader and the toolchain's Init. Agreement between them in Steps 3 and 4 is evidence about the drivers: ordering, the set of skipped constants, the comparisons. About the kernel and the files it is one witness, not two.
- **What disagreement means.** On the fixtures the expected disagreements (T6.Use, T7c, T9, T10, T12) are exactly where the drivers differ. On real inputs, any disagreement points to a bug in one driver.
- **Step 4.** The sampled modules are checked against unchecked `.olean` files of everything else, so it is weaker than a full default-mode run. A full default-mode run is itself weaker than a fresh replay on crafted input (T6.Use, T10).
- **Step 1** closes findings 1, 2, 3(a) and 3(b) for the published files only, not for future runs.
- **Step 5** is the only independent evidence about the kernel.
- **Outside every step.**
  - That the `.olean` files correspond to the sources: a from-source rebuild of Mathlib followed by a second replay would show it.
  - The absence of `sorry` or compiler-trusting axioms: shown by `#print axioms`, already done.
  - What the statements mean.
  - The soundness of the kernel, including its name-based trust of `Nat` (finding 8).

## Changes before relying on the program

1. After `drain`, require the kernel environment to equal the stored one constant for constant, in both directions, with inductive types and quotient constants included (finding 3). This closes findings 1 and 2 and cases 3(a)-(c).
2. Fail on a listed constructor that is missing or of another kind (lines 190-191). Replace the `find?` early return at line 185 with a set of the blocks actually added. Fail unless every key equals its stored name (lines 224-225).
3. Take the main version of a duplicated name from `env.constants.map₁` (finding 4), and zip `constNames` with `constants` (finding 5).
4. Keep the fixture suite as a regression test, with its expected outcomes.
5. For the run already published: run the Step 1 audit on the same files. The paper's sentence on what is passed to `addDeclCore` and the header comment on `getUsedConstants` should be corrected (finding 7).

## Addendum: the program changed during this review

At 08:12 the working copy of `ReplayMain.lean` was uncommitted, sha256 `65396ce3f33656fdb6259e63e55b023c0b779b20c45b85bdba4ffac195cf8011` (214 lines added and 63 removed against `fbc765453`), and `verify/hostile/` had appeared. I read only that diff, not the whole new file, and compiled nothing. The diff appears to close findings 1-5 along the lines proposed above:

- **Finding 2.** A constant whose stored name differs from its key is a failure. Unequal name and constant lists are a failure too (finding 5).
- **Finding 1.** The early return at the old line 185 is now a set of blocks already sent. A listed constructor that is missing, of another kind, or of another type is a failure, and the block is then not sent.
- **Finding 3.** After `drain`, every replayed name is compared with the kernel's constant, and every kernel constant must be a replayed name. This uses `deriving instance BEq for InductiveVal, QuotKind, QuotVal, ConstantInfo`.
- **Finding 4.** A duplicated name keeps the version Lean's import keeps, and alternate axioms are listed.
- **Finding 7(a).** The claim about `getUsedConstants` is gone from the header.

Under the working copy the fixture table should change in four places: T9, T11, T12 and the missing-recursor case of finding 3(b) all become FAIL. The other rows stand, and T7 still stops at import. The fixtures apply to it unchanged. A review of the new file as a whole, once it stops changing, is the next step.
