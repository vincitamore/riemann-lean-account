/-
Writes eleven compiled files directly, with no source.

`Hostile.KeyMismatch`. A compiled file stores a list of names and a list of constants. Lean
writes them so that each name is the name of its constant. Here the file stores, under the name
`phantomBody`, a definition named `Hostile.Phantom` (with value `Nat`), and under the name
`Hostile.Phantom` an inductive type with no constructors. Lean's import accepts the file and
presents `Hostile.Phantom` as the empty inductive type, of which the third constant, a theorem,
claims an element. A replay that adds the definition first and then takes the name
`Hostile.Phantom` as done checks the theorem against `Nat` and accepts it. A replay must reject
this module.

The other ten are files of modules that use Lean's module system. Such a module is compiled to
five files: a first part (`.olean`), from which a module inside the system takes the module's
constants and its import list; a part for the language server; a private part, which an import
from outside the system reads and a replay replays; and two files of compiled code (`.ir.sig`,
`.ir`). Lean writes the first part from the declarations of the private part, each unchanged,
reduced to an axiom with the same statement, or left out; it gives every part the same import
list; and it writes no constants into the files of compiled code. In each file below the private
part is in order and something else is not, so that a file beginning with `module` that imports
it can prove `False`, or use what no theorem may use, while a replay of the private part finds
nothing. A replay must reject each of them. (The first was found by the third review of the
replay program; `ExportedImports` and `CodeConstants` by the fourth.)

`Hostile.ExportedOnly`: the first part holds a theorem `Hostile.exportedFalse : False` with the
proof `True.intro`, and the private part an honest theorem instead.
`Hostile.ExportedFlag`: the same, with the private part marked as the file of a module outside
the module system. Lean's import goes by the mark on the first part; a replay that went by the
mark on the part it replays would not look further.
`Hostile.ExportedStatement`: the private part holds a theorem `Hostile.stated : True`, the first
part an axiom `Hostile.stated : False`.
`Hostile.ExportedLevels`: the private part holds a theorem with no universe parameters, the
first part an axiom of the same name and statement with one.
`Hostile.ExportedPartial`: the private part holds a partial definition `Hostile.spin : False`,
defined as itself, and the first part an axiom `Hostile.spin : False` not marked unsafe. A
partial definition is one that Lean keeps for compiled code; Lean 4.33.1 marks its axiom unsafe,
so that no theorem may use it.
`Hostile.ExportedUnsafe`, `Hostile.ExportedOpaque`: the same with an unsafe definition and with
an unsafe opaque constant.
`Hostile.ExportedImports`: all parts hold the same honest theorem, and the first part's import
list names one module more than the private part's.
`Hostile.CodeConstants`: three honest parts, and an `.ir` file that holds a theorem
`Hostile.codeFalse : False`. A module loaded only for its compiled code hands that theorem to a
module inside the system.
`Hostile.CodeImports`: three honest parts, and an `.ir` file with no constants whose import list
names one module more.

Run after `lake build`:   lake exe craft
-/
import Lean
open Lean

def lib : System.FilePath := ".lake/build/lib/lean"

def initOnly : Array Import := #[{ module := `Init }]
def oneMore : Array Import := #[{ module := `Init }, { module := `Hostile.Honest }]

def moduleData (cs : Array (Name × ConstantInfo)) (isModule := false) (imports := initOnly) : ModuleData :=
  { isModule, imports, constNames := cs.map (·.1), constants := cs.map (·.2),
    extraConstNames := #[], entries := #[] }

def theoremOf (n : Name) (type value : Expr) : Name × ConstantInfo :=
  (n, .thmInfo { name := n, levelParams := [], type := type, value := value, all := [n] })

def axiomOf (n : Name) (type : Expr) (levelParams : List Name := []) : Name × ConstantInfo :=
  (n, .axiomInfo { name := n, levelParams, type, isUnsafe := false })

def honest : Name × ConstantInfo := theoremOf `Hostile.honest (mkConst ``True) (mkConst ``True.intro)

def keyMismatch : IO Unit := do
  let mod := `Hostile.KeyMismatch
  let path := modToFilePath lib mod "olean"
  let type := mkSort Level.one
  let phantom := mkConst `Hostile.Phantom
  saveModuleData path mod <| moduleData #[
    (`Hostile.phantomBody, .defnInfo
      { name := `Hostile.Phantom, levelParams := [], type := type, value := mkConst ``Nat,
        hints := .abbrev, safety := .safe, all := [`Hostile.Phantom] }),
    (`Hostile.Phantom, .inductInfo
      { name := `Hostile.Phantom, levelParams := [], type := type, numParams := 0, numIndices := 0,
        all := [`Hostile.Phantom], ctors := [], numNested := 0, isRec := false, isUnsafe := false,
        isReflexive := false }),
    theoremOf `Hostile.phantomNonempty (mkApp (mkConst ``Nonempty [Level.one]) phantom)
      (mkApp2 (mkConst ``Nonempty.intro [Level.one]) phantom (mkRawNatLit 0))]
  IO.println s!"wrote {path}"

/-- The three parts of a module-system file: the first part and the server part hold `first`,
with the import list `imports`; the private part holds `priv`. -/
def threeParts (mod : Name) (first priv : Array (Name × ConstantInfo))
    (privateIsModule := true) (imports := initOnly) : IO Unit := do
  let path := modToFilePath lib mod "olean"
  saveModuleDataParts mod #[
    (path, moduleData first (isModule := true) (imports := imports)),
    (path.addExtension "server", moduleData first (isModule := true) (imports := imports)),
    (path.addExtension "private", moduleData priv (isModule := privateIsModule))]
  IO.println s!"wrote {path} in three parts"

/-- The two files of compiled code of a module, the second holding `cs` and `imports`. -/
def codeFiles (mod : Name) (cs : Array (Name × ConstantInfo)) (imports := initOnly) : IO Unit := do
  let path := modToFilePath lib mod "olean"
  saveModuleDataParts (mod ++ `ir) #[
    (path.withExtension "ir.sig", default),
    (path.withExtension "ir", moduleData cs (isModule := true) (imports := imports))]
  IO.println s!"wrote the files of compiled code of {mod}"

def main : IO Unit := do
  let falseT := mkConst ``False
  keyMismatch
  let fake := theoremOf `Hostile.exportedFalse falseT (mkConst ``True.intro)
  threeParts `Hostile.ExportedOnly #[fake] #[honest]
  threeParts `Hostile.ExportedFlag #[fake] #[honest] (privateIsModule := false)
  threeParts `Hostile.ExportedStatement #[axiomOf `Hostile.stated falseT]
    #[theoremOf `Hostile.stated (mkConst ``True) (mkConst ``True.intro)]
  threeParts `Hostile.ExportedLevels #[axiomOf `Hostile.levelled (mkConst ``True) [`u]]
    #[theoremOf `Hostile.levelled (mkConst ``True) (mkConst ``True.intro)]
  let spin := `Hostile.spin
  threeParts `Hostile.ExportedPartial #[axiomOf spin falseT]
    #[(spin, .defnInfo
        { name := spin, levelParams := [], type := falseT, value := mkConst spin,
          hints := .opaque, safety := .partial, all := [spin] })]
  let wild := `Hostile.wild
  threeParts `Hostile.ExportedUnsafe #[axiomOf wild falseT]
    #[(wild, .defnInfo
        { name := wild, levelParams := [], type := falseT, value := mkConst wild,
          hints := .opaque, safety := .unsafe, all := [wild] })]
  let shut := `Hostile.shut
  threeParts `Hostile.ExportedOpaque #[axiomOf shut falseT]
    #[(shut, .opaqueInfo
        { name := shut, levelParams := [], type := falseT, value := mkConst shut,
          isUnsafe := true, all := [shut] })]
  threeParts `Hostile.ExportedImports #[honest] #[honest] (imports := oneMore)
  threeParts `Hostile.CodeConstants #[honest] #[honest]
  codeFiles `Hostile.CodeConstants #[theoremOf `Hostile.codeFalse falseT (mkConst ``True.intro)]
  threeParts `Hostile.CodeImports #[honest] #[honest]
  codeFiles `Hostile.CodeImports #[] (imports := oneMore)
