/-
A calibration, not an attack: a theorem proved with `sorry`.

`sorry` is the axiom `sorryAx`, and an axiom is a legal declaration, so every replay accepts
this module. What exposes it is the list of axioms the theorem depends on, which
`#print axioms` gives here and which the replay gives for the theorems it is asked about.
-/
theorem Hostile.bySorry : False := sorry

#print axioms Hostile.bySorry
