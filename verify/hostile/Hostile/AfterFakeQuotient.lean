/-
A module that imports `Hostile.FakeQuotient` and proves `False` from the constant planted there.
It compiles, and `#print axioms` reports that the proof depends on no axioms. Its own
declaration is in order given its imports; what is wrong is in the module it imports.
A replay of everything this module imports must reject it.
-/
import Hostile.FakeQuotient

theorem Hostile.falseFromQuot : False := Hostile.fakeQuot

#print axioms Hostile.falseFromQuot
