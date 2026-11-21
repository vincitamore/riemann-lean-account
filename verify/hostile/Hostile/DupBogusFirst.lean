/-
As Hostile/DupBogusLast.lean, with the bogus module imported first, so that the version Lean
keeps is the proved one and the bogus version is the one set aside. A replay that examines one
version of each name accepts this module. A replay must reject it: the bogus version is in a
compiled file of the closure.
-/
import Hostile.Dup.Bogus
import Hostile.Dup.Good
