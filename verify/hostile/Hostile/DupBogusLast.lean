/-
Imports two modules that declare the same theorem with the same statement, which Lean's import
accepts. One of the two has no proof (Hostile/Dup/Bogus.lean). Here the bogus one is imported
last, so it is the version Lean keeps. A replay must reject this module.
-/
import Hostile.Dup.Good
import Hostile.Dup.Bogus
