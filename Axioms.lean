/-
  Trust-base check.  Run with

      lake env lean Axioms.lean

  Every theorem must report exactly

      [propext, Classical.choice, Quot.sound]

  i.e. Lean 4's three standard axioms and nothing else: no `sorry`, no user-declared
  axiom, and no `native_decide` (which would delegate evaluation to compiled code and
  appear here as `Lean.ofReduceBool`).
-/
import ContactNumbers

open ContactNumbers

-- c(n,3) = 3n - 6 for n = 6, 7, 8, 9
#print axioms contactNumber_six
#print axioms contactNumber_seven
#print axioms contactNumber_eight
#print axioms contactNumber_nine

-- Bezdek-Khan Conjecture 5.2 at those n: the values, and minimal rigidity
-- of every packing attaining them
#print axioms conjecture52_six
#print axioms conjecture52_seven
#print axioms conjecture52_eight
#print axioms conjecture52_nine

-- The statements in full, and the definitions they are built from, so that the
-- reader can see what is being asserted.
#check @contactNumber_nine
#check @conjecture52_nine
#print ContactNumbers.contacts
#print ContactNumbers.realised
#print ContactNumbers.MinimallyRigid
#print Kissing3D.HardCore
#print Kissing3D.neighbors
#print Kissing3D.contactCount
