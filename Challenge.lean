/-
Copyright (c) 2026 Marek Wrzos. All rights reserved.
Released under Apache 2.0 licence.

Contact numbers of packings of congruent balls in Euclidean 3-space.

A packing of `n` congruent balls of radius `1/2` is recorded by the finite set `X` of
its centres: no two centres closer than `1`, so the open balls are disjoint, and two
balls touch exactly when their centres are at distance `1`. `contacts X` is the number
of touching pairs, and `c(n,3)` is its maximum over packings of `n` balls.

Exact values of `c(n,3)` have been known only for `n <= 5`. Bezdek and Khan (*Contact
numbers for sphere packings*, Bolyai Soc. Math. Studies 27, Springer 2018, 25-48) write
that "the contact number c(n, 3) is still unknown for n >= 6", record `c(n,3) = 3n-6`
for `n = 6,...,9` as their Conjecture 5.2, and derive it as their Proposition 5.1 only
conditionally on the completeness of a numerical enumeration.

The statements below are that conjecture, unconditionally: the four values, and minimal
rigidity of every packing attaining them.
-/
import Mathlib

namespace ContactNumbers

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A hard-core configuration: no two centres closer than `1`. -/
def HardCore (X : Finset E3) : Prop :=
  ∀ z ∈ X, ∀ w ∈ X, z ≠ w → 1 ≤ dist z w

open scoped Classical in
/-- The balls touching `z`. -/
noncomputable def neighbors (X : Finset E3) (z : E3) : Finset E3 :=
  X.filter (fun w => dist z w = 1)

/-- The number of touching pairs. The sum counts each pair twice. -/
noncomputable def contacts (X : Finset E3) : ℕ := (∑ z ∈ X, (neighbors X z).card) / 2

/-- The set of contact numbers realised by hard-core packings of `n` balls.
`IsGreatest (realised n) c` says exactly that `c(n,3) = c`. -/
def realised (n : ℕ) : Set ℕ :=
  {k | ∃ X : Finset E3, HardCore X ∧ X.card = n ∧ contacts X = k}

/-- **Minimal rigidity**, Definition 1 of Bezdek-Khan after Arkus-Manoharan-Brenner:
every ball touches at least three others, and there are at least `3n - 6` contacts. -/
def MinimallyRigid (X : Finset E3) : Prop :=
  (∀ v ∈ X, 3 ≤ (neighbors X v).card) ∧ 3 * X.card - 6 ≤ contacts X

/-! ### The contact numbers -/

theorem contactNumber_six : IsGreatest (realised 6) 12 := sorry

theorem contactNumber_seven : IsGreatest (realised 7) 15 := sorry

theorem contactNumber_eight : IsGreatest (realised 8) 18 := sorry

theorem contactNumber_nine : IsGreatest (realised 9) 21 := sorry

/-! ### Bezdek-Khan Conjecture 5.2 at `n = 6, 7, 8, 9`: the values, and minimal
rigidity of every packing attaining them. -/

theorem conjecture52_six :
    IsGreatest (realised 6) 12 ∧
    ∀ X : Finset E3, HardCore X → X.card = 6 → contacts X = 12 → MinimallyRigid X := sorry

theorem conjecture52_seven :
    IsGreatest (realised 7) 15 ∧
    ∀ X : Finset E3, HardCore X → X.card = 7 → contacts X = 15 → MinimallyRigid X := sorry

theorem conjecture52_eight :
    IsGreatest (realised 8) 18 ∧
    ∀ X : Finset E3, HardCore X → X.card = 8 → contacts X = 18 → MinimallyRigid X := sorry

theorem conjecture52_nine :
    IsGreatest (realised 9) 21 ∧
    ∀ X : Finset E3, HardCore X → X.card = 9 → contacts X = 21 → MinimallyRigid X := sorry

end ContactNumbers
