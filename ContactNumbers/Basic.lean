/-
Copyright (c) 2026 Marek Wrzos. All rights reserved.
Released under Apache 2.0 licence.
-/
import Mathlib

/-!
# Contact numbers of congruent sphere packings: basic definitions

A *packing* of `n` congruent balls of radius `1/2` in `ℝ³` is recorded by the finite set
`X` of its centres: `HardCore X` says no two centres are closer than `1`, so the open
balls are disjoint, and two balls *touch* exactly when their centres are at distance `1`.

`contactCount X` counts **ordered** touching pairs, so it is twice the number of contacts;
`energy X = -contactCount X / 2` is the negative of the contact number. The contact number
of Bezdek–Khan, `c(n,3)`, is therefore `max { -energy X : HardCore X, X.card = n }`.
-/

set_option maxHeartbeats 1000000

namespace Kissing3D

open Finset

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A hard-core configuration in space: no two particles closer than `1`. -/
def HardCore (X : Finset E3) : Prop :=
  ∀ z ∈ X, ∀ w ∈ X, z ≠ w → 1 ≤ dist z w

open scoped Classical in
/-- The particles bonded to `z`. -/
noncomputable def neighbors (X : Finset E3) (z : E3) : Finset E3 :=
  X.filter (fun w => dist z w = 1)

/-- Twice the contact number. -/
noncomputable def contactCount (X : Finset E3) : ℕ := ∑ z ∈ X, (neighbors X z).card

/-- The negative of the contact number. -/
noncomputable def energy (X : Finset E3) : ℝ := -(contactCount X : ℝ) / 2

/-- Dot product in `ℝ³`, written out so no inner-product-space instances are involved. -/
def dot3 (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- `dot3` agrees with the Euclidean inner product. -/
theorem dot3_eq_inner (u v : E3) : dot3 u v = inner ℝ u v := by
  rw [PiLp.inner_apply]
  simp [dot3, Fin.sum_univ_three, RCLike.inner_apply]
  ring

/-- A unit vector has `dot3 u u = 1`. -/
theorem dot3_self_of_norm {u : E3} (h : ‖u‖ = 1) : dot3 u u = 1 := by
  rw [dot3_eq_inner, real_inner_self_eq_norm_sq, h]
  norm_num

end Kissing3D
