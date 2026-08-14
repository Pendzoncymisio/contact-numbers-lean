import ContactNumbers.Emin7

set_option linter.style.header false
set_option maxHeartbeats 1000000

/-!
# `E_min(7) = −15`: the pentagonal bipyramid

The unit-edge pentagonal bipyramid: a regular pentagon of side one (circumradius
`R = 2/√(10−2√5) < 1`) with two apexes at height `√(1−R²)` above and below its
centre. All 15 edges (5 ring + 10 apex) have length one; the five base diagonals
are the golden ratio `(1+√5)/2` and the apex pair sits at `√5·√(10−2√5)/5 ≈ 1.051`,
so the configuration is hard-core. With `energy_ge_seven_particles` this pins the
seven-particle ground-state energy at exactly `−15`. This file is machine-generated
by `scratch-h4/bipyr7_gen.py`.
-/

namespace Kissing3D

/-- Pentagonal bipyramid vertex 0. -/
noncomputable def pb0 : E3 := WithLp.toLp 2 ![(5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20, 0, 0]
/-- Pentagonal bipyramid vertex 1. -/
noncomputable def pb1 : E3 := WithLp.toLp 2 ![Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20, (1 + Real.sqrt 5) / 4, 0]
/-- Pentagonal bipyramid vertex 2. -/
noncomputable def pb2 : E3 := WithLp.toLp 2 ![-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40), 1 / 2, 0]
/-- Pentagonal bipyramid vertex 3. -/
noncomputable def pb3 : E3 := WithLp.toLp 2 ![-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40), -(1 / 2), 0]
/-- Pentagonal bipyramid vertex 4. -/
noncomputable def pb4 : E3 := WithLp.toLp 2 ![Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20, -((1 + Real.sqrt 5) / 4), 0]
/-- Pentagonal bipyramid vertex 5. -/
noncomputable def pb5 : E3 := WithLp.toLp 2 ![0, 0, Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10]
/-- Pentagonal bipyramid vertex 6. -/
noncomputable def pb6 : E3 := WithLp.toLp 2 ![0, 0, -(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)]

/-- The unit-edge pentagonal bipyramid. -/
noncomputable def bipyr7 : Finset E3 := {pb0, pb1, pb2, pb3, pb4, pb5, pb6}

section Bipyr7Distances

private lemma hs5sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma hs5le : Real.sqrt 5 ≤ 5 / 2 := by
  nlinarith [hs5sq, Real.sqrt_nonneg 5]

private lemma ht5sq : Real.sqrt (10 - 2 * Real.sqrt 5) ^ 2 = 10 - 2 * Real.sqrt 5 :=
  Real.sq_sqrt (by linarith [hs5le])

private lemma ne_of_dist_one' {a b : E3} (h : dist a b = 1) : a ≠ b := by
  rintro rfl
  rw [dist_self] at h
  norm_num at h

private lemma ne_of_dist_ge_one {a b : E3} (h : 1 ≤ dist a b) : a ≠ b := by
  rintro rfl
  rw [dist_self] at h
  linarith

private lemma pd01 : dist pb0 pb1 = 1 := by
  rw [dist_coords]
  show Real.sqrt ((((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + ((0 : ℝ) - ((1 + Real.sqrt 5) / 4))^2 + ((0 : ℝ) - (0))^2) = 1
  rw [show (((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + ((0 : ℝ) - ((1 + Real.sqrt 5) / 4))^2 + ((0 : ℝ) - (0))^2 = 1 by linear_combination (1/16) * hs5sq + (1/16) * ht5sq]
  exact Real.sqrt_one

private lemma pd12 : dist pb1 pb2 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (1 / 2))^2 + ((0 : ℝ) - (0))^2) = 1
  rw [show ((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (1 / 2))^2 + ((0 : ℝ) - (0))^2 = 1 by linear_combination (5/32 - (Real.sqrt 5)/32) * hs5sq + ((Real.sqrt 5)^2/64 + (Real.sqrt 5)/32 + 1/64) * ht5sq]
  exact Real.sqrt_one

private lemma pd23 : dist pb2 pb3 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + ((1 / 2 : ℝ) - (-(1 / 2)))^2 + ((0 : ℝ) - (0))^2) = 1
  rw [show ((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + ((1 / 2 : ℝ) - (-(1 / 2)))^2 + ((0 : ℝ) - (0))^2 = 1 by linear_combination (0 : ℝ) * hs5sq]
  exact Real.sqrt_one

private lemma pd34 : dist pb3 pb4 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + ((-(1 / 2) : ℝ) - (-((1 + Real.sqrt 5) / 4)))^2 + ((0 : ℝ) - (0))^2) = 1
  rw [show ((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + ((-(1 / 2) : ℝ) - (-((1 + Real.sqrt 5) / 4)))^2 + ((0 : ℝ) - (0))^2 = 1 by linear_combination (5/32 - (Real.sqrt 5)/32) * hs5sq + ((Real.sqrt 5)^2/64 + (Real.sqrt 5)/32 + 1/64) * ht5sq]
  exact Real.sqrt_one

private lemma pd04 : dist pb0 pb4 = 1 := by
  rw [dist_coords]
  show Real.sqrt ((((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + ((0 : ℝ) - (-((1 + Real.sqrt 5) / 4)))^2 + ((0 : ℝ) - (0))^2) = 1
  rw [show (((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + ((0 : ℝ) - (-((1 + Real.sqrt 5) / 4)))^2 + ((0 : ℝ) - (0))^2 = 1 by linear_combination (1/16) * hs5sq + (1/16) * ht5sq]
  exact Real.sqrt_one

private lemma pd05 : dist pb0 pb5 = 1 := by
  rw [dist_coords]
  show Real.sqrt ((((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + ((0 : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2) = 1
  rw [show (((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + ((0 : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2 = 1 by linear_combination (3/40 - (Real.sqrt 5)/40) * hs5sq + ((Real.sqrt 5)^2/80 + (Real.sqrt 5)/40 + 1/16) * ht5sq]
  exact Real.sqrt_one

private lemma pd15 : dist pb1 pb5 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2) = 1
  rw [show ((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2 = 1 by linear_combination (3/16 - (Real.sqrt 5)/40) * hs5sq + ((Real.sqrt 5)^2/80) * ht5sq]
  exact Real.sqrt_one

private lemma pd25 : dist pb2 pb5 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (0))^2 + ((1 / 2 : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2) = 1
  rw [show ((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (0))^2 + ((1 / 2 : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2 = 1 by linear_combination (19/160 - (Real.sqrt 5)/32) * hs5sq + ((Real.sqrt 5)^2/64 + 3*(Real.sqrt 5)/160 + 1/64) * ht5sq]
  exact Real.sqrt_one

private lemma pd35 : dist pb3 pb5 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (0))^2 + ((-(1 / 2) : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2) = 1
  rw [show ((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (0))^2 + ((-(1 / 2) : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2 = 1 by linear_combination (19/160 - (Real.sqrt 5)/32) * hs5sq + ((Real.sqrt 5)^2/64 + 3*(Real.sqrt 5)/160 + 1/64) * ht5sq]
  exact Real.sqrt_one

private lemma pd45 : dist pb4 pb5 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + ((-((1 + Real.sqrt 5) / 4) : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2) = 1
  rw [show ((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + ((-((1 + Real.sqrt 5) / 4) : ℝ) - (0))^2 + ((0 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10))^2 = 1 by linear_combination (3/16 - (Real.sqrt 5)/40) * hs5sq + ((Real.sqrt 5)^2/80) * ht5sq]
  exact Real.sqrt_one

private lemma pd06 : dist pb0 pb6 = 1 := by
  rw [dist_coords]
  show Real.sqrt ((((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + ((0 : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2) = 1
  rw [show (((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + ((0 : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2 = 1 by linear_combination (3/40 - (Real.sqrt 5)/40) * hs5sq + ((Real.sqrt 5)^2/80 + (Real.sqrt 5)/40 + 1/16) * ht5sq]
  exact Real.sqrt_one

private lemma pd16 : dist pb1 pb6 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2) = 1
  rw [show ((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2 = 1 by linear_combination (3/16 - (Real.sqrt 5)/40) * hs5sq + ((Real.sqrt 5)^2/80) * ht5sq]
  exact Real.sqrt_one

private lemma pd26 : dist pb2 pb6 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (0))^2 + ((1 / 2 : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2) = 1
  rw [show ((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (0))^2 + ((1 / 2 : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2 = 1 by linear_combination (19/160 - (Real.sqrt 5)/32) * hs5sq + ((Real.sqrt 5)^2/64 + 3*(Real.sqrt 5)/160 + 1/64) * ht5sq]
  exact Real.sqrt_one

private lemma pd36 : dist pb3 pb6 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (0))^2 + ((-(1 / 2) : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2) = 1
  rw [show ((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (0))^2 + ((-(1 / 2) : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2 = 1 by linear_combination (19/160 - (Real.sqrt 5)/32) * hs5sq + ((Real.sqrt 5)^2/64 + 3*(Real.sqrt 5)/160 + 1/64) * ht5sq]
  exact Real.sqrt_one

private lemma pd46 : dist pb4 pb6 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + ((-((1 + Real.sqrt 5) / 4) : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2) = 1
  rw [show ((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (0))^2 + ((-((1 + Real.sqrt 5) / 4) : ℝ) - (0))^2 + ((0 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2 = 1 by linear_combination (3/16 - (Real.sqrt 5)/40) * hs5sq + ((Real.sqrt 5)^2/80) * ht5sq]
  exact Real.sqrt_one

private lemma pge02 : 1 ≤ dist pb0 pb2 := by
  rw [dist_coords]
  show 1 ≤ Real.sqrt ((((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + ((0 : ℝ) - (1 / 2))^2 + ((0 : ℝ) - (0))^2)
  rw [show (((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + ((0 : ℝ) - (1 / 2))^2 + ((0 : ℝ) - (0))^2 = (3 + Real.sqrt 5) / 2 by linear_combination (-(Real.sqrt 5)/32 - 1/32) * hs5sq + ((Real.sqrt 5)^2/64 + 3*(Real.sqrt 5)/32 + 9/64) * ht5sq]
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  linarith [Real.sqrt_nonneg 5]

private lemma pge03 : 1 ≤ dist pb0 pb3 := by
  rw [dist_coords]
  show 1 ≤ Real.sqrt ((((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + ((0 : ℝ) - (-(1 / 2)))^2 + ((0 : ℝ) - (0))^2)
  rw [show (((5 + Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + ((0 : ℝ) - (-(1 / 2)))^2 + ((0 : ℝ) - (0))^2 = (3 + Real.sqrt 5) / 2 by linear_combination (-(Real.sqrt 5)/32 - 1/32) * hs5sq + ((Real.sqrt 5)^2/64 + 3*(Real.sqrt 5)/32 + 9/64) * ht5sq]
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  linarith [Real.sqrt_nonneg 5]

private lemma pge13 : 1 ≤ dist pb1 pb3 := by
  rw [dist_coords]
  show 1 ≤ Real.sqrt (((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (-(1 / 2)))^2 + ((0 : ℝ) - (0))^2)
  rw [show ((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40)))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (-(1 / 2)))^2 + ((0 : ℝ) - (0))^2 = (3 + Real.sqrt 5) / 2 by linear_combination (5/32 - (Real.sqrt 5)/32) * hs5sq + ((Real.sqrt 5)^2/64 + (Real.sqrt 5)/32 + 1/64) * ht5sq]
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  linarith [Real.sqrt_nonneg 5]

private lemma pge14 : 1 ≤ dist pb1 pb4 := by
  rw [dist_coords]
  show 1 ≤ Real.sqrt (((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (-((1 + Real.sqrt 5) / 4)))^2 + ((0 : ℝ) - (0))^2)
  rw [show ((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20 : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + (((1 + Real.sqrt 5) / 4 : ℝ) - (-((1 + Real.sqrt 5) / 4)))^2 + ((0 : ℝ) - (0))^2 = (3 + Real.sqrt 5) / 2 by linear_combination (1/4) * hs5sq]
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  linarith [Real.sqrt_nonneg 5]

private lemma pge24 : 1 ≤ dist pb2 pb4 := by
  rw [dist_coords]
  show 1 ≤ Real.sqrt (((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + ((1 / 2 : ℝ) - (-((1 + Real.sqrt 5) / 4)))^2 + ((0 : ℝ) - (0))^2)
  rw [show ((-((5 + 3 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5) / 40) : ℝ) - (Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 20))^2 + ((1 / 2 : ℝ) - (-((1 + Real.sqrt 5) / 4)))^2 + ((0 : ℝ) - (0))^2 = (3 + Real.sqrt 5) / 2 by linear_combination (5/32 - (Real.sqrt 5)/32) * hs5sq + ((Real.sqrt 5)^2/64 + (Real.sqrt 5)/32 + 1/64) * ht5sq]
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  linarith [Real.sqrt_nonneg 5]

private lemma pge56 : 1 ≤ dist pb5 pb6 := by
  rw [dist_coords]
  show 1 ≤ Real.sqrt (((0 : ℝ) - (0))^2 + ((0 : ℝ) - (0))^2 + ((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2)
  rw [show ((0 : ℝ) - (0))^2 + ((0 : ℝ) - (0))^2 + ((Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10 : ℝ) - (-(Real.sqrt 5 * Real.sqrt (10 - 2 * Real.sqrt 5) / 10)))^2 = 2 - 2 / 5 * Real.sqrt 5 by linear_combination (2/5 - 2*(Real.sqrt 5)/25) * hs5sq + ((Real.sqrt 5)^2/25) * ht5sq]
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  nlinarith [hs5le, Real.sqrt_nonneg 5]

private lemma pne01 : pb0 ≠ pb1 := ne_of_dist_one' pd01
private lemma pne02 : pb0 ≠ pb2 := ne_of_dist_ge_one pge02
private lemma pne03 : pb0 ≠ pb3 := ne_of_dist_ge_one pge03
private lemma pne04 : pb0 ≠ pb4 := ne_of_dist_one' pd04
private lemma pne05 : pb0 ≠ pb5 := ne_of_dist_one' pd05
private lemma pne06 : pb0 ≠ pb6 := ne_of_dist_one' pd06
private lemma pne12 : pb1 ≠ pb2 := ne_of_dist_one' pd12
private lemma pne13 : pb1 ≠ pb3 := ne_of_dist_ge_one pge13
private lemma pne14 : pb1 ≠ pb4 := ne_of_dist_ge_one pge14
private lemma pne15 : pb1 ≠ pb5 := ne_of_dist_one' pd15
private lemma pne16 : pb1 ≠ pb6 := ne_of_dist_one' pd16
private lemma pne23 : pb2 ≠ pb3 := ne_of_dist_one' pd23
private lemma pne24 : pb2 ≠ pb4 := ne_of_dist_ge_one pge24
private lemma pne25 : pb2 ≠ pb5 := ne_of_dist_one' pd25
private lemma pne26 : pb2 ≠ pb6 := ne_of_dist_one' pd26
private lemma pne34 : pb3 ≠ pb4 := ne_of_dist_one' pd34
private lemma pne35 : pb3 ≠ pb5 := ne_of_dist_one' pd35
private lemma pne36 : pb3 ≠ pb6 := ne_of_dist_one' pd36
private lemma pne45 : pb4 ≠ pb5 := ne_of_dist_one' pd45
private lemma pne46 : pb4 ≠ pb6 := ne_of_dist_one' pd46
private lemma pne56 : pb5 ≠ pb6 := ne_of_dist_ge_one pge56

end Bipyr7Distances

section Bipyr7Config

private lemma bipyr7_dist : ∀ u ∈ bipyr7, ∀ v ∈ bipyr7, u ≠ v → 1 ≤ dist u v := by
  have key : ∀ a b : E3, dist a b = 1 → 1 ≤ dist a b ∧ 1 ≤ dist b a := by
    intro a b h
    exact ⟨by rw [h], by rw [dist_comm, h]⟩
  have key2 : ∀ a b : E3, 1 ≤ dist a b → 1 ≤ dist a b ∧ 1 ≤ dist b a := by
    intro a b h
    exact ⟨h, by rw [dist_comm]; exact h⟩
  intro u hu v hv huv
  simp only [bipyr7, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl huv
      | exact (key _ _ pd01).1 | exact (key _ _ pd01).2
      | exact (key _ _ pd12).1 | exact (key _ _ pd12).2
      | exact (key _ _ pd23).1 | exact (key _ _ pd23).2
      | exact (key _ _ pd34).1 | exact (key _ _ pd34).2
      | exact (key _ _ pd04).1 | exact (key _ _ pd04).2
      | exact (key _ _ pd05).1 | exact (key _ _ pd05).2
      | exact (key _ _ pd15).1 | exact (key _ _ pd15).2
      | exact (key _ _ pd25).1 | exact (key _ _ pd25).2
      | exact (key _ _ pd35).1 | exact (key _ _ pd35).2
      | exact (key _ _ pd45).1 | exact (key _ _ pd45).2
      | exact (key _ _ pd06).1 | exact (key _ _ pd06).2
      | exact (key _ _ pd16).1 | exact (key _ _ pd16).2
      | exact (key _ _ pd26).1 | exact (key _ _ pd26).2
      | exact (key _ _ pd36).1 | exact (key _ _ pd36).2
      | exact (key _ _ pd46).1 | exact (key _ _ pd46).2
      | exact (key2 _ _ pge02).1 | exact (key2 _ _ pge02).2
      | exact (key2 _ _ pge03).1 | exact (key2 _ _ pge03).2
      | exact (key2 _ _ pge13).1 | exact (key2 _ _ pge13).2
      | exact (key2 _ _ pge14).1 | exact (key2 _ _ pge14).2
      | exact (key2 _ _ pge24).1 | exact (key2 _ _ pge24).2
      | exact (key2 _ _ pge56).1 | exact (key2 _ _ pge56).2

theorem hardCore_bipyr7 : HardCore bipyr7 := bipyr7_dist

theorem card_bipyr7 : bipyr7.card = 7 := by
  rw [bipyr7]
  rw [Finset.card_insert_of_notMem (by simp [pne01, pne02, pne03, pne04, pne05, pne06])]
  rw [Finset.card_insert_of_notMem (by simp [pne12, pne13, pne14, pne15, pne16])]
  rw [Finset.card_insert_of_notMem (by simp [pne23, pne24, pne25, pne26])]
  rw [Finset.card_insert_of_notMem (by simp [pne34, pne35, pne36])]
  rw [Finset.card_insert_of_notMem (by simp [pne45, pne46])]
  rw [Finset.card_insert_of_notMem (by simp [pne56])]
  rw [Finset.card_singleton]

private lemma pdeg0 : 4 ≤ (neighbors bipyr7 pb0).card := by
  have hsub : ({pb1, pb4, pb5, pb6} : Finset E3) ⊆ neighbors bipyr7 pb0 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd01⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd04⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd05⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd06⟩
  have hcard : ({pb1, pb4, pb5, pb6} : Finset E3).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [pne14, pne15, pne16])]
    rw [Finset.card_insert_of_notMem (by simp [pne45, pne46])]
    rw [Finset.card_insert_of_notMem (by simp [pne56])]
    rw [Finset.card_singleton]
  calc 4 = ({pb1, pb4, pb5, pb6} : Finset E3).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

private lemma pdeg1 : 4 ≤ (neighbors bipyr7 pb1).card := by
  have hsub : ({pb0, pb2, pb5, pb6} : Finset E3) ⊆ neighbors bipyr7 pb1 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd01⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd12⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd15⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd16⟩
  have hcard : ({pb0, pb2, pb5, pb6} : Finset E3).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [pne02, pne05, pne06])]
    rw [Finset.card_insert_of_notMem (by simp [pne25, pne26])]
    rw [Finset.card_insert_of_notMem (by simp [pne56])]
    rw [Finset.card_singleton]
  calc 4 = ({pb0, pb2, pb5, pb6} : Finset E3).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

private lemma pdeg2 : 4 ≤ (neighbors bipyr7 pb2).card := by
  have hsub : ({pb1, pb3, pb5, pb6} : Finset E3) ⊆ neighbors bipyr7 pb2 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd12⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd23⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd25⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd26⟩
  have hcard : ({pb1, pb3, pb5, pb6} : Finset E3).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [pne13, pne15, pne16])]
    rw [Finset.card_insert_of_notMem (by simp [pne35, pne36])]
    rw [Finset.card_insert_of_notMem (by simp [pne56])]
    rw [Finset.card_singleton]
  calc 4 = ({pb1, pb3, pb5, pb6} : Finset E3).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

private lemma pdeg3 : 4 ≤ (neighbors bipyr7 pb3).card := by
  have hsub : ({pb2, pb4, pb5, pb6} : Finset E3) ⊆ neighbors bipyr7 pb3 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd23⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd34⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd35⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd36⟩
  have hcard : ({pb2, pb4, pb5, pb6} : Finset E3).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [pne24, pne25, pne26])]
    rw [Finset.card_insert_of_notMem (by simp [pne45, pne46])]
    rw [Finset.card_insert_of_notMem (by simp [pne56])]
    rw [Finset.card_singleton]
  calc 4 = ({pb2, pb4, pb5, pb6} : Finset E3).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

private lemma pdeg4 : 4 ≤ (neighbors bipyr7 pb4).card := by
  have hsub : ({pb0, pb3, pb5, pb6} : Finset E3) ⊆ neighbors bipyr7 pb4 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd04⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd34⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd45⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], pd46⟩
  have hcard : ({pb0, pb3, pb5, pb6} : Finset E3).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [pne03, pne05, pne06])]
    rw [Finset.card_insert_of_notMem (by simp [pne35, pne36])]
    rw [Finset.card_insert_of_notMem (by simp [pne56])]
    rw [Finset.card_singleton]
  calc 4 = ({pb0, pb3, pb5, pb6} : Finset E3).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

private lemma pdeg5 : 5 ≤ (neighbors bipyr7 pb5).card := by
  have hsub : ({pb0, pb1, pb2, pb3, pb4} : Finset E3) ⊆ neighbors bipyr7 pb5 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd05⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd15⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd25⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd35⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd45⟩
  have hcard : ({pb0, pb1, pb2, pb3, pb4} : Finset E3).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [pne01, pne02, pne03, pne04])]
    rw [Finset.card_insert_of_notMem (by simp [pne12, pne13, pne14])]
    rw [Finset.card_insert_of_notMem (by simp [pne23, pne24])]
    rw [Finset.card_insert_of_notMem (by simp [pne34])]
    rw [Finset.card_singleton]
  calc 5 = ({pb0, pb1, pb2, pb3, pb4} : Finset E3).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

private lemma pdeg6 : 5 ≤ (neighbors bipyr7 pb6).card := by
  have hsub : ({pb0, pb1, pb2, pb3, pb4} : Finset E3) ⊆ neighbors bipyr7 pb6 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd06⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd16⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd26⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd36⟩
    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact pd46⟩
  have hcard : ({pb0, pb1, pb2, pb3, pb4} : Finset E3).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [pne01, pne02, pne03, pne04])]
    rw [Finset.card_insert_of_notMem (by simp [pne12, pne13, pne14])]
    rw [Finset.card_insert_of_notMem (by simp [pne23, pne24])]
    rw [Finset.card_insert_of_notMem (by simp [pne34])]
    rw [Finset.card_singleton]
  calc 5 = ({pb0, pb1, pb2, pb3, pb4} : Finset E3).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem energy_bipyr7 : energy bipyr7 = -15 := by
  have hle : energy bipyr7 ≤ -15 := by
    have hcc : 30 ≤ contactCount bipyr7 := by
      rw [contactCount, bipyr7]
      rw [Finset.sum_insert (by simp [pne01, pne02, pne03, pne04, pne05, pne06])]
      rw [Finset.sum_insert (by simp [pne12, pne13, pne14, pne15, pne16])]
      rw [Finset.sum_insert (by simp [pne23, pne24, pne25, pne26])]
      rw [Finset.sum_insert (by simp [pne34, pne35, pne36])]
      rw [Finset.sum_insert (by simp [pne45, pne46])]
      rw [Finset.sum_insert (by simp [pne56])]
      rw [Finset.sum_singleton]
      simp only [show ({pb0, pb1, pb2, pb3, pb4, pb5, pb6} : Finset E3) = bipyr7 from rfl]
      have h0 := pdeg0; have h1 := pdeg1; have h2 := pdeg2; have h3 := pdeg3
      have h4 := pdeg4; have h5 := pdeg5; have h6 := pdeg6
      omega
    rw [energy]
    have : (30 : ℝ) ≤ (contactCount bipyr7 : ℝ) := by exact_mod_cast hcc
    linarith
  have hge := energy_ge_seven_particles hardCore_bipyr7 card_bipyr7
  linarith

/-- **`E_min(7) = −15`**: the pentagonal bipyramid is the seven-particle ground
state. The lower bound is the certificate-checked graph fact; the upper bound is
this configuration. -/
theorem groundState_seven :
    (∀ X : Finset E3, HardCore X → X.card = 7 → -15 ≤ energy X) ∧
    HardCore bipyr7 ∧ bipyr7.card = 7 ∧ energy bipyr7 = -15 :=
  ⟨fun _ hX h => energy_ge_seven_particles hX h, hardCore_bipyr7, card_bipyr7,
    energy_bipyr7⟩

end Bipyr7Config

end Kissing3D
