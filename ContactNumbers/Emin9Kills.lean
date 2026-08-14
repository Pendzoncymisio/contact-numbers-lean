import ContactNumbers.Emin8Kills

set_option linter.style.header false
set_option maxHeartbeats 1600000

/-!
# Geometric kill lemmas for the `E_min(9)` programme

The 22-bond nine-particle survivor classes that escape the `E_min(8)` patterns
`P1/P4/P5` are killed by two new minimal obstructions found by sub-pattern
analysis (`scratch-h4/emin9_subpat.py`), plus one full nine-point pattern.

This file proves the first: **P6, the K4-mirror pattern** (obstruction `obs8`,
six points, eleven bonds), which kills 13 of the 52 new classes directly and
underlies the size-6 core of many others.

Structure: points `q0 q1 q2 q3` form a unit tetrahedron; `q5` is bonded to
`q1 q2 q3` and hard-core-separated from `q0`, hence sits at the mirror position
of `q0` through the plane `(q1,q2,q3)`; `q4` is bonded to both `q0` and `q5`.
Recentring at `q1`, vanishing Gram determinants force `⟨y₀,y₅⟩ = −1/3`, then
`dist(q1,q4) = dist(q2,q4) = dist(q3,q4) = 1` exactly (the hard-core bounds are
tight), and the final Gram determinant `det G[y₀,y₂,y₃,y₄] = 5/16 ≠ 0` is a
contradiction: `q4` would have to lie on the circumcircle of `(q1,q2,q3)` at
distance `≥ 1` from all three vertices, which the circle cannot accommodate.
-/

namespace Kissing3D

lemma det_fin_four (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.det =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
        - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
        + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
      - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
        - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
        + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
      + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
        - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
        + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
      - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)
        - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
        + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp +decide [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove]
  ring

/-- Cauchy–Schwarz as a `2×2` Gram-minor inequality, in the product form the
SOS wrappers rewrite. -/
lemma gram2_det_nonneg (u v : E3) :
    0 ≤ (inner ℝ u u : ℝ) * (inner ℝ v v : ℝ)
      - (inner ℝ u v : ℝ) * (inner ℝ v u : ℝ) := by
  rw [real_inner_comm u v, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h := abs_real_inner_le_norm u v
  have h2 := mul_self_le_mul_self (abs_nonneg (inner ℝ u v : ℝ)) h
  rw [abs_mul_abs_self] at h2
  have h3 : ‖u‖ ^ 2 * ‖v‖ ^ 2 = ‖u‖ * ‖v‖ * (‖u‖ * ‖v‖) := by ring
  linarith [h2, h3]

/-- The `3×3` Gram determinant of three vectors of `E3` is nonnegative: the Gram
matrix factors as `A * Aᵀ` over the coordinates, so its determinant is
`(det A)²`. -/
lemma gram3_det_nonneg (v : Fin 3 → E3) :
    0 ≤ (Matrix.of fun i j => (inner ℝ (v i) (v j) : ℝ)).det := by
  have hfact : (Matrix.of fun i j => (inner ℝ (v i) (v j) : ℝ))
      = (Matrix.of (fun i j => v i j)) * (Matrix.of (fun i j => v i j)).transpose := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [hfact, Matrix.det_mul, Matrix.det_transpose]
  exact mul_self_nonneg _

/-- One multiplication step of a monomial box bound: from `1 ≤ x ≤ 4` and
`1 ≤ m ≤ C` conclude `1 ≤ x·m ≤ 4·C`. Used by the slack-absorbed SOS
certificates to bound residual monomials on the box `[1,4]ⁿ`. -/
lemma mono_step {x m C : ℝ} (hx1 : 1 ≤ x) (hx4 : x ≤ 4)
    (hm1 : 1 ≤ m) (hmC : m ≤ C) : 1 ≤ x * m ∧ x * m ≤ 4 * C := by
  have h0 : (0:ℝ) ≤ m := by linarith
  have h1 : (0:ℝ) ≤ x - 1 := by linarith
  have h3 : (0:ℝ) ≤ 4 - x := by linarith
  constructor
  · nlinarith [mul_nonneg h1 h0]
  · nlinarith [mul_nonneg h0 h3]

/-- **The P6 (K4-mirror) pattern is impossible**: in a hard-core configuration
there are no six points with the eleven bonds
`{01, 02, 03, 04, 12, 13, 15, 23, 25, 35, 45}`. This kills 13 of the 52 new
nine-particle survivor classes. -/
theorem pattern_p6_impossible {X : Finset E3} (hX : HardCore X)
    {q : Fin 6 → E3} (hq : ∀ i, q i ∈ X) (hinj : Function.Injective q)
    (h01 : dist (q 0) (q 1) = 1) (h02 : dist (q 0) (q 2) = 1)
    (h03 : dist (q 0) (q 3) = 1) (h04 : dist (q 0) (q 4) = 1)
    (h12 : dist (q 1) (q 2) = 1) (h13 : dist (q 1) (q 3) = 1)
    (h15 : dist (q 1) (q 5) = 1) (h23 : dist (q 2) (q 3) = 1)
    (h25 : dist (q 2) (q 5) = 1) (h35 : dist (q 3) (q 5) = 1)
    (h45 : dist (q 4) (q 5) = 1) : False := by
  set y : Fin 6 → E3 := fun i => q i - q 1 with hy
  have hsep : ∀ i j, i ≠ j → (1:ℝ) ≤ dist (q i) (q j) ^ 2 := by
    intro i j hne
    have hd := hX (q i) (hq i) (q j) (hq j) (fun h => hne (hinj h))
    nlinarith [dist_nonneg (x := q i) (y := q j)]
  have hipgen : ∀ i j, (inner ℝ (y i) (y j) : ℝ)
      = (‖y i‖ ^ 2 + ‖y j‖ ^ 2 - dist (q i) (q j) ^ 2) / 2 := by
    intro i j
    have hkey := norm_sub_sq_real (y i) (y j)
    rw [show y i - y j = q i - q j by simp only [hy]; abel, ← dist_eq_norm] at hkey
    linarith
  have hnrm : ∀ i, ‖y i‖ = dist (q i) (q 1) := by
    intro i
    simp only [hy]
    rw [← dist_eq_norm]
  -- unit norms for the four base-adjacent vertices
  have hn0 : ‖y 0‖ = 1 := by rw [hnrm]; exact h01
  have hn2 : ‖y 2‖ = 1 := by rw [hnrm, dist_comm]; exact h12
  have hn3 : ‖y 3‖ = 1 := by rw [hnrm, dist_comm]; exact h13
  have hn5 : ‖y 5‖ = 1 := by rw [hnrm, dist_comm]; exact h15
  have hs0 : (inner ℝ (y 0) (y 0) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn0]; norm_num
  have hs2 : (inner ℝ (y 2) (y 2) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn2]; norm_num
  have hs3 : (inner ℝ (y 3) (y 3) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn3]; norm_num
  have hs5 : (inner ℝ (y 5) (y 5) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn5]; norm_num
  -- scalar unknowns
  set m : ℝ := dist (q 4) (q 1) ^ 2 with hmdef
  set c2 : ℝ := dist (q 2) (q 4) ^ 2 with hc2def
  set c3 : ℝ := dist (q 3) (q 4) ^ 2 with hc3def
  set p : ℝ := (inner ℝ (y 0) (y 5) : ℝ) with hpdef
  have hs4 : (inner ℝ (y 4) (y 4) : ℝ) = m := by
    rw [real_inner_self_eq_norm_sq, hnrm]
  have hm1 : 1 ≤ m := by rw [hmdef]; exact hsep 4 1 (by decide)
  have hc21 : 1 ≤ c2 := by rw [hc2def]; exact hsep 2 4 (by decide)
  have hc31 : 1 ≤ c3 := by rw [hc3def]; exact hsep 3 4 (by decide)
  -- hard-core bound on p through the (0,5) pair
  have hp12 : p ≤ 1 / 2 := by
    have h05 := hsep 0 5 (by decide)
    have := hipgen 0 5
    rw [hn0, hn5] at this
    rw [hpdef, this]
    nlinarith
  -- pinned inner products
  have e02 : (inner ℝ (y 0) (y 2) : ℝ) = 1 / 2 := by
    rw [hipgen, hn0, hn2, h02]; norm_num
  have e20 : (inner ℝ (y 2) (y 0) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e02
  have e03 : (inner ℝ (y 0) (y 3) : ℝ) = 1 / 2 := by
    rw [hipgen, hn0, hn3, h03]; norm_num
  have e30 : (inner ℝ (y 3) (y 0) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e03
  have e23 : (inner ℝ (y 2) (y 3) : ℝ) = 1 / 2 := by
    rw [hipgen, hn2, hn3, h23]; norm_num
  have e32 : (inner ℝ (y 3) (y 2) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e23
  have e25 : (inner ℝ (y 2) (y 5) : ℝ) = 1 / 2 := by
    rw [hipgen, hn2, hn5, h25]; norm_num
  have e52 : (inner ℝ (y 5) (y 2) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e25
  have e35 : (inner ℝ (y 3) (y 5) : ℝ) = 1 / 2 := by
    rw [hipgen, hn3, hn5, h35]; norm_num
  have e53 : (inner ℝ (y 5) (y 3) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e35
  have e40 : (inner ℝ (y 4) (y 0) : ℝ) = m / 2 := by
    rw [hipgen, hn0, hnrm 4, dist_comm (q 4) (q 0), h04, hmdef]
    ring
  have e04 : (inner ℝ (y 0) (y 4) : ℝ) = m / 2 := by rw [real_inner_comm]; exact e40
  have e45 : (inner ℝ (y 4) (y 5) : ℝ) = m / 2 := by
    rw [hipgen, hn5, hnrm 4, h45, hmdef]
    ring
  have e54 : (inner ℝ (y 5) (y 4) : ℝ) = m / 2 := by rw [real_inner_comm]; exact e45
  have e42 : (inner ℝ (y 4) (y 2) : ℝ) = (m + 1 - c2) / 2 := by
    rw [hipgen, hn2, hnrm 4, dist_comm (q 4) (q 2), hmdef, hc2def]
    ring
  have e24 : (inner ℝ (y 2) (y 4) : ℝ) = (m + 1 - c2) / 2 := by
    rw [real_inner_comm]; exact e42
  have e43 : (inner ℝ (y 4) (y 3) : ℝ) = (m + 1 - c3) / 2 := by
    rw [hipgen, hn3, hnrm 4, dist_comm (q 4) (q 3), hmdef, hc3def]
    ring
  have e34 : (inner ℝ (y 3) (y 4) : ℝ) = (m + 1 - c3) / 2 := by
    rw [real_inner_comm]; exact e43
  have e50 : (inner ℝ (y 5) (y 0) : ℝ) = p := by
    rw [real_inner_comm]
  -- Step 1: p = −1/3 from det G[y0,y2,y3,y5] = 0
  have hp : p = -(1 / 3) := by
    have hd := gram_det_zero ![y 0, y 2, y 3, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hs0, hs2, hs3, hs5, e02, e20, e03, e30, e23, e32, e25, e52, e35, e53,
      ← hpdef, e50] at hd
    have hfact : (p - 1) * (3 * p + 1) = 0 := by linear_combination (-4 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  -- Step 2: det G[y0,y2,y4,y5] = 0 at p = −1/3 forces c2 = m = 1
  have hf2 : c2 ^ 2 + c2 * m + m ^ 2 - 2 * c2 - 2 * m + 1 = 0 := by
    have hd := gram_det_zero ![y 0, y 2, y 4, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hs0, hs2, hs4, hs5, e02, e20, e04, e40, e24, e42, e45, e54, e25, e52,
      ← hpdef, e50, hp] at hd
    linear_combination (-9 / 2 : ℝ) * hd
  have hkey2 : (c2 - 1) ^ 2 + (c2 - 1) * (m - 1) + (m - 1) ^ 2
      + (c2 - 1) + (m - 1) = 0 := by linear_combination hf2
  have hm : m = 1 := by
    linarith [sq_nonneg (c2 - 1), sq_nonneg (m - 1),
      mul_nonneg (sub_nonneg.mpr hc21) (sub_nonneg.mpr hm1),
      sub_nonneg.mpr hc21, sub_nonneg.mpr hm1]
  have hc2 : c2 = 1 := by
    linarith [sq_nonneg (c2 - 1), sq_nonneg (m - 1),
      mul_nonneg (sub_nonneg.mpr hc21) (sub_nonneg.mpr hm1),
      sub_nonneg.mpr hc21, sub_nonneg.mpr hm1]
  -- Step 3: det G[y0,y3,y4,y5] = 0 at p = −1/3 forces c3 = 1
  have hf3 : c3 ^ 2 + c3 * m + m ^ 2 - 2 * c3 - 2 * m + 1 = 0 := by
    have hd := gram_det_zero ![y 0, y 3, y 4, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hs0, hs3, hs4, hs5, e03, e30, e04, e40, e34, e43, e45, e54, e35, e53,
      ← hpdef, e50, hp] at hd
    linear_combination (-9 / 2 : ℝ) * hd
  have hkey3 : (c3 - 1) ^ 2 + (c3 - 1) * (m - 1) + (m - 1) ^ 2
      + (c3 - 1) + (m - 1) = 0 := by linear_combination hf3
  have hc3 : c3 = 1 := by
    linarith [sq_nonneg (c3 - 1), sq_nonneg (m - 1),
      mul_nonneg (sub_nonneg.mpr hc31) (sub_nonneg.mpr hm1),
      sub_nonneg.mpr hc31, sub_nonneg.mpr hm1]
  -- Step 4: det G[y0,y2,y3,y4] = 5/16 ≠ 0 — contradiction
  have hd := gram_det_zero ![y 0, y 2, y 3, y 4]
  rw [det_fin_four] at hd
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
    ] at hd
  rw [hs0, hs2, hs3, hs4, e02, e20, e03, e30, e04, e40, e23, e32, e24, e42,
    e34, e43, hm, hc2, hc3] at hd
  norm_num at hd

end Kissing3D
