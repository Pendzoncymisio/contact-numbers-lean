import ContactNumbers.Cap8

set_option linter.style.header false
set_option maxHeartbeats 1000000

/-!
# Gram-determinant kills for `E_min(8)`

Four vectors of `ℝ³` are dependent, so every `4 × 4` Gram determinant vanishes
(`gram_det_zero`). For the seven-point obstruction patterns of the `E_min(8)`
programme this pins the free inner products of a recentred shell one determinant at a
time — exactly as `ring_two_positions` did on the ring circle — until a determinant
appears whose admissible roots all violate the hard core.

This file starts with the general machinery and the P1 pattern (which kills survivor
classes 0, 1, 2 of the 19-bond enumeration): a particle bonded to six others whose
shell carries the nine-contact code `{03, 04, 05, 12, 14, 15, 23, 24, 34}`.
-/

namespace Kissing3D

open Finset

/-- **Four vectors of `ℝ³` have a singular Gram matrix.** -/
lemma gram_det_zero (v : Fin 4 → E3) :
    (Matrix.of fun i j => (inner ℝ (v i) (v j) : ℝ)).det = 0 := by
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [finrank_euclideanSpace_fin] at this
    simp at this
  obtain ⟨g, hg0, i₀, hgi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨g, fun hg => hgi₀ (by rw [hg]; rfl), ?_⟩
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  have hz : (inner ℝ (v i) (∑ j, g j • v j) : ℝ) = 0 := by
    rw [hg0, inner_zero_right]
  rw [inner_sum] at hz
  simp only [real_inner_smul_right] at hz
  rw [← hz]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Cofactor expansion of a `4 × 4` real determinant, entrywise. -/
private lemma det_fin_four (M : Matrix (Fin 4) (Fin 4) ℝ) :
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

/-- **The P1 shell pattern is impossible**: no hard-core particle can be bonded to six
others carrying the nine-contact shell code `{03, 04, 05, 12, 14, 15, 23, 24, 34}`.
Recentred on the centre, the shell is six unit vectors with nine inner products pinned
at `1/2`; vanishing `4×4` Gram determinants force `⟨y₀,y₂⟩ = ⟨y₁,y₃⟩ = −1/3` and
`⟨y₀,y₁⟩ = −7/18`, and then `det G[y₀,y₁,y₄,y₅] = 0` has roots `{1, 7/11}` — both
beyond the hard-core bound `1/2`. This kills survivor classes 0, 1, 2 of the 19-bond
eight-particle enumeration. -/
theorem pattern_p1_impossible {X : Finset E3} (hX : HardCore X)
    {c : E3} {u : Fin 6 → E3} (_hc : c ∈ X) (hu : ∀ i, u i ∈ X)
    (huinj : Function.Injective u)
    (hbond : ∀ i, dist c (u i) = 1)
    (h03 : dist (u 0) (u 3) = 1) (h04 : dist (u 0) (u 4) = 1)
    (h05 : dist (u 0) (u 5) = 1) (h12 : dist (u 1) (u 2) = 1)
    (h14 : dist (u 1) (u 4) = 1) (h15 : dist (u 1) (u 5) = 1)
    (h23 : dist (u 2) (u 3) = 1) (h24 : dist (u 2) (u 4) = 1)
    (h34 : dist (u 3) (u 4) = 1) : False := by
  set y : Fin 6 → E3 := fun i => u i - c with hy
  have hnorm : ∀ i, ‖y i‖ = 1 := by
    intro i
    simp only [hy]
    rw [← dist_eq_norm, dist_comm]
    exact hbond i
  have hipd : ∀ i j, (inner ℝ (y i) (y j) : ℝ) = 1 - dist (u i) (u j) ^ 2 / 2 := by
    intro i j
    have hkey := norm_sub_sq_real (y i) (y j)
    rw [show y i - y j = u i - u j by simp only [hy]; abel, ← dist_eq_norm,
      hnorm i, hnorm j] at hkey
    linarith
  have hip : ∀ i j, dist (u i) (u j) = 1 → (inner ℝ (y i) (y j) : ℝ) = 1/2 := by
    intro i j h
    rw [hipd i j, h]
    norm_num
  have hle : ∀ i j, i ≠ j → (inner ℝ (y i) (y j) : ℝ) ≤ 1/2 := by
    intro i j hne
    have hd := hX (u i) (hu i) (u j) (hu j) (fun h => hne (huinj h))
    have hd2 : (1:ℝ) ≤ dist (u i) (u j) ^ 2 := by
      nlinarith [dist_nonneg (x := u i) (y := u j)]
    rw [hipd i j]
    linarith
  have hself : ∀ i, (inner ℝ (y i) (y i) : ℝ) = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, hnorm i]
    norm_num
  -- the nine pinned inner products, both orientations
  have e03 := hip 0 3 h03
  have e30 := hip 3 0 (by rw [dist_comm]; exact h03)
  have e04 := hip 0 4 h04
  have e40 := hip 4 0 (by rw [dist_comm]; exact h04)
  have e05 := hip 0 5 h05
  have e50 := hip 5 0 (by rw [dist_comm]; exact h05)
  have e12 := hip 1 2 h12
  have e21 := hip 2 1 (by rw [dist_comm]; exact h12)
  have e14 := hip 1 4 h14
  have e41 := hip 4 1 (by rw [dist_comm]; exact h14)
  have e15 := hip 1 5 h15
  have e51 := hip 5 1 (by rw [dist_comm]; exact h15)
  have e23 := hip 2 3 h23
  have e32 := hip 3 2 (by rw [dist_comm]; exact h23)
  have e24 := hip 2 4 h24
  have e42 := hip 4 2 (by rw [dist_comm]; exact h24)
  have e34 := hip 3 4 h34
  have e43 := hip 4 3 (by rw [dist_comm]; exact h34)
  -- Step 1: ⟨y₀,y₂⟩ = −1/3 from det G[0,2,3,4] = 0
  have hα02 : (inner ℝ (y 0) (y 2) : ℝ) = -(1/3) := by
    have hd := gram_det_zero ![y 0, y 2, y 3, y 4]
    have hsym := real_inner_comm (y 0) (y 2)
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself, hself, hself, hself, e03, e30, e04, e40, e23, e32, e24, e42, e34, e43,
      hsym] at hd
    have hfact : ((inner ℝ (y 0) (y 2) : ℝ) - 1) * (3 * inner ℝ (y 0) (y 2) + 1) = 0 := by
      linear_combination (-4 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso
      have := hle 0 2 (by decide)
      linarith
    · linarith
  -- Step 2: ⟨y₁,y₃⟩ = −1/3 from det G[1,2,3,4] = 0
  have hα13 : (inner ℝ (y 1) (y 3) : ℝ) = -(1/3) := by
    have hd := gram_det_zero ![y 1, y 2, y 3, y 4]
    have hsym := real_inner_comm (y 1) (y 3)
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself, hself, hself, hself, e12, e21, e14, e41, e23, e32, e24, e42, e34, e43,
      hsym] at hd
    have hfact : ((inner ℝ (y 1) (y 3) : ℝ) - 1) * (3 * inner ℝ (y 1) (y 3) + 1) = 0 := by
      linear_combination (-4 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso
      have := hle 1 3 (by decide)
      linarith
    · linarith
  have s02 := real_inner_comm (y 0) (y 2)
  have s13 := real_inner_comm (y 1) (y 3)
  have hβ02 : (inner ℝ (y 2) (y 0) : ℝ) = -(1/3) := by rw [s02, hα02]
  have hβ13 : (inner ℝ (y 3) (y 1) : ℝ) = -(1/3) := by rw [s13, hα13]
  -- Step 3: ⟨y₀,y₁⟩ = −7/18 by intersecting det G[0,1,2,3] = 0 and det G[0,1,2,4] = 0
  have hα01 : (inner ℝ (y 0) (y 1) : ℝ) = -(7/18) := by
    have hd1 := gram_det_zero ![y 0, y 1, y 2, y 3]
    have hd2 := gram_det_zero ![y 0, y 1, y 2, y 4]
    have hsym := real_inner_comm (y 0) (y 1)
    rw [det_fin_four] at hd1 hd2
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd1 hd2
    rw [hself, hself, hself, hself, hα02, hβ02, e03, e30, e12, e21, e23, e32,
      hα13, hβ13, hsym] at hd1
    rw [hself, hself, hself, hself, hα02, hβ02, e04, e40, e12, e21, e14, e41,
      e24, e42, hsym] at hd2
    have hf1 : (18 * (inner ℝ (y 0) (y 1) : ℝ) + 7) * (54 * inner ℝ (y 0) (y 1) + 53)
        = 0 := by
      linear_combination (-1296 : ℝ) * hd1
    have hf2 : (2 * (inner ℝ (y 0) (y 1) : ℝ) - 1) * (18 * inner ℝ (y 0) (y 1) + 7)
        = 0 := by
      linear_combination (-48 : ℝ) * hd2
    rcases mul_eq_zero.mp hf1 with h | h
    · linarith
    · -- ⟨y₀,y₁⟩ = −53/54 fails the second determinant
      exfalso
      have hval : (inner ℝ (y 0) (y 1) : ℝ) = -(53/54) := by linarith
      rw [hval] at hf2
      norm_num at hf2
  have hβ01 : (inner ℝ (y 1) (y 0) : ℝ) = -(7/18) := by
    rw [real_inner_comm (y 0) (y 1), hα01]
  -- Step 4: det G[0,1,4,5] = 0 has no admissible root
  have hd := gram_det_zero ![y 0, y 1, y 4, y 5]
  have hsym := real_inner_comm (y 4) (y 5)
  rw [det_fin_four] at hd
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
    ] at hd
  rw [hself, hself, hself, hself, hα01, hβ01, e04, e40, e05, e50, e14, e41, e15, e51,
    hsym] at hd
  have hfact : ((inner ℝ (y 4) (y 5) : ℝ) - 1) * (11 * inner ℝ (y 4) (y 5) - 7) = 0 := by
    linear_combination (-1296/100 : ℝ) * hd
  have hle45 := hle 4 5 (by decide)
  rcases mul_eq_zero.mp hfact with h | h
  · linarith
  · linarith

/-! ### The P4 pattern: the prism shell

The second obstruction pattern is a particle bonded to six others whose shell code is
the **triangular prism** `{01, 04, 05, 12, 13, 23, 25, 34, 45}`. The six free inner
products sit on a 6-cycle; opposite pairs satisfy the exact Möbius relation
`ad + a + d = 0` (their Gram determinant factors as `(a−1)(d−1)(ad+a+d)` and the hard
core kills the linear factors), which also confines every variable to `[−1/3, 1/2]`.
Adjacent pairs satisfy the ellipse `Q(a,b) = 12a² − 8ab − 4a + 12b² − 4b − 5 = 0`, and
on the box `−Q` is a positive combination of four boundary products, so `Q = 0` forces
the corner alternation `{−1/3, 1/2}`. Either alternating pattern makes some fully
determined Gram determinant equal `−80/81 ≠ 0`. -/

/-- The Möbius box: `ad + a + d = 0` with `a ≥ −1` and `d ≤ 1/2` forces `a ≥ −1/3`. -/
private lemma F_box {a d : ℝ} (h : a * d + a + d = 0) (ha : -1 ≤ a) (hd : d ≤ 1/2) :
    -(1/3) ≤ a := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1/2 - d) (by linarith : (0:ℝ) ≤ 1 + a)]

/-- On the box `[−1/3, 1/2]²` the ellipse `Q = 0` passes only through the two corners
`(−1/3, 1/2)` and `(1/2, −1/3)`: `−Q` is a positive combination of four nonnegative
boundary products. -/
private lemma Q_corner {a b : ℝ}
    (hQ : 12*a^2 - 8*a*b - 4*a + 12*b^2 - 4*b - 5 = 0)
    (ha1 : -(1/3) ≤ a) (ha2 : a ≤ 1/2) (hb1 : -(1/3) ≤ b) (hb2 : b ≤ 1/2) :
    (a = -(1/3) ∧ b = 1/2) ∨ (a = 1/2 ∧ b = -(1/3)) := by
  have t1 : (0:ℝ) ≤ (a + 1/3) * (1/2 - a) := mul_nonneg (by linarith) (by linarith)
  have t2 : (0:ℝ) ≤ (b + 1/3) * (1/2 - b) := mul_nonneg (by linarith) (by linarith)
  have t3 : (0:ℝ) ≤ (a + 1/3) * (b + 1/3) := mul_nonneg (by linarith) (by linarith)
  have t4 : (0:ℝ) ≤ (1/2 - a) * (1/2 - b) := mul_nonneg (by linarith) (by linarith)
  have hsum : 12 * ((a + 1/3) * (1/2 - a)) + 12 * ((b + 1/3) * (1/2 - b))
      + (36/5) * ((a + 1/3) * (b + 1/3)) + (4/5) * ((1/2 - a) * (1/2 - b)) = 0 := by
    linear_combination -hQ
  have h1 : (a + 1/3) * (1/2 - a) = 0 := by linarith
  have h3 : (a + 1/3) * (b + 1/3) = 0 := by linarith
  have h4 : (1/2 - a) * (1/2 - b) = 0 := by linarith
  rcases mul_eq_zero.mp h1 with h | h
  · left
    have hA : a = -(1/3) := by linarith
    refine ⟨hA, ?_⟩
    rcases mul_eq_zero.mp h4 with h' | h'
    · exfalso; rw [hA] at h'; norm_num at h'
    · linarith
  · right
    have hA : a = 1/2 := by linarith
    refine ⟨hA, ?_⟩
    rcases mul_eq_zero.mp h3 with h' | h'
    · exfalso; rw [hA] at h'; norm_num at h'
    · linarith

/-- **The P4 shell pattern is impossible**: no hard-core particle can be bonded to six
others carrying the prism shell code `{01, 04, 05, 12, 13, 23, 25, 34, 45}`. Kills
survivor class 3 of the 19-bond eight-particle enumeration. -/
theorem pattern_p4_impossible {X : Finset E3} (hX : HardCore X)
    {c : E3} {u : Fin 6 → E3} (_hc : c ∈ X) (hu : ∀ i, u i ∈ X)
    (huinj : Function.Injective u)
    (hbond : ∀ i, dist c (u i) = 1)
    (h01 : dist (u 0) (u 1) = 1) (h04 : dist (u 0) (u 4) = 1)
    (h05 : dist (u 0) (u 5) = 1) (h12 : dist (u 1) (u 2) = 1)
    (h13 : dist (u 1) (u 3) = 1) (h23 : dist (u 2) (u 3) = 1)
    (h25 : dist (u 2) (u 5) = 1) (h34 : dist (u 3) (u 4) = 1)
    (h45 : dist (u 4) (u 5) = 1) : False := by
  set y : Fin 6 → E3 := fun i => u i - c with hy
  have hnorm : ∀ i, ‖y i‖ = 1 := by
    intro i
    simp only [hy]
    rw [← dist_eq_norm, dist_comm]
    exact hbond i
  have hipd : ∀ i j, (inner ℝ (y i) (y j) : ℝ) = 1 - dist (u i) (u j) ^ 2 / 2 := by
    intro i j
    have hkey := norm_sub_sq_real (y i) (y j)
    rw [show y i - y j = u i - u j by simp only [hy]; abel, ← dist_eq_norm,
      hnorm i, hnorm j] at hkey
    linarith
  have hip : ∀ i j, dist (u i) (u j) = 1 → (inner ℝ (y i) (y j) : ℝ) = 1/2 := by
    intro i j h
    rw [hipd i j, h]
    norm_num
  have hle : ∀ i j, i ≠ j → (inner ℝ (y i) (y j) : ℝ) ≤ 1/2 := by
    intro i j hne
    have hd := hX (u i) (hu i) (u j) (hu j) (fun h => hne (huinj h))
    have hd2 : (1:ℝ) ≤ dist (u i) (u j) ^ 2 := by
      nlinarith [dist_nonneg (x := u i) (y := u j)]
    rw [hipd i j]
    linarith
  have hge : ∀ i j, (-1 : ℝ) ≤ inner ℝ (y i) (y j) := by
    intro i j
    have habs := abs_real_inner_le_norm (y i) (y j)
    rw [hnorm i, hnorm j] at habs
    have := abs_le.mp (by simpa using habs)
    exact this.1
  have hself : ∀ i, (inner ℝ (y i) (y i) : ℝ) = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, hnorm i]
    norm_num
  -- pinned inner products, both orientations
  have e01 := hip 0 1 h01
  have e10 := hip 1 0 (by rw [dist_comm]; exact h01)
  have e04 := hip 0 4 h04
  have e40 := hip 4 0 (by rw [dist_comm]; exact h04)
  have e05 := hip 0 5 h05
  have e50 := hip 5 0 (by rw [dist_comm]; exact h05)
  have e12 := hip 1 2 h12
  have e21 := hip 2 1 (by rw [dist_comm]; exact h12)
  have e13 := hip 1 3 h13
  have e31 := hip 3 1 (by rw [dist_comm]; exact h13)
  have e23 := hip 2 3 h23
  have e32 := hip 3 2 (by rw [dist_comm]; exact h23)
  have e25 := hip 2 5 h25
  have e52 := hip 5 2 (by rw [dist_comm]; exact h25)
  have e34 := hip 3 4 h34
  have e43 := hip 4 3 (by rw [dist_comm]; exact h34)
  have e45 := hip 4 5 h45
  have e54 := hip 5 4 (by rw [dist_comm]; exact h45)
  -- symmetry for the six free pairs
  have s20 := real_inner_comm (y 0) (y 2)
  have s30 := real_inner_comm (y 0) (y 3)
  have s41 := real_inner_comm (y 1) (y 4)
  have s51 := real_inner_comm (y 1) (y 5)
  have s42 := real_inner_comm (y 2) (y 4)
  have s53 := real_inner_comm (y 3) (y 5)
  -- Möbius relations on the three opposite pairs
  have hrel1 : (inner ℝ (y 0) (y 2) : ℝ) * inner ℝ (y 1) (y 5)
      + inner ℝ (y 0) (y 2) + inner ℝ (y 1) (y 5) = 0 := by
    have hd := gram_det_zero ![y 0, y 1, y 2, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself, hself, hself, hself, e01, e10, e05, e50, e12, e21, e25, e52,
      s20, s51] at hd
    have hfact : ((inner ℝ (y 0) (y 2) : ℝ) - 1) * ((inner ℝ (y 1) (y 5) : ℝ) - 1)
        * ((inner ℝ (y 0) (y 2) : ℝ) * inner ℝ (y 1) (y 5)
          + inner ℝ (y 0) (y 2) + inner ℝ (y 1) (y 5)) = 0 := by
      linear_combination hd
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h' | h'
      · have := hle 0 2 (by decide); linarith
      · have := hle 1 5 (by decide); linarith
    · exact h
  have hrel2 : (inner ℝ (y 0) (y 3) : ℝ) * inner ℝ (y 1) (y 4)
      + inner ℝ (y 0) (y 3) + inner ℝ (y 1) (y 4) = 0 := by
    have hd := gram_det_zero ![y 0, y 1, y 3, y 4]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself, hself, hself, hself, e01, e10, e04, e40, e13, e31, e34, e43,
      s30, s41] at hd
    have hfact : ((inner ℝ (y 0) (y 3) : ℝ) - 1) * ((inner ℝ (y 1) (y 4) : ℝ) - 1)
        * ((inner ℝ (y 0) (y 3) : ℝ) * inner ℝ (y 1) (y 4)
          + inner ℝ (y 0) (y 3) + inner ℝ (y 1) (y 4)) = 0 := by
      linear_combination hd
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h' | h'
      · have := hle 0 3 (by decide); linarith
      · have := hle 1 4 (by decide); linarith
    · exact h
  have hrel3 : (inner ℝ (y 2) (y 4) : ℝ) * inner ℝ (y 3) (y 5)
      + inner ℝ (y 2) (y 4) + inner ℝ (y 3) (y 5) = 0 := by
    have hd := gram_det_zero ![y 2, y 3, y 4, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself, hself, hself, hself, e23, e32, e25, e52, e34, e43, e45, e54,
      s42, s53] at hd
    have hfact : ((inner ℝ (y 2) (y 4) : ℝ) - 1) * ((inner ℝ (y 3) (y 5) : ℝ) - 1)
        * ((inner ℝ (y 2) (y 4) : ℝ) * inner ℝ (y 3) (y 5)
          + inner ℝ (y 2) (y 4) + inner ℝ (y 3) (y 5)) = 0 := by
      linear_combination hd
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h' | h'
      · have := hle 2 4 (by decide); linarith
      · have := hle 3 5 (by decide); linarith
    · exact h
  -- every free variable lies in [−1/3, 1/2]
  have hb02 : -(1/3) ≤ (inner ℝ (y 0) (y 2) : ℝ) := F_box hrel1 (hge 0 2) (hle 1 5 (by decide))
  have hb15 : -(1/3) ≤ (inner ℝ (y 1) (y 5) : ℝ) :=
    F_box (by linear_combination hrel1) (hge 1 5) (hle 0 2 (by decide))
  have hb03 : -(1/3) ≤ (inner ℝ (y 0) (y 3) : ℝ) := F_box hrel2 (hge 0 3) (hle 1 4 (by decide))
  have hb14 : -(1/3) ≤ (inner ℝ (y 1) (y 4) : ℝ) :=
    F_box (by linear_combination hrel2) (hge 1 4) (hle 0 3 (by decide))
  have hb24 : -(1/3) ≤ (inner ℝ (y 2) (y 4) : ℝ) := F_box hrel3 (hge 2 4) (hle 3 5 (by decide))
  have hb35 : -(1/3) ≤ (inner ℝ (y 3) (y 5) : ℝ) :=
    F_box (by linear_combination hrel3) (hge 3 5) (hle 2 4 (by decide))
  -- the two adjacent ellipses pin the corner alternation
  have hQ1 : 12 * (inner ℝ (y 0) (y 2) : ℝ)^2
      - 8 * inner ℝ (y 0) (y 2) * inner ℝ (y 0) (y 3) - 4 * inner ℝ (y 0) (y 2)
      + 12 * (inner ℝ (y 0) (y 3) : ℝ)^2 - 4 * inner ℝ (y 0) (y 3) - 5 = 0 := by
    have hd := gram_det_zero ![y 0, y 1, y 2, y 3]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself, hself, hself, hself, e01, e10, e12, e21, e13, e31, e23, e32,
      s20, s30] at hd
    linear_combination (-16 : ℝ) * hd
  have hQ2 : 12 * (inner ℝ (y 0) (y 3) : ℝ)^2
      - 8 * inner ℝ (y 0) (y 3) * inner ℝ (y 3) (y 5) - 4 * inner ℝ (y 0) (y 3)
      + 12 * (inner ℝ (y 3) (y 5) : ℝ)^2 - 4 * inner ℝ (y 3) (y 5) - 5 = 0 := by
    have hd := gram_det_zero ![y 0, y 3, y 4, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself, hself, hself, hself, e04, e40, e05, e50, e34, e43, e45, e54,
      s30, s53] at hd
    linear_combination (-16 : ℝ) * hd
  have hab := Q_corner hQ1 hb02 (hle 0 2 (by decide)) hb03 (hle 0 3 (by decide))
  have hbc := Q_corner hQ2 hb03 (hle 0 3 (by decide)) hb35 (hle 3 5 (by decide))
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- α₀₂ = −1/3, α₀₃ = 1/2, hence γ₃₅ = −1/3, ε₁₄ = −1/3, φ₂₄ = 1/2
    have hg : (inner ℝ (y 3) (y 5) : ℝ) = -(1/3) := by
      rcases hbc with ⟨hb', _⟩ | ⟨_, hg⟩
      · exfalso; rw [hb] at hb'; norm_num at hb'
      · exact hg
    have he14 : (inner ℝ (y 1) (y 4) : ℝ) = -(1/3) := by
      rw [hb] at hrel2; linarith
    have hf24 : (inner ℝ (y 2) (y 4) : ℝ) = 1/2 := by
      rw [hg] at hrel3; linarith
    have hd := gram_det_zero ![y 0, y 1, y 2, y 4]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself, hself, hself, hself, e01, e10, e04, e40, e12, e21, s20, s41, s42,
      ha, he14, hf24] at hd
    norm_num at hd
  · -- α₀₂ = 1/2, α₀₃ = −1/3, hence γ₃₅ = 1/2, δ₁₅ = −1/3
    have hg : (inner ℝ (y 3) (y 5) : ℝ) = 1/2 := by
      rcases hbc with ⟨_, hg⟩ | ⟨hb', _⟩
      · exact hg
      · exfalso; rw [hb] at hb'; norm_num at hb'
    have hd15 : (inner ℝ (y 1) (y 5) : ℝ) = -(1/3) := by
      rw [ha] at hrel1; linarith
    have hd := gram_det_zero ![y 0, y 1, y 3, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself, hself, hself, hself, e01, e10, e05, e50, e13, e31, s30, s51, s53,
      hb, hd15, hg] at hd
    norm_num at hd

/-! ### The P5 pattern

The last obstruction has no cone vertex. Recentring at the degree-five vertex leaves
five unit shell vectors `y₁ … y₅` and one long vector `y₀` with `R := ⟨y₀,y₀⟩ ≥ 1`,
bonded to `y₃, y₄, y₅` (`⟨y₀,y_k⟩ = R/2`) but not to the centre. The shell carries the
Möbius pair `(a, b) = (⟨y₁,y₃⟩, ⟨y₂,y₄⟩)` and two ellipses `Q(a, c) = Q(b, d) = 0` with
`c = ⟨y₃,y₅⟩`, `d = ⟨y₄,y₅⟩`. `Q_split` reduces each ellipse to a corner or `≤ −1/3`;
in every branch the `y₀`-determinants pin everything — `R = 1` and saturated contacts —
and a final determinant equals `−80/81`, or the Möbius relation itself explodes. The
case analysis lives in the scalar lemma `p5_scalar`. -/

/-- On the strip `a ∈ [−1/3, 1/2]`, `b ≤ 1/2`, the ellipse `Q = 0` forces the corner
`(−1/3, 1/2)` or `b ≤ −1/3`. -/
private lemma Q_split {a b : ℝ}
    (hQ : 12*a^2 - 8*a*b - 4*a + 12*b^2 - 4*b - 5 = 0)
    (ha1 : -(1/3) ≤ a) (ha2 : a ≤ 1/2) (hb2 : b ≤ 1/2) :
    (a = -(1/3) ∧ b = 1/2) ∨ b ≤ -(1/3) := by
  by_cases hb : b ≤ -(1/3)
  · exact Or.inr hb
  · left
    have hb' : -(1/3) < b := not_le.mp hb
    rcases Q_corner hQ ha1 ha2 (le_of_lt hb') hb2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exfalso
      rw [h2] at hb'
      exact lt_irrefl _ hb'

/-- The scalar heart of the P5 kill: the sixteen Gram facts of the recentred
configuration are jointly contradictory. -/
private lemma p5_scalar {R p1 p2 a b c d : ℝ}
    (hR1 : 1 ≤ R) (hp1 : p1 ≤ R/2) (hp2 : p2 ≤ R/2)
    (ha1 : -(1/3) ≤ a) (ha2 : a ≤ 1/2) (hb1 : -(1/3) ≤ b) (hb2 : b ≤ 1/2)
    (hc1 : (-1:ℝ) ≤ c) (hc2 : c ≤ 1/2) (hd1 : (-1:ℝ) ≤ d) (hd2 : d ≤ 1/2)
    (hF : a*b + a + b = 0)
    (hQ1 : 12*a^2 - 8*a*c - 4*a + 12*c^2 - 4*c - 5 = 0)
    (hQ2 : 12*b^2 - 8*b*d - 4*b + 12*d^2 - 4*d - 5 = 0)
    (hbr8 : 4*R*c^2 - 8*R*c*d + 4*R*c + 4*R*d^2 + 4*R*d - 7*R
      - 16*c^2 + 16*c*d - 16*d^2 + 12 = 0)
    (hB1 : R^2 - 2*R*p1 - 2*R*d - R + 2*p1^2*(d+1) = 0)
    (hB2 : R^2 - 2*R*p2 - 2*R*c - R + 2*p2^2*(c+1) = 0)
    (hK1 : -3*R^2 - 16*R*a^2 + 16*R*a*p1 - 8*R*a*p2 + 8*R*a - 4*R*p1 + 8*R*p2 + 8*R
      + 16*a^2*p2^2 - 16*a*p1*p2 - 12*p1^2 + 16*p1*p2 - 16*p2^2 = 0)
    (hK2 : -3*R^2 - 16*R*b^2 - 8*R*b*p1 + 16*R*b*p2 + 8*R*b + 8*R*p1 - 4*R*p2 + 8*R
      + 16*b^2*p1^2 - 16*b*p1*p2 - 16*p1^2 + 16*p1*p2 - 12*p2^2 = 0) : False := by
  rcases Q_split hQ1 ha1 ha2 hc2 with ⟨hav, hcv⟩ | hcle
  · rcases Q_split hQ2 hb1 hb2 hd2 with ⟨hbv, _⟩ | hdle
    · rw [hav, hbv] at hF
      norm_num at hF
    · have hbv : b = 1/2 := by rw [hav] at hF; linarith
      have hdv : d = -(1/3) := by
        rw [hbv] at hQ2
        have hfact : (3*d + 1) * (d - 1) = 0 := by linear_combination (1/4 : ℝ) * hQ2
        rcases mul_eq_zero.mp hfact with h | h
        · linarith
        · linarith
      have hRe : R = 1 := by rw [hcv, hdv] at hbr8; linarith
      have hp1v : p1 = 1/2 := by
        rw [hdv, hRe] at hB1
        have hfact : (2*p1 - 1) * (p1 - 1) = 0 := by linear_combination (3/2 : ℝ) * hB1
        rcases mul_eq_zero.mp hfact with h | h
        · linarith
        · rw [hRe] at hp1; linarith
      have hp2v : p2 = -(1/3) := by
        rw [hcv, hRe] at hB2
        have hfact : (3*p2 + 1) * (p2 - 1) = 0 := by linear_combination hB2
        rcases mul_eq_zero.mp hfact with h | h
        · linarith
        · rw [hRe] at hp2; linarith
      rw [hav, hRe, hp1v, hp2v] at hK1
      norm_num at hK1
  · rcases Q_split hQ2 hb1 hb2 hd2 with ⟨hbv, hdv⟩ | hdle
    · have hav : a = 1/2 := by rw [hbv] at hF; linarith
      have hcv : c = -(1/3) := by
        rw [hav] at hQ1
        have hfact : (3*c + 1) * (c - 1) = 0 := by linear_combination (1/4 : ℝ) * hQ1
        rcases mul_eq_zero.mp hfact with h | h
        · linarith
        · linarith
      have hRe : R = 1 := by rw [hcv, hdv] at hbr8; linarith
      have hp2v : p2 = 1/2 := by
        rw [hcv, hRe] at hB2
        have hfact : (2*p2 - 1) * (p2 - 1) = 0 := by linear_combination (3/2 : ℝ) * hB2
        rcases mul_eq_zero.mp hfact with h | h
        · linarith
        · rw [hRe] at hp2; linarith
      have hp1v : p1 = -(1/3) := by
        rw [hdv, hRe] at hB1
        have hfact : (3*p1 + 1) * (p1 - 1) = 0 := by linear_combination hB1
        rcases mul_eq_zero.mp hfact with h | h
        · linarith
        · rw [hRe] at hp1; linarith
      rw [hbv, hRe, hp1v, hp2v] at hK2
      norm_num at hK2
    · -- both `c, d ≤ −1/3`: contact saturation
      have hf1 : (0:ℝ) ≤ R/2 - p1 := by linarith
      have h1 : R + 2*p1 ≤ 2*R := by linarith
      have h2 : (0:ℝ) ≤ d + 1 := by linarith
      have h3 : (d+1)*(R + 2*p1) ≤ (d+1)*(2*R) := mul_le_mul_of_nonneg_left h1 h2
      have h4 : (0:ℝ) ≤ (-d) * (2*R) := mul_nonneg (by linarith) (by linarith)
      have h5 : (d+1)*(2*R) = 2*R - (-d)*(2*R) := by ring
      have hf2 : (d+1)*(R + 2*p1) - 2*R ≤ 0 := by linarith
      have hident : (d+1)*R^2/2 - 2*R*d - R
          = (R/2 - p1) * ((d+1)*(R + 2*p1) - 2*R) := by
        linear_combination hB1
      have hprod : (0:ℝ) ≤ (R/2 - p1) * (2*R - (d+1)*(R + 2*p1)) :=
        mul_nonneg hf1 (by linarith)
      have hsum : (R/2 - p1) * ((d+1)*(R + 2*p1) - 2*R)
          + (R/2 - p1) * (2*R - (d+1)*(R + 2*p1)) = 0 := by ring
      have hg2 : (d+1)*R^2/2 - 2*R*d - R ≤ 0 := by linarith
      have hkey : (d+1)*R ≤ 4*d + 2 := by
        by_contra hcon
        push Not at hcon
        have hpos : (0:ℝ) < R * ((d+1)*R - (4*d + 2)) :=
          mul_pos (by linarith) (by linarith)
        have hring : R * ((d+1)*R - (4*d + 2)) = 2*((d+1)*R^2/2 - 2*R*d - R) := by
          ring
        linarith
      have hdv : d = -(1/3) := by
        have hlow : d + 1 ≤ (d+1)*R := le_mul_of_one_le_right h2 hR1
        linarith
      have hRe : R = 1 := by
        rw [hdv] at hkey
        linarith
      rw [hRe] at hB2 hp2
      have hf1' : (0:ℝ) ≤ 1/2 - p2 := by linarith
      have h1' : (1:ℝ) + 2*p2 ≤ 2 := by linarith
      have h2' : (0:ℝ) ≤ c + 1 := by linarith
      have h3' : (c+1)*(1 + 2*p2) ≤ (c+1)*2 := mul_le_mul_of_nonneg_left h1' h2'
      have h4' : (c+1)*2 ≤ 2 := by linarith
      have hf2' : (c+1)*(1 + 2*p2) - 2 ≤ 0 := by linarith
      have hident' : (c+1)/2 - 2*c - 1 = (1/2 - p2) * ((c+1)*(1 + 2*p2) - 2) := by
        linear_combination hB2
      have hprod' : (0:ℝ) ≤ (1/2 - p2) * (2 - (c+1)*(1 + 2*p2)) :=
        mul_nonneg hf1' (by linarith)
      have hsum' : (1/2 - p2) * ((c+1)*(1 + 2*p2) - 2)
          + (1/2 - p2) * (2 - (c+1)*(1 + 2*p2)) = 0 := by ring
      have hcv : c = -(1/3) := by linarith
      have hav : a = 1/2 := by
        rw [hcv] at hQ1
        have hfact : (2*a - 1) * (18*a + 7) = 0 := by linear_combination (3 : ℝ) * hQ1
        rcases mul_eq_zero.mp hfact with h | h
        · linarith
        · linarith
      have hbv : b = 1/2 := by
        rw [hdv] at hQ2
        have hfact : (2*b - 1) * (18*b + 7) = 0 := by linear_combination (3 : ℝ) * hQ2
        rcases mul_eq_zero.mp hfact with h | h
        · linarith
        · linarith
      rw [hav, hbv] at hF
      norm_num at hF

/-- **The P5 shell pattern is impossible**: no hard-core configuration contains a
particle `c` bonded to `u₁, …, u₅` but not `u₀`, with the bond pattern
`{03, 04, 05, 12, 14, 15, 23, 25, 34}` among `u₀, …, u₅`. Kills survivor class 4 of
the 19-bond eight-particle enumeration. -/
theorem pattern_p5_impossible {X : Finset E3} (hX : HardCore X)
    {c : E3} {u : Fin 6 → E3} (hc : c ∈ X) (hu : ∀ i, u i ∈ X)
    (huinj : Function.Injective u) (hu0c : u 0 ≠ c)
    (hcb1 : dist c (u 1) = 1) (hcb2 : dist c (u 2) = 1) (hcb3 : dist c (u 3) = 1)
    (hcb4 : dist c (u 4) = 1) (hcb5 : dist c (u 5) = 1)
    (h03 : dist (u 0) (u 3) = 1) (h04 : dist (u 0) (u 4) = 1)
    (h05 : dist (u 0) (u 5) = 1) (h12 : dist (u 1) (u 2) = 1)
    (h14 : dist (u 1) (u 4) = 1) (h15 : dist (u 1) (u 5) = 1)
    (h23 : dist (u 2) (u 3) = 1) (h25 : dist (u 2) (u 5) = 1)
    (h34 : dist (u 3) (u 4) = 1) : False := by
  set y : Fin 6 → E3 := fun i => u i - c with hy
  have hnormS : ∀ k : Fin 6, 1 ≤ (k : ℕ) → ‖y k‖ = 1 := by
    intro k hk
    have hd : dist c (u k) = 1 := by
      fin_cases k
      · simp at hk
      · exact hcb1
      · exact hcb2
      · exact hcb3
      · exact hcb4
      · exact hcb5
    simp only [hy]
    rw [← dist_eq_norm, dist_comm]
    exact hd
  have hipd : ∀ i j, 2 * (inner ℝ (y i) (y j) : ℝ)
      = inner ℝ (y i) (y i) + inner ℝ (y j) (y j) - dist (u i) (u j) ^ 2 := by
    intro i j
    have hkey := norm_sub_sq_real (y i) (y j)
    rw [show y i - y j = u i - u j by simp only [hy]; abel, ← dist_eq_norm,
      ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hkey
    linarith
  have hselfS : ∀ k : Fin 6, 1 ≤ (k : ℕ) → (inner ℝ (y k) (y k) : ℝ) = 1 := by
    intro k hk
    rw [real_inner_self_eq_norm_sq, hnormS k hk]
    norm_num
  have hself1 := hselfS 1 (by decide)
  have hself2 := hselfS 2 (by decide)
  have hself3 := hselfS 3 (by decide)
  have hself4 := hselfS 4 (by decide)
  have hself5 := hselfS 5 (by decide)
  have hR1 : (1:ℝ) ≤ inner ℝ (y 0) (y 0) := by
    have hd := hX c hc (u 0) (hu 0) (Ne.symm hu0c)
    rw [real_inner_self_eq_norm_sq]
    have he : ‖y 0‖ = dist c (u 0) := by
      simp only [hy]
      rw [← dist_eq_norm, dist_comm]
    rw [he]
    nlinarith [dist_nonneg (x := c) (y := u 0)]
  have hipS : ∀ i j : Fin 6, 1 ≤ (i : ℕ) → 1 ≤ (j : ℕ) → dist (u i) (u j) = 1 →
      (inner ℝ (y i) (y j) : ℝ) = 1/2 := by
    intro i j hi hj hd
    have := hipd i j
    rw [hselfS i hi, hselfS j hj, hd] at this
    linarith
  have hleS : ∀ i j : Fin 6, 1 ≤ (i : ℕ) → 1 ≤ (j : ℕ) → i ≠ j →
      (inner ℝ (y i) (y j) : ℝ) ≤ 1/2 := by
    intro i j hi hj hne
    have hd := hX (u i) (hu i) (u j) (hu j) (fun h => hne (huinj h))
    have hd2 : (1:ℝ) ≤ dist (u i) (u j) ^ 2 := by
      nlinarith [dist_nonneg (x := u i) (y := u j)]
    have := hipd i j
    rw [hselfS i hi, hselfS j hj] at this
    linarith
  have hgeS : ∀ i j : Fin 6, 1 ≤ (i : ℕ) → 1 ≤ (j : ℕ) →
      (-1 : ℝ) ≤ inner ℝ (y i) (y j) := by
    intro i j hi hj
    have habs := abs_real_inner_le_norm (y i) (y j)
    rw [hnormS i hi, hnormS j hj] at habs
    have := abs_le.mp (by simpa using habs)
    exact this.1
  have hip0 : ∀ k : Fin 6, 1 ≤ (k : ℕ) → dist (u 0) (u k) = 1 →
      (inner ℝ (y 0) (y k) : ℝ) = inner ℝ (y 0) (y 0) / 2 := by
    intro k hk hd
    have := hipd 0 k
    rw [hselfS k hk, hd] at this
    linarith
  have hple : ∀ k : Fin 6, 1 ≤ (k : ℕ) → k ≠ 0 →
      (inner ℝ (y 0) (y k) : ℝ) ≤ inner ℝ (y 0) (y 0) / 2 := by
    intro k hk hne
    have hd := hX (u 0) (hu 0) (u k) (hu k) (fun h => hne (huinj h).symm)
    have hd2 : (1:ℝ) ≤ dist (u 0) (u k) ^ 2 := by
      nlinarith [dist_nonneg (x := u 0) (y := u k)]
    have := hipd 0 k
    rw [hselfS k hk] at this
    linarith
  have hp1 := hple 1 (by decide) (by decide)
  have hp2 := hple 2 (by decide) (by decide)
  have e03 := hip0 3 (by decide) h03
  have e30 := (real_inner_comm (y 0) (y 3)).trans e03
  have e04 := hip0 4 (by decide) h04
  have e40 := (real_inner_comm (y 0) (y 4)).trans e04
  have e05 := hip0 5 (by decide) h05
  have e50 := (real_inner_comm (y 0) (y 5)).trans e05
  have e12 := hipS 1 2 (by decide) (by decide) h12
  have e21 := (real_inner_comm (y 1) (y 2)).trans e12
  have e14 := hipS 1 4 (by decide) (by decide) h14
  have e41 := (real_inner_comm (y 1) (y 4)).trans e14
  have e15 := hipS 1 5 (by decide) (by decide) h15
  have e51 := (real_inner_comm (y 1) (y 5)).trans e15
  have e23 := hipS 2 3 (by decide) (by decide) h23
  have e32 := (real_inner_comm (y 2) (y 3)).trans e23
  have e25 := hipS 2 5 (by decide) (by decide) h25
  have e52 := (real_inner_comm (y 2) (y 5)).trans e25
  have e34 := hipS 3 4 (by decide) (by decide) h34
  have e43 := (real_inner_comm (y 3) (y 4)).trans e34
  have s10 := real_inner_comm (y 0) (y 1)
  have s20 := real_inner_comm (y 0) (y 2)
  have s31 := real_inner_comm (y 1) (y 3)
  have s42 := real_inner_comm (y 2) (y 4)
  have s53 := real_inner_comm (y 3) (y 5)
  have s54 := real_inner_comm (y 4) (y 5)
  -- the Möbius relation on `(a, b)`
  have hF : (inner ℝ (y 1) (y 3) : ℝ) * inner ℝ (y 2) (y 4)
      + inner ℝ (y 1) (y 3) + inner ℝ (y 2) (y 4) = 0 := by
    have hd := gram_det_zero ![y 1, y 2, y 3, y 4]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself1, hself2, hself3, hself4, e12, e21, e14, e41, e23, e32, e34, e43,
      s31, s42] at hd
    have hfact : ((inner ℝ (y 1) (y 3) : ℝ) - 1) * ((inner ℝ (y 2) (y 4) : ℝ) - 1)
        * ((inner ℝ (y 1) (y 3) : ℝ) * inner ℝ (y 2) (y 4)
          + inner ℝ (y 1) (y 3) + inner ℝ (y 2) (y 4)) = 0 := by
      linear_combination hd
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso
      rcases mul_eq_zero.mp h with h' | h'
      · have := hleS 1 3 (by decide) (by decide) (by decide); linarith
      · have := hleS 2 4 (by decide) (by decide) (by decide); linarith
    · exact h
  have hba1 : -(1/3) ≤ (inner ℝ (y 1) (y 3) : ℝ) :=
    F_box hF (hgeS 1 3 (by decide) (by decide))
      (hleS 2 4 (by decide) (by decide) (by decide))
  have hbb1 : -(1/3) ≤ (inner ℝ (y 2) (y 4) : ℝ) :=
    F_box (by linear_combination hF) (hgeS 2 4 (by decide) (by decide))
      (hleS 1 3 (by decide) (by decide) (by decide))
  -- the two ellipses
  have hQ1 : 12 * (inner ℝ (y 1) (y 3) : ℝ)^2
      - 8 * inner ℝ (y 1) (y 3) * inner ℝ (y 3) (y 5) - 4 * inner ℝ (y 1) (y 3)
      + 12 * (inner ℝ (y 3) (y 5) : ℝ)^2 - 4 * inner ℝ (y 3) (y 5) - 5 = 0 := by
    have hd := gram_det_zero ![y 1, y 2, y 3, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself1, hself2, hself3, hself5, e12, e21, e15, e51, e23, e32, e25, e52,
      s31, s53] at hd
    linear_combination (-16 : ℝ) * hd
  have hQ2 : 12 * (inner ℝ (y 2) (y 4) : ℝ)^2
      - 8 * inner ℝ (y 2) (y 4) * inner ℝ (y 4) (y 5) - 4 * inner ℝ (y 2) (y 4)
      + 12 * (inner ℝ (y 4) (y 5) : ℝ)^2 - 4 * inner ℝ (y 4) (y 5) - 5 = 0 := by
    have hd := gram_det_zero ![y 1, y 2, y 4, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself1, hself2, hself4, hself5, e12, e21, e14, e41, e15, e51, e25, e52,
      s42, s54] at hd
    linear_combination (-16 : ℝ) * hd
  -- the `y₀` brackets
  have hbr8 : 4 * (inner ℝ (y 0) (y 0) : ℝ) * (inner ℝ (y 3) (y 5) : ℝ)^2
      - 8 * inner ℝ (y 0) (y 0) * inner ℝ (y 3) (y 5) * inner ℝ (y 4) (y 5)
      + 4 * inner ℝ (y 0) (y 0) * inner ℝ (y 3) (y 5)
      + 4 * inner ℝ (y 0) (y 0) * (inner ℝ (y 4) (y 5) : ℝ)^2
      + 4 * inner ℝ (y 0) (y 0) * inner ℝ (y 4) (y 5)
      - 7 * inner ℝ (y 0) (y 0) - 16 * (inner ℝ (y 3) (y 5) : ℝ)^2
      + 16 * inner ℝ (y 3) (y 5) * inner ℝ (y 4) (y 5)
      - 16 * (inner ℝ (y 4) (y 5) : ℝ)^2 + 12 = 0 := by
    have hd := gram_det_zero ![y 0, y 3, y 4, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself3, hself4, hself5, e03, e30, e04, e40, e05, e50, e34, e43,
      s53, s54] at hd
    have hfact : (inner ℝ (y 0) (y 0) : ℝ) *
        (4 * inner ℝ (y 0) (y 0) * (inner ℝ (y 3) (y 5) : ℝ)^2
          - 8 * inner ℝ (y 0) (y 0) * inner ℝ (y 3) (y 5) * inner ℝ (y 4) (y 5)
          + 4 * inner ℝ (y 0) (y 0) * inner ℝ (y 3) (y 5)
          + 4 * inner ℝ (y 0) (y 0) * (inner ℝ (y 4) (y 5) : ℝ)^2
          + 4 * inner ℝ (y 0) (y 0) * inner ℝ (y 4) (y 5)
          - 7 * inner ℝ (y 0) (y 0) - 16 * (inner ℝ (y 3) (y 5) : ℝ)^2
          + 16 * inner ℝ (y 3) (y 5) * inner ℝ (y 4) (y 5)
          - 16 * (inner ℝ (y 4) (y 5) : ℝ)^2 + 12) = 0 := by
      linear_combination (16 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso; linarith
    · exact h
  have hB1 : (inner ℝ (y 0) (y 0) : ℝ)^2
      - 2 * inner ℝ (y 0) (y 0) * inner ℝ (y 0) (y 1)
      - 2 * inner ℝ (y 0) (y 0) * inner ℝ (y 4) (y 5) - inner ℝ (y 0) (y 0)
      + 2 * (inner ℝ (y 0) (y 1) : ℝ)^2 * (inner ℝ (y 4) (y 5) + 1) = 0 := by
    have hd := gram_det_zero ![y 0, y 1, y 4, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself1, hself4, hself5, e04, e40, e05, e50, e14, e41, e15, e51,
      s10, s54] at hd
    have hfact : ((inner ℝ (y 4) (y 5) : ℝ) - 1) *
        ((inner ℝ (y 0) (y 0) : ℝ)^2
          - 2 * inner ℝ (y 0) (y 0) * inner ℝ (y 0) (y 1)
          - 2 * inner ℝ (y 0) (y 0) * inner ℝ (y 4) (y 5) - inner ℝ (y 0) (y 0)
          + 2 * (inner ℝ (y 0) (y 1) : ℝ)^2 * (inner ℝ (y 4) (y 5) + 1)) = 0 := by
      linear_combination (2 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso
      have := hleS 4 5 (by decide) (by decide) (by decide)
      linarith
    · exact h
  have hB2 : (inner ℝ (y 0) (y 0) : ℝ)^2
      - 2 * inner ℝ (y 0) (y 0) * inner ℝ (y 0) (y 2)
      - 2 * inner ℝ (y 0) (y 0) * inner ℝ (y 3) (y 5) - inner ℝ (y 0) (y 0)
      + 2 * (inner ℝ (y 0) (y 2) : ℝ)^2 * (inner ℝ (y 3) (y 5) + 1) = 0 := by
    have hd := gram_det_zero ![y 0, y 2, y 3, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself2, hself3, hself5, e03, e30, e05, e50, e23, e32, e25, e52,
      s20, s53] at hd
    have hfact : ((inner ℝ (y 3) (y 5) : ℝ) - 1) *
        ((inner ℝ (y 0) (y 0) : ℝ)^2
          - 2 * inner ℝ (y 0) (y 0) * inner ℝ (y 0) (y 2)
          - 2 * inner ℝ (y 0) (y 0) * inner ℝ (y 3) (y 5) - inner ℝ (y 0) (y 0)
          + 2 * (inner ℝ (y 0) (y 2) : ℝ)^2 * (inner ℝ (y 3) (y 5) + 1)) = 0 := by
      linear_combination (2 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · exfalso
      have := hleS 3 5 (by decide) (by decide) (by decide)
      linarith
    · exact h
  -- the two killer determinants, upfront
  have hK1 : -3 * (inner ℝ (y 0) (y 0) : ℝ)^2
      - 16 * inner ℝ (y 0) (y 0) * (inner ℝ (y 1) (y 3) : ℝ)^2
      + 16 * inner ℝ (y 0) (y 0) * inner ℝ (y 1) (y 3) * inner ℝ (y 0) (y 1)
      - 8 * inner ℝ (y 0) (y 0) * inner ℝ (y 1) (y 3) * inner ℝ (y 0) (y 2)
      + 8 * inner ℝ (y 0) (y 0) * inner ℝ (y 1) (y 3)
      - 4 * inner ℝ (y 0) (y 0) * inner ℝ (y 0) (y 1)
      + 8 * inner ℝ (y 0) (y 0) * inner ℝ (y 0) (y 2) + 8 * inner ℝ (y 0) (y 0)
      + 16 * (inner ℝ (y 1) (y 3) : ℝ)^2 * (inner ℝ (y 0) (y 2) : ℝ)^2
      - 16 * inner ℝ (y 1) (y 3) * inner ℝ (y 0) (y 1) * inner ℝ (y 0) (y 2)
      - 12 * (inner ℝ (y 0) (y 1) : ℝ)^2
      + 16 * inner ℝ (y 0) (y 1) * inner ℝ (y 0) (y 2)
      - 16 * (inner ℝ (y 0) (y 2) : ℝ)^2 = 0 := by
    have hd := gram_det_zero ![y 0, y 1, y 2, y 3]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself1, hself2, hself3, e03, e30, e12, e21, e23, e32, s10, s20, s31] at hd
    linear_combination (16 : ℝ) * hd
  have hK2 : -3 * (inner ℝ (y 0) (y 0) : ℝ)^2
      - 16 * inner ℝ (y 0) (y 0) * (inner ℝ (y 2) (y 4) : ℝ)^2
      - 8 * inner ℝ (y 0) (y 0) * inner ℝ (y 2) (y 4) * inner ℝ (y 0) (y 1)
      + 16 * inner ℝ (y 0) (y 0) * inner ℝ (y 2) (y 4) * inner ℝ (y 0) (y 2)
      + 8 * inner ℝ (y 0) (y 0) * inner ℝ (y 2) (y 4)
      + 8 * inner ℝ (y 0) (y 0) * inner ℝ (y 0) (y 1)
      - 4 * inner ℝ (y 0) (y 0) * inner ℝ (y 0) (y 2) + 8 * inner ℝ (y 0) (y 0)
      + 16 * (inner ℝ (y 2) (y 4) : ℝ)^2 * (inner ℝ (y 0) (y 1) : ℝ)^2
      - 16 * inner ℝ (y 2) (y 4) * inner ℝ (y 0) (y 1) * inner ℝ (y 0) (y 2)
      - 16 * (inner ℝ (y 0) (y 1) : ℝ)^2
      + 16 * inner ℝ (y 0) (y 1) * inner ℝ (y 0) (y 2)
      - 12 * (inner ℝ (y 0) (y 2) : ℝ)^2 = 0 := by
    have hd := gram_det_zero ![y 0, y 1, y 2, y 4]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three
      ] at hd
    rw [hself1, hself2, hself4, e04, e40, e12, e21, e14, e41, s10, s20, s42] at hd
    linear_combination (16 : ℝ) * hd
  exact p5_scalar hR1 hp1 hp2
    hba1 (hleS 1 3 (by decide) (by decide) (by decide))
    hbb1 (hleS 2 4 (by decide) (by decide) (by decide))
    (hgeS 3 5 (by decide) (by decide)) (hleS 3 5 (by decide) (by decide) (by decide))
    (hgeS 4 5 (by decide) (by decide)) (hleS 4 5 (by decide) (by decide) (by decide))
    hF hQ1 hQ2 hbr8 hB1 hB2 hK1 hK2

end Kissing3D
