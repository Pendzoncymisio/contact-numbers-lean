import ContactNumbers.Emin9Q28Tree
import ContactNumbers.Emin9Kills

set_option linter.style.header false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! # IBP kill lemma: 8-point pattern q28 (kills classes [29, 38])

The eight points carry the contact graph
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 7), (1, 2), (1, 3), (1, 5), (1, 7), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (4, 6), (5, 6), (6, 7)]
and the remaining pair distances are confined to [1, 2].  Every point of
the resulting box violates either a rank-3 Gram determinant identity or a
Gram minor nonnegativity, so no such configuration embeds in E3. -/

namespace Kissing3D

open IBP

theorem pattern_q28_impossible {X : Finset E3} (hX : HardCore X)
    {q : Fin 8 → E3} (hq : ∀ i, q i ∈ X) (hinj : Function.Injective q)
    (h01 : dist (q 0) (q 1) = 1)
    (h02 : dist (q 0) (q 2) = 1)
    (h03 : dist (q 0) (q 3) = 1)
    (h04 : dist (q 0) (q 4) = 1)
    (h07 : dist (q 0) (q 7) = 1)
    (h12 : dist (q 1) (q 2) = 1)
    (h13 : dist (q 1) (q 3) = 1)
    (h15 : dist (q 1) (q 5) = 1)
    (h17 : dist (q 1) (q 7) = 1)
    (h24 : dist (q 2) (q 4) = 1)
    (h25 : dist (q 2) (q 5) = 1)
    (h26 : dist (q 2) (q 6) = 1)
    (h34 : dist (q 3) (q 4) = 1)
    (h35 : dist (q 3) (q 5) = 1)
    (h46 : dist (q 4) (q 6) = 1)
    (h56 : dist (q 5) (q 6) = 1)
    (h67 : dist (q 6) (q 7) = 1)
    : False := by
  set y : Fin 8 → E3 := fun i => q i - q 0 with hy
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
  have hnrm : ∀ i, ‖y i‖ = dist (q i) (q 0) := by
    intro i
    simp only [hy]
    rw [← dist_eq_norm]
  set s05 : ℝ := dist (q 0) (q 5) ^ 2 with hs05def
  set s06 : ℝ := dist (q 0) (q 6) ^ 2 with hs06def
  set s14 : ℝ := dist (q 1) (q 4) ^ 2 with hs14def
  set s16 : ℝ := dist (q 1) (q 6) ^ 2 with hs16def
  set s23 : ℝ := dist (q 2) (q 3) ^ 2 with hs23def
  set s27 : ℝ := dist (q 2) (q 7) ^ 2 with hs27def
  set s36 : ℝ := dist (q 3) (q 6) ^ 2 with hs36def
  set s37 : ℝ := dist (q 3) (q 7) ^ 2 with hs37def
  set s45 : ℝ := dist (q 4) (q 5) ^ 2 with hs45def
  set s47 : ℝ := dist (q 4) (q 7) ^ 2 with hs47def
  set s57 : ℝ := dist (q 5) (q 7) ^ 2 with hs57def
  have hN1 : ‖y 1‖ ^ 2 = (1 : ℝ) := by
    rw [hnrm, dist_comm, h01]; norm_num
  have hN2 : ‖y 2‖ ^ 2 = (1 : ℝ) := by
    rw [hnrm, dist_comm, h02]; norm_num
  have hN3 : ‖y 3‖ ^ 2 = (1 : ℝ) := by
    rw [hnrm, dist_comm, h03]; norm_num
  have hN4 : ‖y 4‖ ^ 2 = (1 : ℝ) := by
    rw [hnrm, dist_comm, h04]; norm_num
  have hN5 : ‖y 5‖ ^ 2 = s05 := by
    rw [hnrm, dist_comm, ← hs05def]
  have hN6 : ‖y 6‖ ^ 2 = s06 := by
    rw [hnrm, dist_comm, ← hs06def]
  have hN7 : ‖y 7‖ ^ 2 = (1 : ℝ) := by
    rw [hnrm, dist_comm, h07]; norm_num
  have hs1 : (inner ℝ (y 1) (y 1) : ℝ) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hN1]
  have hs2 : (inner ℝ (y 2) (y 2) : ℝ) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hN2]
  have hs3 : (inner ℝ (y 3) (y 3) : ℝ) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hN3]
  have hs4 : (inner ℝ (y 4) (y 4) : ℝ) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hN4]
  have hs5 : (inner ℝ (y 5) (y 5) : ℝ) = s05 := by
    rw [real_inner_self_eq_norm_sq, hN5]
  have hs6 : (inner ℝ (y 6) (y 6) : ℝ) = s06 := by
    rw [real_inner_self_eq_norm_sq, hN6]
  have hs7 : (inner ℝ (y 7) (y 7) : ℝ) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hN7]
  have e12 : (inner ℝ (y 1) (y 2) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [hipgen, hN1, hN2, h12]; ring
  have e21 : (inner ℝ (y 2) (y 1) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e12
  have e13 : (inner ℝ (y 1) (y 3) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [hipgen, hN1, hN3, h13]; ring
  have e31 : (inner ℝ (y 3) (y 1) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e13
  have e14 : (inner ℝ (y 1) (y 4) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s14) / 2 := by
    rw [hipgen, hN1, hN4, ← hs14def]
  have e41 : (inner ℝ (y 4) (y 1) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s14) / 2 := by
    rw [real_inner_comm]; exact e14
  have e15 : (inner ℝ (y 1) (y 5) : ℝ) = ((1 : ℝ) + s05 - (1 : ℝ)) / 2 := by
    rw [hipgen, hN1, hN5, h15]; ring
  have e51 : (inner ℝ (y 5) (y 1) : ℝ) = ((1 : ℝ) + s05 - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e15
  have e16 : (inner ℝ (y 1) (y 6) : ℝ) = ((1 : ℝ) + s06 - s16) / 2 := by
    rw [hipgen, hN1, hN6, ← hs16def]
  have e61 : (inner ℝ (y 6) (y 1) : ℝ) = ((1 : ℝ) + s06 - s16) / 2 := by
    rw [real_inner_comm]; exact e16
  have e17 : (inner ℝ (y 1) (y 7) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [hipgen, hN1, hN7, h17]; ring
  have e71 : (inner ℝ (y 7) (y 1) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e17
  have e23 : (inner ℝ (y 2) (y 3) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s23) / 2 := by
    rw [hipgen, hN2, hN3, ← hs23def]
  have e32 : (inner ℝ (y 3) (y 2) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s23) / 2 := by
    rw [real_inner_comm]; exact e23
  have e24 : (inner ℝ (y 2) (y 4) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [hipgen, hN2, hN4, h24]; ring
  have e42 : (inner ℝ (y 4) (y 2) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e24
  have e25 : (inner ℝ (y 2) (y 5) : ℝ) = ((1 : ℝ) + s05 - (1 : ℝ)) / 2 := by
    rw [hipgen, hN2, hN5, h25]; ring
  have e52 : (inner ℝ (y 5) (y 2) : ℝ) = ((1 : ℝ) + s05 - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e25
  have e26 : (inner ℝ (y 2) (y 6) : ℝ) = ((1 : ℝ) + s06 - (1 : ℝ)) / 2 := by
    rw [hipgen, hN2, hN6, h26]; ring
  have e62 : (inner ℝ (y 6) (y 2) : ℝ) = ((1 : ℝ) + s06 - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e26
  have e27 : (inner ℝ (y 2) (y 7) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s27) / 2 := by
    rw [hipgen, hN2, hN7, ← hs27def]
  have e72 : (inner ℝ (y 7) (y 2) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s27) / 2 := by
    rw [real_inner_comm]; exact e27
  have e34 : (inner ℝ (y 3) (y 4) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [hipgen, hN3, hN4, h34]; ring
  have e43 : (inner ℝ (y 4) (y 3) : ℝ) = ((1 : ℝ) + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e34
  have e35 : (inner ℝ (y 3) (y 5) : ℝ) = ((1 : ℝ) + s05 - (1 : ℝ)) / 2 := by
    rw [hipgen, hN3, hN5, h35]; ring
  have e53 : (inner ℝ (y 5) (y 3) : ℝ) = ((1 : ℝ) + s05 - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e35
  have e36 : (inner ℝ (y 3) (y 6) : ℝ) = ((1 : ℝ) + s06 - s36) / 2 := by
    rw [hipgen, hN3, hN6, ← hs36def]
  have e63 : (inner ℝ (y 6) (y 3) : ℝ) = ((1 : ℝ) + s06 - s36) / 2 := by
    rw [real_inner_comm]; exact e36
  have e37 : (inner ℝ (y 3) (y 7) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s37) / 2 := by
    rw [hipgen, hN3, hN7, ← hs37def]
  have e73 : (inner ℝ (y 7) (y 3) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s37) / 2 := by
    rw [real_inner_comm]; exact e37
  have e45 : (inner ℝ (y 4) (y 5) : ℝ) = ((1 : ℝ) + s05 - s45) / 2 := by
    rw [hipgen, hN4, hN5, ← hs45def]
  have e54 : (inner ℝ (y 5) (y 4) : ℝ) = ((1 : ℝ) + s05 - s45) / 2 := by
    rw [real_inner_comm]; exact e45
  have e46 : (inner ℝ (y 4) (y 6) : ℝ) = ((1 : ℝ) + s06 - (1 : ℝ)) / 2 := by
    rw [hipgen, hN4, hN6, h46]; ring
  have e64 : (inner ℝ (y 6) (y 4) : ℝ) = ((1 : ℝ) + s06 - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e46
  have e47 : (inner ℝ (y 4) (y 7) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s47) / 2 := by
    rw [hipgen, hN4, hN7, ← hs47def]
  have e74 : (inner ℝ (y 7) (y 4) : ℝ) = ((1 : ℝ) + (1 : ℝ) - s47) / 2 := by
    rw [real_inner_comm]; exact e47
  have e56 : (inner ℝ (y 5) (y 6) : ℝ) = (s05 + s06 - (1 : ℝ)) / 2 := by
    rw [hipgen, hN5, hN6, h56]; ring
  have e65 : (inner ℝ (y 6) (y 5) : ℝ) = (s05 + s06 - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e56
  have e57 : (inner ℝ (y 5) (y 7) : ℝ) = (s05 + (1 : ℝ) - s57) / 2 := by
    rw [hipgen, hN5, hN7, ← hs57def]
  have e75 : (inner ℝ (y 7) (y 5) : ℝ) = (s05 + (1 : ℝ) - s57) / 2 := by
    rw [real_inner_comm]; exact e57
  have e67 : (inner ℝ (y 6) (y 7) : ℝ) = (s06 + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [hipgen, hN6, hN7, h67]; ring
  have e76 : (inner ℝ (y 7) (y 6) : ℝ) = (s06 + (1 : ℝ) - (1 : ℝ)) / 2 := by
    rw [real_inner_comm]; exact e67
  have hlo_s05 : (1 : ℝ) ≤ s05 := by
    have hs := hsep 0 5 (by decide)
    rw [hs05def]; linarith only [hs]
  have hhi_s05 : s05 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 0) (q 1) (q 5)
    have hb1 : dist (q 0) (q 1) = 1 := by
      exact h01
    have hb2 : dist (q 1) (q 5) = 1 := by
      exact h15
    rw [hs05def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 0) (y := q 5)]
  have hlo_s06 : (1 : ℝ) ≤ s06 := by
    have hs := hsep 0 6 (by decide)
    rw [hs06def]; linarith only [hs]
  have hhi_s06 : s06 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 0) (q 2) (q 6)
    have hb1 : dist (q 0) (q 2) = 1 := by
      exact h02
    have hb2 : dist (q 2) (q 6) = 1 := by
      exact h26
    rw [hs06def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 0) (y := q 6)]
  have hlo_s14 : (1 : ℝ) ≤ s14 := by
    have hs := hsep 1 4 (by decide)
    rw [hs14def]; linarith only [hs]
  have hhi_s14 : s14 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 1) (q 0) (q 4)
    have hb1 : dist (q 1) (q 0) = 1 := by
      rw [dist_comm]; exact h01
    have hb2 : dist (q 0) (q 4) = 1 := by
      exact h04
    rw [hs14def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 1) (y := q 4)]
  have hlo_s16 : (1 : ℝ) ≤ s16 := by
    have hs := hsep 1 6 (by decide)
    rw [hs16def]; linarith only [hs]
  have hhi_s16 : s16 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 1) (q 2) (q 6)
    have hb1 : dist (q 1) (q 2) = 1 := by
      exact h12
    have hb2 : dist (q 2) (q 6) = 1 := by
      exact h26
    rw [hs16def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 1) (y := q 6)]
  have hlo_s23 : (1 : ℝ) ≤ s23 := by
    have hs := hsep 2 3 (by decide)
    rw [hs23def]; linarith only [hs]
  have hhi_s23 : s23 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 2) (q 0) (q 3)
    have hb1 : dist (q 2) (q 0) = 1 := by
      rw [dist_comm]; exact h02
    have hb2 : dist (q 0) (q 3) = 1 := by
      exact h03
    rw [hs23def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 2) (y := q 3)]
  have hlo_s27 : (1 : ℝ) ≤ s27 := by
    have hs := hsep 2 7 (by decide)
    rw [hs27def]; linarith only [hs]
  have hhi_s27 : s27 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 2) (q 0) (q 7)
    have hb1 : dist (q 2) (q 0) = 1 := by
      rw [dist_comm]; exact h02
    have hb2 : dist (q 0) (q 7) = 1 := by
      exact h07
    rw [hs27def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 2) (y := q 7)]
  have hlo_s36 : (1 : ℝ) ≤ s36 := by
    have hs := hsep 3 6 (by decide)
    rw [hs36def]; linarith only [hs]
  have hhi_s36 : s36 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 3) (q 4) (q 6)
    have hb1 : dist (q 3) (q 4) = 1 := by
      exact h34
    have hb2 : dist (q 4) (q 6) = 1 := by
      exact h46
    rw [hs36def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 3) (y := q 6)]
  have hlo_s37 : (1 : ℝ) ≤ s37 := by
    have hs := hsep 3 7 (by decide)
    rw [hs37def]; linarith only [hs]
  have hhi_s37 : s37 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 3) (q 0) (q 7)
    have hb1 : dist (q 3) (q 0) = 1 := by
      rw [dist_comm]; exact h03
    have hb2 : dist (q 0) (q 7) = 1 := by
      exact h07
    rw [hs37def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 3) (y := q 7)]
  have hlo_s45 : (1 : ℝ) ≤ s45 := by
    have hs := hsep 4 5 (by decide)
    rw [hs45def]; linarith only [hs]
  have hhi_s45 : s45 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 4) (q 2) (q 5)
    have hb1 : dist (q 4) (q 2) = 1 := by
      rw [dist_comm]; exact h24
    have hb2 : dist (q 2) (q 5) = 1 := by
      exact h25
    rw [hs45def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 4) (y := q 5)]
  have hlo_s47 : (1 : ℝ) ≤ s47 := by
    have hs := hsep 4 7 (by decide)
    rw [hs47def]; linarith only [hs]
  have hhi_s47 : s47 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 4) (q 0) (q 7)
    have hb1 : dist (q 4) (q 0) = 1 := by
      rw [dist_comm]; exact h04
    have hb2 : dist (q 0) (q 7) = 1 := by
      exact h07
    rw [hs47def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 4) (y := q 7)]
  have hlo_s57 : (1 : ℝ) ≤ s57 := by
    have hs := hsep 5 7 (by decide)
    rw [hs57def]; linarith only [hs]
  have hhi_s57 : s57 ≤ (4 : ℝ) := by
    have htri := dist_triangle (q 5) (q 1) (q 7)
    have hb1 : dist (q 5) (q 1) = 1 := by
      rw [dist_comm]; exact h15
    have hb2 : dist (q 1) (q 7) = 1 := by
      exact h17
    rw [hs57def]
    nlinarith only [htri, hb1, hb2, dist_nonneg (x := q 5) (y := q 7)]
  have hd0 : evalPoly [(((1 : ℚ) / 16), [0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 3, y 4]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e13, e14, e21, hs2, e23, e24, e31, e32, hs3, e34, e41, e42, e43, hs4] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd1 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 3, y 5]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e13, e15, e21, hs2, e23, e25, e31, e32, hs3, e35, e51, e52, e53, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd2 : evalPoly [(((1 : ℚ) / 16), [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 3, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e13, e16, e21, hs2, e23, e26, e31, e32, hs3, e36, e61, e62, e63, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd3 : evalPoly [(((-3 : ℚ) / 16), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 3, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e13, e17, e21, hs2, e23, e27, e31, e32, hs3, e37, e71, e72, e73, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd4 : evalPoly [(((1 : ℚ) / 16), [2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]), (((5 : ℚ) / 8), [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 4, y 5]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e14, e15, e21, hs2, e24, e25, e41, e42, hs4, e45, e51, e52, e54, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd5 : evalPoly [(((1 : ℚ) / 16), [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (((5 : ℚ) / 8), [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 4, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e14, e16, e21, hs2, e24, e26, e41, e42, hs4, e46, e61, e62, e64, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd6 : evalPoly [(((1 : ℚ) / 16), [0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0]), (((5 : ℚ) / 8), [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 4, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e14, e17, e21, hs2, e24, e27, e41, e42, hs4, e47, e71, e72, e74, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd7 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((5 : ℚ) / 8), [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 5, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e15, e16, e21, hs2, e25, e26, e51, e52, hs5, e56, e61, e62, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd8 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (((5 : ℚ) / 8), [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 5, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e15, e17, e21, hs2, e25, e27, e51, e52, hs5, e57, e71, e72, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd9 : evalPoly [(((1 : ℚ) / 16), [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 2, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e12, e16, e17, e21, hs2, e26, e27, e61, e62, hs6, e67, e71, e72, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd10 : evalPoly [(((1 : ℚ) / 16), [2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]), (((5 : ℚ) / 8), [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 3, y 4, y 5]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e13, e14, e15, e31, hs3, e34, e35, e41, e43, hs4, e45, e51, e53, e54, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd11 : evalPoly [(((1 : ℚ) / 16), [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 3, y 4, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e13, e14, e16, e31, hs3, e34, e36, e41, e43, hs4, e46, e61, e63, e64, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd12 : evalPoly [(((1 : ℚ) / 16), [0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0]), (((5 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 3, y 4, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e13, e14, e17, e31, hs3, e34, e37, e41, e43, hs4, e47, e71, e73, e74, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd13 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0]), (((3 : ℚ) / 8), [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((3 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 3, y 5, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e13, e15, e16, e31, hs3, e35, e36, e51, e53, hs5, e56, e61, e63, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd14 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]), (((5 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 3, y 5, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e13, e15, e17, e31, hs3, e35, e37, e51, e53, hs5, e57, e71, e73, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd15 : evalPoly [(((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((3 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 3, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e13, e16, e17, e31, hs3, e36, e37, e61, e63, hs6, e67, e71, e73, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd16 : evalPoly [(((1 : ℚ) / 16), [2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 2), [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-3 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-3 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 8), [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]), (((-3 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]), (((-3 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((-3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((5 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 4, y 5, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e14, e15, e16, e41, hs4, e45, e46, e51, e54, hs5, e56, e61, e64, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd17 : evalPoly [(((1 : ℚ) / 16), [2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 8), [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1]), (((1 : ℚ) / 8), [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 8), [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 4), [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((3 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2]), (((-1 : ℚ) / 8), [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1]), (((-1 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2]), (((3 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]), (((1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 4, y 5, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e14, e15, e17, e41, hs4, e45, e47, e51, e54, hs5, e57, e71, e74, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd18 : evalPoly [(((1 : ℚ) / 16), [0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 8), [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 2), [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 8), [0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((3 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 2), [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 4, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e14, e16, e17, e41, hs4, e46, e47, e61, e64, hs6, e67, e71, e74, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd19 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 2), [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 8), [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2]), (((-1 : ℚ) / 8), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2]), (((3 : ℚ) / 8), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 1, y 5, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs1, e15, e16, e17, e51, hs5, e56, e57, e61, e65, hs6, e67, e71, e75, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd20 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 3, y 4, y 5]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e23, e24, e25, e32, hs3, e34, e35, e42, e43, hs4, e45, e52, e53, e54, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd21 : evalPoly [(((1 : ℚ) / 16), [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (((5 : ℚ) / 8), [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 3, y 4, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e23, e24, e26, e32, hs3, e34, e36, e42, e43, hs4, e46, e62, e63, e64, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd22 : evalPoly [(((1 : ℚ) / 16), [0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 3, y 4, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e23, e24, e27, e32, hs3, e34, e37, e42, e43, hs4, e47, e72, e73, e74, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd23 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (((3 : ℚ) / 8), [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 3, y 5, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e23, e25, e26, e32, hs3, e35, e36, e52, e53, hs5, e56, e62, e63, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd24 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1]), (((3 : ℚ) / 8), [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1]), (((3 : ℚ) / 8), [1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 2), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 3, y 5, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e23, e25, e27, e32, hs3, e35, e37, e52, e53, hs5, e57, e72, e73, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd25 : evalPoly [(((1 : ℚ) / 16), [0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]), (((3 : ℚ) / 8), [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0]), (((3 : ℚ) / 8), [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 3, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e23, e26, e27, e32, hs3, e36, e37, e62, e63, hs6, e67, e72, e73, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd26 : evalPoly [(((-3 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((3 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((5 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 4, y 5, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e24, e25, e26, e42, hs4, e45, e46, e52, e54, hs5, e56, e62, e64, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd27 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (((1 : ℚ) / 4), [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((3 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0]), (((1 : ℚ) / 8), [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 4, y 5, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e24, e25, e27, e42, hs4, e45, e47, e52, e54, hs5, e57, e72, e74, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd28 : evalPoly [(((1 : ℚ) / 16), [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 4, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e24, e26, e27, e42, hs4, e46, e47, e62, e64, hs6, e67, e72, e74, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd29 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (((3 : ℚ) / 8), [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 2, y 5, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs2, e25, e26, e27, e52, hs5, e56, e57, e62, e65, hs6, e67, e72, e75, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd30 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 3, y 4, y 5, y 6]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs3, e34, e35, e36, e43, hs4, e45, e46, e53, e54, hs5, e56, e63, e64, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd31 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]), (((1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((3 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0]), (((1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]), (((3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-3 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 3, y 4, y 5, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs3, e34, e35, e37, e43, hs4, e45, e47, e53, e54, hs5, e57, e73, e74, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd32 : evalPoly [(((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 0, 0, 2, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((3 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 3, y 4, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs3, e34, e36, e37, e43, hs4, e46, e47, e63, e64, hs6, e67, e73, e74, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd33 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 8), [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1]), (((-1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-3 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 2]), (((1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-3 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1]), (((1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (((-1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]), (((-3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]), (((-3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((-3 : ℚ) / 8), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((5 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 3, y 5, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs3, e35, e36, e37, e53, hs5, e56, e57, e63, e65, hs6, e67, e73, e75, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hd34 : evalPoly [(((1 : ℚ) / 16), [2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0]), (((-1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 8), [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((-1 : ℚ) / 8), [1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 1]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 8), [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((1 : ℚ) / 16), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1]), (((3 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1]), (((-1 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((3 : ℚ) / 8), [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 16), [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    have hg := gram_det_zero ![y 4, y 5, y 6, y 7]
    rw [det_fin_four] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hg
    rw [hs4, e45, e46, e47, e54, hs5, e56, e57, e64, e65, hs6, e67, e74, e75, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    linear_combination hg
  have hm0 : 0 ≤ evalPoly [(((3 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 1) (y 2)
    rw [hs1, hs2, e12, e21] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm1 : 0 ≤ evalPoly [(((3 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 1) (y 3)
    rw [hs1, hs3, e13, e31] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm2 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), ((1 : ℚ), [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 1) (y 4)
    rw [hs1, hs4, e14, e41] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm3 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), ((1 : ℚ), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 1) (y 5)
    rw [hs1, hs5, e15, e51] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm4 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 1) (y 6)
    rw [hs1, hs6, e16, e61] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm5 : 0 ≤ evalPoly [(((3 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 1) (y 7)
    rw [hs1, hs7, e17, e71] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm6 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), ((1 : ℚ), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 2) (y 3)
    rw [hs2, hs3, e23, e32] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm7 : 0 ≤ evalPoly [(((3 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 2) (y 4)
    rw [hs2, hs4, e24, e42] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm8 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), ((1 : ℚ), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 2) (y 5)
    rw [hs2, hs5, e25, e52] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm9 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), ((1 : ℚ), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 2) (y 6)
    rw [hs2, hs6, e26, e62] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm10 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), ((1 : ℚ), [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 2) (y 7)
    rw [hs2, hs7, e27, e72] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm11 : 0 ≤ evalPoly [(((3 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 3) (y 4)
    rw [hs3, hs4, e34, e43] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm12 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), ((1 : ℚ), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 3) (y 5)
    rw [hs3, hs5, e35, e53] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm13 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 3) (y 6)
    rw [hs3, hs6, e36, e63] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm14 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), ((1 : ℚ), [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 3) (y 7)
    rw [hs3, hs7, e37, e73] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm15 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 4) (y 5)
    rw [hs4, hs5, e45, e54] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm16 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), ((1 : ℚ), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 4) (y 6)
    rw [hs4, hs6, e46, e64] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm17 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), ((1 : ℚ), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 4) (y 7)
    rw [hs4, hs7, e47, e74] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm18 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 5) (y 6)
    rw [hs5, hs6, e56, e65] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm19 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 5) (y 7)
    rw [hs5, hs7, e57, e75] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm20 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), ((1 : ℚ), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram2_det_nonneg (y 6) (y 7)
    rw [hs6, hs7, e67, e76] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm21 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 2, y 3]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e12, e13, e21, hs2, e23, e31, e32, hs3] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm22 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 2, y 4]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e12, e14, e21, hs2, e24, e41, e42, hs4] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm23 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 2, y 5]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e12, e15, e21, hs2, e25, e51, e52, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm24 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 2, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e12, e16, e21, hs2, e26, e61, e62, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm25 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 2, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e12, e17, e21, hs2, e27, e71, e72, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm26 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 3, y 4]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e13, e14, e31, hs3, e34, e41, e43, hs4] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm27 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 3, y 5]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e13, e15, e31, hs3, e35, e51, e53, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm28 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 3, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e13, e16, e31, hs3, e36, e61, e63, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm29 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((3 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 3, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e13, e17, e31, hs3, e37, e71, e73, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm30 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]), (((3 : ℚ) / 4), [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 4, y 5]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e14, e15, e41, hs4, e45, e51, e54, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm31 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 4, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e14, e16, e41, hs4, e46, e61, e64, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm32 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 2), [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 4, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e14, e17, e41, hs4, e47, e71, e74, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm33 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 5, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e15, e16, e51, hs5, e56, e61, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm34 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 5, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e15, e17, e51, hs5, e57, e71, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm35 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 1, y 6, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs1, e16, e17, e61, hs6, e67, e71, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm36 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 3, y 4]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e23, e24, e32, hs3, e34, e42, e43, hs4] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm37 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), ((1 : ℚ), [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 3, y 5]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e23, e25, e32, hs3, e35, e52, e53, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm38 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0]), (((3 : ℚ) / 4), [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 3, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e23, e26, e32, hs3, e36, e62, e63, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm39 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 3, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e23, e27, e32, hs3, e37, e72, e73, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm40 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 4, y 5]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e24, e25, e42, hs4, e45, e52, e54, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm41 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((3 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 4, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e24, e26, e42, hs4, e46, e62, e64, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm42 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 4, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e24, e27, e42, hs4, e47, e72, e74, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm43 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 5, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e25, e26, e52, hs5, e56, e62, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm44 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]), (((3 : ℚ) / 4), [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 5, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e25, e27, e52, hs5, e57, e72, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm45 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0]), ((1 : ℚ), [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 2, y 6, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs2, e26, e27, e62, hs6, e67, e72, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm46 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 3, y 4, y 5]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs3, e34, e35, e43, hs4, e45, e53, e54, hs5] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm47 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 3, y 4, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs3, e34, e36, e43, hs4, e46, e63, e64, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm48 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 3, y 4, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs3, e34, e37, e43, hs4, e47, e73, e74, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm49 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((3 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 3, y 5, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs3, e35, e36, e53, hs5, e56, e63, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm50 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]), (((3 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 3, y 5, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs3, e35, e37, e53, hs5, e57, e73, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm51 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0]), (((3 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 3, y 6, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs3, e36, e37, e63, hs6, e67, e73, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm52 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((3 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 4, y 5, y 6]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs4, e45, e46, e54, hs5, e56, e64, e65, hs6] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm53 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]), (((-1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]), (((1 : ℚ) / 4), [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]), (((1 : ℚ) / 2), [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]), (((1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 4, y 5, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs4, e45, e47, e54, hs5, e57, e74, e75, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm54 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0]), ((1 : ℚ), [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 4, y 6, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs4, e46, e47, e64, hs6, e67, e74, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hm55 : 0 ≤ evalPoly [(((-1 : ℚ) / 4), [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((1 : ℚ) / 4), [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((1 : ℚ) / 2), [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), (((-1 : ℚ) / 4), [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2]), (((3 : ℚ) / 4), [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]), (((-1 : ℚ) / 4), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    have hg := gram3_det_nonneg ![y 5, y 6, y 7]
    rw [Matrix.det_fin_three] at hg
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hg
    rw [hs5, e56, e57, e65, hs6, e67, e75, e76, hs7] at hg
    simp only [evalPoly_cons, evalPoly_nil, evalMono]
    convert hg using 1
    ring
  have hdets : ∀ P ∈ q28D, evalPoly P [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] = 0 := by
    intro P hP
    simp only [q28D, List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hd0
    · exact hd1
    · exact hd2
    · exact hd3
    · exact hd4
    · exact hd5
    · exact hd6
    · exact hd7
    · exact hd8
    · exact hd9
    · exact hd10
    · exact hd11
    · exact hd12
    · exact hd13
    · exact hd14
    · exact hd15
    · exact hd16
    · exact hd17
    · exact hd18
    · exact hd19
    · exact hd20
    · exact hd21
    · exact hd22
    · exact hd23
    · exact hd24
    · exact hd25
    · exact hd26
    · exact hd27
    · exact hd28
    · exact hd29
    · exact hd30
    · exact hd31
    · exact hd32
    · exact hd33
    · exact hd34
  have hminors : ∀ P ∈ q28M, 0 ≤ evalPoly P [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] := by
    intro P hP
    simp only [q28M, List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm0
    · exact hm1
    · exact hm2
    · exact hm3
    · exact hm4
    · exact hm5
    · exact hm6
    · exact hm7
    · exact hm8
    · exact hm9
    · exact hm10
    · exact hm11
    · exact hm12
    · exact hm13
    · exact hm14
    · exact hm15
    · exact hm16
    · exact hm17
    · exact hm18
    · exact hm19
    · exact hm20
    · exact hm21
    · exact hm22
    · exact hm23
    · exact hm24
    · exact hm25
    · exact hm26
    · exact hm27
    · exact hm28
    · exact hm29
    · exact hm30
    · exact hm31
    · exact hm32
    · exact hm33
    · exact hm34
    · exact hm35
    · exact hm36
    · exact hm37
    · exact hm38
    · exact hm39
    · exact hm40
    · exact hm41
    · exact hm42
    · exact hm43
    · exact hm44
    · exact hm45
    · exact hm46
    · exact hm47
    · exact hm48
    · exact hm49
    · exact hm50
    · exact hm51
    · exact hm52
    · exact hm53
    · exact hm54
    · exact hm55
  have harity : ∀ P ∈ q28D ++ q28M, ∀ p ∈ P, (p.2 : List ℕ).length = 11 := by decide +kernel
  have hbox : ∀ i, i < ([s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] : List ℝ).length →
      ((([(1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ)] : List ℚ).getD i 0 : ℚ) : ℝ) ≤ ([s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] : List ℝ).getD i 0 ∧
        ([s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] : List ℝ).getD i 0 ≤ (((([(1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ)] : List ℚ).getD i 0 + ([(3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ)] : List ℚ).getD i 0) : ℚ) : ℝ) := by
    intro i hi
    have hi' : i < 11 := by simpa using hi
    clear hi
    interval_cases i <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
      refine ⟨by push_cast; linarith [hlo_s05, hlo_s06, hlo_s14, hlo_s16, hlo_s23, hlo_s27, hlo_s36, hlo_s37, hlo_s45, hlo_s47, hlo_s57], by push_cast; linarith [hhi_s05, hhi_s06, hhi_s14, hhi_s16, hhi_s23, hhi_s27, hhi_s36, hhi_s37, hhi_s45, hhi_s47, hhi_s57]⟩
  have hwnn : ∀ x ∈ ([(3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ), (3 : ℚ)] : List ℚ), (0:ℚ) ≤ x := by decide
  exact IBP.ibpWalk_impossible q28D q28M [s05, s06, s14, s16, s23, s27, s36, s37, s45, s47, s57] hdets hminors harity
    _ _ _ _ _ q28tree rfl rfl hbox hwnn

end Kissing3D
