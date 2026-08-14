import ContactNumbers.Emin9Kills

set_option linter.style.header false
set_option maxHeartbeats 1600000

/-!
# Kill lemma for `E_min(9)` survivor class 23: the double-hub pattern

Class 23 is the unique nine-particle 22-bond survivor class with no proper
infeasible sub-pattern: two degree-7 hubs `q0, q1` bonded to each other, a
five-point ring `q2..q6` bonded to both hubs, and two cap points `q7` (bonded
to `q0, q2, q3, q8`) and `q8` (bonded to `q1, q2, q3, q7`).

The proof is a linear chain of Gram-determinant pins with **rational** values
(found by `scratch-h4/chain_finder.py`): the ring rigidifies as
`s26 = s36 = 8/3`, `s23 = 32/27`, `s34 = s25 = 25/9` (the ring has
`cos θ₀ = 1/3`), then the caps pin `s17 = s08 = 49/19`, and finally
`det G[y1,y2,y7,y8] = −1716715/2085136 ≠ 0` — contradiction with four vectors
in `ℝ³`. Every excluded root is `< 1`, killed by hard-core alone.
-/

namespace Kissing3D

/-- **Survivor class 23 is impossible**: no hard-core configuration contains
nine points with the 22-bond double-hub pattern. -/
theorem pattern_class23_impossible {X : Finset E3} (hX : HardCore X)
    {q : Fin 9 → E3} (hq : ∀ i, q i ∈ X) (hinj : Function.Injective q)
    (h01 : dist (q 0) (q 1) = 1) (h02 : dist (q 0) (q 2) = 1)
    (h03 : dist (q 0) (q 3) = 1) (h04 : dist (q 0) (q 4) = 1)
    (h05 : dist (q 0) (q 5) = 1) (h06 : dist (q 0) (q 6) = 1)
    (h07 : dist (q 0) (q 7) = 1) (h12 : dist (q 1) (q 2) = 1)
    (h13 : dist (q 1) (q 3) = 1) (h14 : dist (q 1) (q 4) = 1)
    (h15 : dist (q 1) (q 5) = 1) (h16 : dist (q 1) (q 6) = 1)
    (h18 : dist (q 1) (q 8) = 1) (h24 : dist (q 2) (q 4) = 1)
    (h27 : dist (q 2) (q 7) = 1) (h28 : dist (q 2) (q 8) = 1)
    (h35 : dist (q 3) (q 5) = 1) (h37 : dist (q 3) (q 7) = 1)
    (h38 : dist (q 3) (q 8) = 1) (h46 : dist (q 4) (q 6) = 1)
    (h56 : dist (q 5) (q 6) = 1) (h78 : dist (q 7) (q 8) = 1) : False := by
  set y : Fin 9 → E3 := fun i => q i - q 0 with hy
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
  have hn1 : ‖y 1‖ = 1 := by rw [hnrm, dist_comm]; exact h01
  have hn2 : ‖y 2‖ = 1 := by rw [hnrm, dist_comm]; exact h02
  have hn3 : ‖y 3‖ = 1 := by rw [hnrm, dist_comm]; exact h03
  have hn4 : ‖y 4‖ = 1 := by rw [hnrm, dist_comm]; exact h04
  have hn5 : ‖y 5‖ = 1 := by rw [hnrm, dist_comm]; exact h05
  have hn6 : ‖y 6‖ = 1 := by rw [hnrm, dist_comm]; exact h06
  have hn7 : ‖y 7‖ = 1 := by rw [hnrm, dist_comm]; exact h07
  -- unknown squared distances
  set s26 : ℝ := dist (q 2) (q 6) ^ 2 with hs26def
  set s36 : ℝ := dist (q 3) (q 6) ^ 2 with hs36def
  set s23 : ℝ := dist (q 2) (q 3) ^ 2 with hs23def
  set s34 : ℝ := dist (q 3) (q 4) ^ 2 with hs34def
  set s25 : ℝ := dist (q 2) (q 5) ^ 2 with hs25def
  set s17 : ℝ := dist (q 1) (q 7) ^ 2 with hs17def
  set s08 : ℝ := dist (q 0) (q 8) ^ 2 with hs08def
  have hge26 : 1 ≤ s26 := by rw [hs26def]; exact hsep 2 6 (by decide)
  have hge36 : 1 ≤ s36 := by rw [hs36def]; exact hsep 3 6 (by decide)
  have hge23 : 1 ≤ s23 := by rw [hs23def]; exact hsep 2 3 (by decide)
  have hge34 : 1 ≤ s34 := by rw [hs34def]; exact hsep 3 4 (by decide)
  have hge25 : 1 ≤ s25 := by rw [hs25def]; exact hsep 2 5 (by decide)
  have hge17 : 1 ≤ s17 := by rw [hs17def]; exact hsep 1 7 (by decide)
  have hge08 : 1 ≤ s08 := by rw [hs08def]; exact hsep 0 8 (by decide)
  -- self inner products
  have hs1 : (inner ℝ (y 1) (y 1) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn1]; norm_num
  have hs2 : (inner ℝ (y 2) (y 2) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn2]; norm_num
  have hs3 : (inner ℝ (y 3) (y 3) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn3]; norm_num
  have hs4 : (inner ℝ (y 4) (y 4) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn4]; norm_num
  have hs5 : (inner ℝ (y 5) (y 5) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn5]; norm_num
  have hs6 : (inner ℝ (y 6) (y 6) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn6]; norm_num
  have hs7 : (inner ℝ (y 7) (y 7) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn7]; norm_num
  have hs8 : (inner ℝ (y 8) (y 8) : ℝ) = s08 := by
    rw [real_inner_self_eq_norm_sq, hnrm, dist_comm (q 8) (q 0), hs08def]
  -- bonded cross inner products (both endpoints 0-adjacent): value 1/2
  have hev : ∀ i j : Fin 9, ‖y i‖ = 1 → ‖y j‖ = 1 → dist (q i) (q j) = 1 →
      (inner ℝ (y i) (y j) : ℝ) = 1 / 2 := by
    intro i j hni hnj hd
    rw [hipgen, hni, hnj, hd]; norm_num
  have e12 : (inner ℝ (y 1) (y 2) : ℝ) = 1 / 2 := hev 1 2 hn1 hn2 h12
  have e21 : (inner ℝ (y 2) (y 1) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e12
  have e13 : (inner ℝ (y 1) (y 3) : ℝ) = 1 / 2 := hev 1 3 hn1 hn3 h13
  have e31 : (inner ℝ (y 3) (y 1) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e13
  have e14 : (inner ℝ (y 1) (y 4) : ℝ) = 1 / 2 := hev 1 4 hn1 hn4 h14
  have e41 : (inner ℝ (y 4) (y 1) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e14
  have e15 : (inner ℝ (y 1) (y 5) : ℝ) = 1 / 2 := hev 1 5 hn1 hn5 h15
  have e51 : (inner ℝ (y 5) (y 1) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e15
  have e16 : (inner ℝ (y 1) (y 6) : ℝ) = 1 / 2 := hev 1 6 hn1 hn6 h16
  have e61 : (inner ℝ (y 6) (y 1) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e16
  have e24 : (inner ℝ (y 2) (y 4) : ℝ) = 1 / 2 := hev 2 4 hn2 hn4 h24
  have e42 : (inner ℝ (y 4) (y 2) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e24
  have e27 : (inner ℝ (y 2) (y 7) : ℝ) = 1 / 2 := hev 2 7 hn2 hn7 h27
  have e72 : (inner ℝ (y 7) (y 2) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e27
  have e35 : (inner ℝ (y 3) (y 5) : ℝ) = 1 / 2 := hev 3 5 hn3 hn5 h35
  have e53 : (inner ℝ (y 5) (y 3) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e35
  have e37 : (inner ℝ (y 3) (y 7) : ℝ) = 1 / 2 := hev 3 7 hn3 hn7 h37
  have e73 : (inner ℝ (y 7) (y 3) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e37
  have e46 : (inner ℝ (y 4) (y 6) : ℝ) = 1 / 2 := hev 4 6 hn4 hn6 h46
  have e64 : (inner ℝ (y 6) (y 4) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e46
  have e56 : (inner ℝ (y 5) (y 6) : ℝ) = 1 / 2 := hev 5 6 hn5 hn6 h56
  have e65 : (inner ℝ (y 6) (y 5) : ℝ) = 1 / 2 := by rw [real_inner_comm]; exact e56
  -- non-bonded cross inner products among unit vectors: 1 - s/2
  have e26 : (inner ℝ (y 2) (y 6) : ℝ) = 1 - s26 / 2 := by
    rw [hipgen, hn2, hn6, hs26def]; ring
  have e62 : (inner ℝ (y 6) (y 2) : ℝ) = 1 - s26 / 2 := by
    rw [real_inner_comm]; exact e26
  have e36 : (inner ℝ (y 3) (y 6) : ℝ) = 1 - s36 / 2 := by
    rw [hipgen, hn3, hn6, hs36def]; ring
  have e63 : (inner ℝ (y 6) (y 3) : ℝ) = 1 - s36 / 2 := by
    rw [real_inner_comm]; exact e36
  have e23 : (inner ℝ (y 2) (y 3) : ℝ) = 1 - s23 / 2 := by
    rw [hipgen, hn2, hn3, hs23def]; ring
  have e32 : (inner ℝ (y 3) (y 2) : ℝ) = 1 - s23 / 2 := by
    rw [real_inner_comm]; exact e23
  have e34 : (inner ℝ (y 3) (y 4) : ℝ) = 1 - s34 / 2 := by
    rw [hipgen, hn3, hn4, hs34def]; ring
  have e43 : (inner ℝ (y 4) (y 3) : ℝ) = 1 - s34 / 2 := by
    rw [real_inner_comm]; exact e34
  have e25 : (inner ℝ (y 2) (y 5) : ℝ) = 1 - s25 / 2 := by
    rw [hipgen, hn2, hn5, hs25def]; ring
  have e52 : (inner ℝ (y 5) (y 2) : ℝ) = 1 - s25 / 2 := by
    rw [real_inner_comm]; exact e25
  have e17 : (inner ℝ (y 1) (y 7) : ℝ) = 1 - s17 / 2 := by
    rw [hipgen, hn1, hn7, hs17def]; ring
  have e71 : (inner ℝ (y 7) (y 1) : ℝ) = 1 - s17 / 2 := by
    rw [real_inner_comm]; exact e17
  -- inner products with y8 (|y8|² = s08)
  have e18 : (inner ℝ (y 1) (y 8) : ℝ) = s08 / 2 := by
    rw [hipgen, hn1, hnrm 8, dist_comm (q 8) (q 0), h18, hs08def]; ring
  have e81 : (inner ℝ (y 8) (y 1) : ℝ) = s08 / 2 := by
    rw [real_inner_comm]; exact e18
  have e28 : (inner ℝ (y 2) (y 8) : ℝ) = s08 / 2 := by
    rw [hipgen, hn2, hnrm 8, dist_comm (q 8) (q 0), h28, hs08def]; ring
  have e82 : (inner ℝ (y 8) (y 2) : ℝ) = s08 / 2 := by
    rw [real_inner_comm]; exact e28
  have e38 : (inner ℝ (y 3) (y 8) : ℝ) = s08 / 2 := by
    rw [hipgen, hn3, hnrm 8, dist_comm (q 8) (q 0), h38, hs08def]; ring
  have e83 : (inner ℝ (y 8) (y 3) : ℝ) = s08 / 2 := by
    rw [real_inner_comm]; exact e38
  have e78 : (inner ℝ (y 7) (y 8) : ℝ) = s08 / 2 := by
    rw [hipgen, hn7, hnrm 8, dist_comm (q 8) (q 0), h78, hs08def]; ring
  have e87 : (inner ℝ (y 8) (y 7) : ℝ) = s08 / 2 := by
    rw [real_inner_comm]; exact e78
  -- Step 1: det G[y1,y2,y4,y6] pins s26 = 8/3
  have hp26 : s26 = 8 / 3 := by
    have hd := gram_det_zero ![y 1, y 2, y 4, y 6]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hd
    rw [hs1, hs2, hs4, hs6, e12, e21, e14, e41, e16, e61, e24, e42, e26, e62,
      e46, e64] at hd
    have hfact : s26 * (3 * s26 - 8) = 0 := by linear_combination (-16 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  -- Step 2: det G[y1,y3,y5,y6] pins s36 = 8/3
  have hp36 : s36 = 8 / 3 := by
    have hd := gram_det_zero ![y 1, y 3, y 5, y 6]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hd
    rw [hs1, hs3, hs5, hs6, e13, e31, e15, e51, e16, e61, e35, e53, e36, e63,
      e56, e65] at hd
    have hfact : s36 * (3 * s36 - 8) = 0 := by linear_combination (-16 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  -- Step 3: det G[y1,y2,y3,y6] pins s23 = 32/27
  have hp23 : s23 = 32 / 27 := by
    have hd := gram_det_zero ![y 1, y 2, y 3, y 6]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hd
    rw [hs1, hs2, hs3, hs6, e12, e21, e13, e31, e16, e61, e23, e32, e26, e62,
      e36, e63, hp26, hp36] at hd
    have hfact : s23 * (27 * s23 - 32) = 0 := by
      linear_combination (-144 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  -- Step 4: det G[y1,y2,y3,y4] pins s34 = 25/9
  have hp34 : s34 = 25 / 9 := by
    have hd := gram_det_zero ![y 1, y 2, y 3, y 4]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hd
    rw [hs1, hs2, hs3, hs4, e12, e21, e13, e31, e14, e41, e23, e32, e24, e42,
      e34, e43, hp23] at hd
    have hfact : (9 * s34 - 25) * (81 * s34 - 1) = 0 := by
      linear_combination (-3888 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  -- Step 5: det G[y1,y2,y3,y5] pins s25 = 25/9
  have hp25 : s25 = 25 / 9 := by
    have hd := gram_det_zero ![y 1, y 2, y 3, y 5]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hd
    rw [hs1, hs2, hs3, hs5, e12, e21, e13, e31, e15, e51, e23, e32, e25, e52,
      e35, e53, hp23] at hd
    have hfact : (9 * s25 - 25) * (81 * s25 - 1) = 0 := by
      linear_combination (-3888 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  -- Step 6: det G[y1,y2,y3,y7] pins s17 = 49/19
  have hp17 : s17 = 49 / 19 := by
    have hd := gram_det_zero ![y 1, y 2, y 3, y 7]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hd
    rw [hs1, hs2, hs3, hs7, e12, e21, e13, e31, e17, e71, e23, e32, e27, e72,
      e37, e73, hp23] at hd
    have hfact : s17 * (19 * s17 - 49) = 0 := by
      linear_combination (-729 / 8 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  -- Step 7: det G[y1,y2,y3,y8] pins s08 = 49/19
  have hp08 : s08 = 49 / 19 := by
    have hd := gram_det_zero ![y 1, y 2, y 3, y 8]
    rw [det_fin_four] at hd
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] at hd
    rw [hs1, hs2, hs3, hs8, e12, e21, e13, e31, e18, e81, e23, e32, e28, e82,
      e38, e83, hp23] at hd
    have hfact : s08 * (19 * s08 - 49) = 0 := by
      linear_combination (-729 / 8 : ℝ) * hd
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · linarith
  -- Step 8: det G[y1,y2,y7,y8] is a nonzero rational — contradiction
  have hd := gram_det_zero ![y 1, y 2, y 7, y 8]
  rw [det_fin_four] at hd
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_three] at hd
  rw [hs1, hs2, hs7, hs8, e12, e21, e17, e71, e18, e81, e27, e72, e28, e82,
    e78, e87, hp17, hp08] at hd
  have hfinal : (1716715 : ℝ) / 2085136 = 0 := by
    linear_combination (-1 : ℝ) * hd
  norm_num at hfinal

end Kissing3D
