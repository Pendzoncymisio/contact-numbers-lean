import ContactNumbers.Frame

set_option linter.style.header false
set_option maxHeartbeats 1000000

/-!
# Local contact structure

The entry point to the structure problem: what the bond graph of a hard-core configuration
looks like *locally*. Everything here is direction counting in a plane, reusing the frame
machinery (`parseval3`, `cross3`) built for the cap count.

* `no_six` / `gap_bounds_six` — six directions with pairwise cosine `≤ 1/3` do not fit on
  a circle. The threshold comparison is `1/3 < cos 60° = 1/2`, exact and trivial.
* `ring_card_le_five` — at most five vectors of norm `√3/2`, orthogonal to a unit axis,
  pairwise at inner product `≤ 1/4`.
* `common_neighbors_le_five` — **the triangle bound**: two bonded particles have at most
  five common neighbours. They lie on the circle of radius `√3/2` around the midpoint of
  the bond, pairwise at least `1` apart. FCC and HCP realise **four**; five is realised by
  a pentagonal bipyramid fragment, which is exactly the local obstruction that makes 3D
  crystallization hard.
* `shell_bonds_le_sixty` — the bond graph inside a contact shell: each of the at most
  twelve neighbours of `v` touches at most five of the others, so the shell carries at
  most 30 internal contacts (ordered: 60). FCC/HCP-local shells carry 24; the gap
  `24 ≤ · ≤ 30` is precisely the open local-structure problem recorded in the plan.
* `gram_offdiag_ge` — the off-diagonal Gram sum of any finite unit-vector family is at
  least `−|S|` (nonnegativity of `‖Σy‖²`), the global constraint used by the
  second-moment bookkeeping.
-/

namespace Kissing3D

open Real

/-! ### Six directions do not fit -/

/-- **A gap of more than `60°`.** Any `d ∈ (0, 2π)` with `cos d ≤ 1/3` lies strictly
between `π/3` and `5π/3`. The comparison `1/3 < cos(π/3) = 1/2` is exact. -/
theorem gap_bounds_six {d : ℝ} (h0 : 0 < d) (h2 : d < 2*π) (hc : Real.cos d ≤ 1/3) :
    π/3 < d ∧ d < 5*π/3 := by
  have hpi := Real.pi_pos
  have key : (1:ℝ)/3 < Real.cos (π/3) := by
    rw [Real.cos_pi_div_three]; norm_num
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    have : Real.cos (π/3) ≤ Real.cos d :=
      Real.cos_le_cos_of_nonneg_of_le_pi h0.le (by linarith) h
    linarith
  · by_contra h
    push_neg at h
    have hle : Real.cos (π/3) ≤ Real.cos (2*π - d) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    rw [show (2*π - d) = -(d - 2*π) by ring, Real.cos_neg,
      show d - 2*π = d + (-1 : ℤ) * (2*π) by push_cast; ring,
      Real.cos_add_int_mul_two_pi] at hle
    linarith

/-- **Six directions do not fit.** Six reals, pairwise less than a full turn apart and
pairwise of cosine at most `1/3`, cannot exist: the five consecutive gaps exceed `5π/3`,
but the total span is below `5π/3`. -/
theorem no_six {T : Finset ℝ} (hcard : 6 ≤ T.card)
    (hspan : ∀ x ∈ T, ∀ y ∈ T, x - y < 2*π)
    (hcos : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Real.cos (x - y) ≤ 1/3) : False := by
  obtain ⟨T', hsub, hc6⟩ := Finset.exists_subset_card_eq hcard
  set g := T'.orderEmbOfFin hc6 with hg
  have hmem : ∀ i, g i ∈ T := fun i => hsub (T'.orderEmbOfFin_mem hc6 i)
  have hlt : ∀ i j : Fin 6, i < j → g i < g j := fun i j h => g.strictMono h
  have gap : ∀ i j : Fin 6, i < j → π/3 < g j - g i := by
    intro i j hij
    refine (gap_bounds_six (sub_pos.mpr (hlt i j hij)) ?_ ?_).1
    · exact hspan _ (hmem j) _ (hmem i)
    · exact hcos _ (hmem j) _ (hmem i) (hlt i j hij).ne'
  have top : g 5 - g 0 < 5*π/3 := by
    refine (gap_bounds_six (sub_pos.mpr (hlt 0 5 (by decide))) ?_ ?_).2
    · exact hspan _ (hmem 5) _ (hmem 0)
    · exact hcos _ (hmem 5) _ (hmem 0) (hlt 0 5 (by decide)).ne'
  have g01 := gap 0 1 (by decide)
  have g12 := gap 1 2 (by decide)
  have g23 := gap 2 3 (by decide)
  have g34 := gap 3 4 (by decide)
  have g45 := gap 4 5 (by decide)
  linarith

/-! ### The ring count -/

/-- **At most five points on the ring.** Vectors of squared norm `3/4`, orthogonal to the
unit axis `p` and pairwise at inner product at most `1/4`, number at most five: their
azimuthal cosines are at most `(1/4)/(3/4) = 1/3`, and six such directions do not fit. -/
theorem ring_card_le_five {S : Finset (Fin 3 → ℝ)} {p : Fin 3 → ℝ} (hp : dot3 p p = 1)
    (hperp : ∀ z ∈ S, dot3 p z = 0)
    (hnorm : ∀ z ∈ S, dot3 z z = 3/4)
    (hsep : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → dot3 z z' ≤ 1/4) : S.card ≤ 5 := by
  by_contra hcon
  push_neg at hcon
  have hcard : 6 ≤ S.card := hcon
  obtain ⟨z₀, hz₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  set R : ℝ := Real.sqrt (3/4) with hRdef
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by norm_num)
  have hRne : R ≠ 0 := hRpos.ne'
  have hRsq : R ^ 2 = 3/4 := Real.sq_sqrt (by norm_num)
  -- the frame built on one chosen ring point
  set e : Fin 3 → ℝ := fun i => R⁻¹ * z₀ i with he
  have hee : dot3 e e = 1 := by
    have hexp : dot3 e e = R⁻¹ ^ 2 * dot3 z₀ z₀ := by simp only [he, dot3]; ring
    rw [hexp, hnorm z₀ hz₀, ← hRsq]
    field_simp
  have hpe : dot3 p e = 0 := by
    have hexp : dot3 p e = R⁻¹ * dot3 p z₀ := by simp only [he, dot3]; ring
    rw [hexp, hperp z₀ hz₀, mul_zero]
  set f := cross3 p e with hf
  set A : (Fin 3 → ℝ) → ℝ := fun z => dot3 e z with hA
  set B : (Fin 3 → ℝ) → ℝ := fun z => dot3 f z with hB
  have hpars : ∀ z ∈ S, ∀ z' ∈ S, dot3 z z' = A z * A z' + B z * B z' := by
    intro z hz z' hz'
    have hpar := parseval3 p e z z' hp hee hpe
    rw [hperp z hz, hperp z' hz'] at hpar
    simp only [hA, hB, hf]
    linarith [hpar]
  have hnormsq : ∀ z ∈ S, A z ^ 2 + B z ^ 2 = 3/4 := by
    intro z hz
    have h := hpars z hz z hz
    rw [hnorm z hz] at h
    nlinarith [h]
  -- planar coordinates as a complex number, and its argument
  set w : (Fin 3 → ℝ) → ℂ := fun z => ⟨A z, B z⟩ with hw
  have hNsq : ∀ z, ‖w z‖ ^ 2 = A z ^ 2 + B z ^ 2 := by
    intro z; rw [Complex.sq_norm]; simp only [hw, Complex.normSq_mk]; ring
  have hNR : ∀ z ∈ S, ‖w z‖ = R := by
    intro z hz
    have h1 : ‖w z‖ ^ 2 = R ^ 2 := by rw [hNsq z, hnormsq z hz, hRsq]
    nlinarith [norm_nonneg (w z), h1, hRpos.le]
  have hwne : ∀ z ∈ S, w z ≠ 0 := by
    intro z hz
    have : 0 < ‖w z‖ := by rw [hNR z hz]; exact hRpos
    exact norm_pos_iff.mp this
  set θ : (Fin 3 → ℝ) → ℝ := fun z => Complex.arg (w z) with hθ
  have hcosdiff : ∀ z ∈ S, ∀ z' ∈ S,
      Real.cos (θ z - θ z') = (A z * A z' + B z * B z') / (R * R) := by
    intro z hz z' hz'
    rw [Real.cos_sub, hθ]
    rw [Complex.cos_arg (hwne z hz), Complex.cos_arg (hwne z' hz'),
      Complex.sin_arg, Complex.sin_arg, hNR z hz, hNR z' hz']
    have hre : (w z).re = A z := rfl
    have him : (w z).im = B z := rfl
    have hre' : (w z').re = A z' := rfl
    have him' : (w z').im = B z' := rfl
    rw [hre, him, hre', him']
    field_simp
  have hkey : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → Real.cos (θ z - θ z') ≤ 1/3 := by
    intro z hz z' hz' hne
    rw [hcosdiff z hz z' hz', ← hpars z hz z' hz',
      div_le_iff₀ (mul_pos hRpos hRpos)]
    have hs := hsep z hz z' hz' hne
    nlinarith [hs, hRsq]
  have hinj : Set.InjOn θ ↑S := by
    intro z hz z' hz' heq
    by_contra hne
    have hb := hkey z (by simpa using hz) z' (by simpa using hz') hne
    rw [heq, sub_self, Real.cos_zero] at hb
    norm_num at hb
  refine no_six (T := S.image θ) ?_ ?_ ?_
  · rw [Finset.card_image_of_injOn hinj]; omega
  · intro x hx y hy
    simp only [Finset.mem_image] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    have h1 := Complex.arg_le_pi (w a)
    have h2 := Complex.neg_pi_lt_arg (w b)
    have hpi := Real.pi_pos
    simp only [hθ]
    linarith
  · intro x hx y hy hxy
    simp only [Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hkey a ha b hb (fun h => hxy (by rw [h]))

/-! ### Planar coordinates on the ring plane -/

/-- The plane `p^⊥` carries two coordinates in which `dot3` is the plain 2D inner
product — the `parseval3` frame, packaged. -/
lemma exists_planar_coords {p : Fin 3 → ℝ} (hp : dot3 p p = 1) (z₀ : Fin 3 → ℝ)
    (hz₀p : dot3 p z₀ = 0) (hz₀ : dot3 z₀ z₀ = 3/4) :
    ∃ A B : (Fin 3 → ℝ) → ℝ, ∀ x y : Fin 3 → ℝ, dot3 p x = 0 → dot3 p y = 0 →
      dot3 x y = A x * A y + B x * B y := by
  set R : ℝ := Real.sqrt (3/4) with hRdef
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by norm_num)
  have hRsq : R ^ 2 = 3/4 := Real.sq_sqrt (by norm_num)
  set e : Fin 3 → ℝ := fun i => R⁻¹ * z₀ i with he
  have hee : dot3 e e = 1 := by
    have hexp : dot3 e e = R⁻¹ ^ 2 * dot3 z₀ z₀ := by simp only [he, dot3]; ring
    rw [hexp, hz₀, ← hRsq]
    field_simp
  have hpe : dot3 p e = 0 := by
    have hexp : dot3 p e = R⁻¹ * dot3 p z₀ := by simp only [he, dot3]; ring
    rw [hexp, hz₀p, mul_zero]
  refine ⟨fun x => dot3 e x, fun x => dot3 (cross3 p e) x, fun x y hx hy => ?_⟩
  have hpar := parseval3 p e x y hp hee hpe
  rw [hx, hy] at hpar
  linarith [hpar]

/-- **No triangle on the ring**: three vectors in `p^⊥` of squared norm `3/4`, pairwise at
inner product exactly `1/4`, do not exist — their Gram matrix has determinant `5/16 ≠ 0`
but rank at most two. Via the Cramer relation and one Lagrange identity. -/
theorem ring_no_triangle {p u v w : Fin 3 → ℝ} (hp : dot3 p p = 1)
    (hpu : dot3 p u = 0) (hpv : dot3 p v = 0) (hpw : dot3 p w = 0)
    (huu : dot3 u u = 3/4) (hvv : dot3 v v = 3/4) (hww : dot3 w w = 3/4)
    (huv : dot3 u v = 1/4) (huw : dot3 u w = 1/4) (hvw : dot3 v w = 1/4) : False := by
  obtain ⟨A, B, hAB⟩ := exists_planar_coords hp u hpu huu
  set x1 := A u with hx1; set y1 := B u with hy1
  set x2 := A v with hx2; set y2 := B v with hy2
  set x3 := A w with hx3; set y3 := B w with hy3
  have g11 : x1*x1 + y1*y1 = 3/4 := by rw [hx1, hy1, ← hAB u u hpu hpu]; exact huu
  have g22 : x2*x2 + y2*y2 = 3/4 := by rw [hx2, hy2, ← hAB v v hpv hpv]; exact hvv
  have g33 : x3*x3 + y3*y3 = 3/4 := by rw [hx3, hy3, ← hAB w w hpw hpw]; exact hww
  have g12 : x1*x2 + y1*y2 = 1/4 := by rw [hx1, hy1, hx2, hy2, ← hAB u v hpu hpv]; exact huv
  have g13 : x1*x3 + y1*y3 = 1/4 := by rw [hx1, hy1, hx3, hy3, ← hAB u w hpu hpw]; exact huw
  have g23 : x2*x3 + y2*y3 = 1/4 := by rw [hx2, hy2, hx3, hy3, ← hAB v w hpv hpw]; exact hvw
  set c1 : ℝ := x2*y3 - x3*y2 with hc1
  set c2 : ℝ := x3*y1 - x1*y3 with hc2
  set c3 : ℝ := x1*y2 - x2*y1 with hc3
  have hA0 : c1*x1 + c2*x2 + c3*x3 = 0 := by rw [hc1, hc2, hc3]; ring
  have hB0 : c1*y1 + c2*y2 + c3*y3 = 0 := by rw [hc1, hc2, hc3]; ring
  have hT : (1/2)*(c1^2+c2^2+c3^2) + (1/4)*(c1+c2+c3)^2 = 0 := by
    linear_combination (-(c1^2)) * g11 + (-(c2^2)) * g22 + (-(c3^2)) * g33
      + (-(2*c1*c2)) * g12 + (-(2*c1*c3)) * g13 + (-(2*c2*c3)) * g23
      + (c1*x1 + c2*x2 + c3*x3) * hA0 + (c1*y1 + c2*y2 + c3*y3) * hB0
  have hc3sq : c3^2 = 1/2 := by
    rw [hc3]
    linear_combination (x2*x2 + y2*y2) * g11 + (3/4) * g22 - (x1*x2 + y1*y2 + 1/4) * g12
  linarith [hT, hc3sq, sq_nonneg c1, sq_nonneg c2, sq_nonneg (c1+c2+c3)]

/-- **No square on the ring**: four vectors in `p^⊥` of squared norm `3/4` forming a
four-cycle of exact-`1/4` inner products across the pairing `{a,b} | {c,d}`, with the
diagonals hard-core (`≤ 1/4`), do not exist. Both `c` and `d` are orthogonal to
`a − b ≠ 0` in a plane, hence parallel; `⟨c,d⟩ = ±3/4` and both signs are absurd. -/
theorem ring_no_square {p a b c d : Fin 3 → ℝ} (hp : dot3 p p = 1)
    (hpa : dot3 p a = 0) (hpb : dot3 p b = 0) (hpc : dot3 p c = 0) (hpd : dot3 p d = 0)
    (haa : dot3 a a = 3/4) (hbb : dot3 b b = 3/4) (hcc : dot3 c c = 3/4)
    (hdd : dot3 d d = 3/4)
    (hac : dot3 a c = 1/4) (had : dot3 a d = 1/4) (hbc : dot3 b c = 1/4)
    (hbd : dot3 b d = 1/4)
    (hab : dot3 a b ≤ 1/4) (hcd : dot3 c d ≤ 1/4) : False := by
  obtain ⟨A, B, hAB⟩ := exists_planar_coords hp a hpa haa
  set x1 := A a with hx1; set y1 := B a with hy1
  set x2 := A b with hx2; set y2 := B b with hy2
  set x3 := A c with hx3; set y3 := B c with hy3
  set x4 := A d with hx4; set y4 := B d with hy4
  have g11 : x1*x1 + y1*y1 = 3/4 := by rw [hx1, hy1, ← hAB a a hpa hpa]; exact haa
  have g22 : x2*x2 + y2*y2 = 3/4 := by rw [hx2, hy2, ← hAB b b hpb hpb]; exact hbb
  have g33 : x3*x3 + y3*y3 = 3/4 := by rw [hx3, hy3, ← hAB c c hpc hpc]; exact hcc
  have g44 : x4*x4 + y4*y4 = 3/4 := by rw [hx4, hy4, ← hAB d d hpd hpd]; exact hdd
  have g13 : x1*x3 + y1*y3 = 1/4 := by rw [hx1, hy1, hx3, hy3, ← hAB a c hpa hpc]; exact hac
  have g14 : x1*x4 + y1*y4 = 1/4 := by rw [hx1, hy1, hx4, hy4, ← hAB a d hpa hpd]; exact had
  have g23 : x2*x3 + y2*y3 = 1/4 := by rw [hx2, hy2, hx3, hy3, ← hAB b c hpb hpc]; exact hbc
  have g24 : x2*x4 + y2*y4 = 1/4 := by rw [hx2, hy2, hx4, hy4, ← hAB b d hpb hpd]; exact hbd
  have g12 : x1*x2 + y1*y2 ≤ 1/4 := by rw [hx1, hy1, hx2, hy2, ← hAB a b hpa hpb]; exact hab
  have g34 : x3*x4 + y3*y4 ≤ 1/4 := by rw [hx3, hy3, hx4, hy4, ← hAB c d hpc hpd]; exact hcd
  -- `a − b` is a nonzero plane vector orthogonal to both `c` and `d`
  have hw : 1 ≤ (x1-x2)^2 + (y1-y2)^2 := by nlinarith [g11, g22, g12]
  have h3w : x3*(x1-x2) + y3*(y1-y2) = 0 := by linear_combination g13 - g23
  have h4w : x4*(x1-x2) + y4*(y1-y2) = 0 := by linear_combination g14 - g24
  set det : ℝ := x3*y4 - x4*y3 with hdet
  have hprod : det^2 * ((x1-x2)^2 + (y1-y2)^2) = 0 := by
    rw [hdet]
    linear_combination
      ((x3*y4 - x4*y3)*(x1-x2)*y4 - (x3*y4 - x4*y3)*(y1-y2)*x4) * h3w
      + ((x3*y4 - x4*y3)*(y1-y2)*x3 - (x3*y4 - x4*y3)*(x1-x2)*y3) * h4w
  have hdetle : det^2 ≤ 0 := by nlinarith [hprod, hw, sq_nonneg det]
  -- Lagrange forces `⟨c,d⟩ = ±3/4`
  have hlag : (x3*x4 + y3*y4)^2 + det^2 = 9/16 := by
    rw [hdet]
    linear_combination (x4*x4 + y4*y4) * g33 + (3/4) * g44
  have hcd2 : (x3*x4 + y3*y4)^2 = 9/16 := by
    linarith [hlag, hdetle, sq_nonneg det]
  have hfact : (x3*x4 + y3*y4 - 3/4) * (x3*x4 + y3*y4 + 3/4) = 0 := by
    linear_combination hcd2
  rcases mul_eq_zero.mp hfact with h34 | h34
  · -- `⟨c,d⟩ = 3/4` contradicts the hard core
    linarith [g34]
  · -- `⟨c,d⟩ = −3/4` means `d = −c`, but both have inner product `1/4` with `a`
    have hsum : (x3+x4)^2 + (y3+y4)^2 = 0 := by
      linear_combination g33 + g44 + 2 * h34
    have hval : x1*(x3+x4) + y1*(y3+y4) = 1/2 := by linear_combination g13 + g14
    have hlag2 : (x1*(x3+x4) + y1*(y3+y4))^2 + (x1*(y3+y4) - y1*(x3+x4))^2
        = (x1*x1 + y1*y1) * ((x3+x4)^2 + (y3+y4)^2) := by ring
    have hz : (x1*x1 + y1*y1) * ((x3+x4)^2 + (y3+y4)^2) = 0 :=
      mul_eq_zero_of_right _ hsum
    nlinarith [hlag2, hz, hval, sq_nonneg (x1*(y3+y4) - y1*(x3+x4))]

/-- **The two-positions identity.** Two ring vectors at the same inner product `α` from a
third sit either on top of each other (`⟨x,y⟩ = 3/4`) or at its reflection
(`⟨x,y⟩ = 8α²/3 − 3/4`). Lagrange plus the planar Cramer identity
`‖c‖²⟨x,y⟩ = ⟨c,x⟩⟨c,y⟩ + det(c,x)det(c,y)`. -/
theorem ring_two_positions {p c x y : Fin 3 → ℝ} (hp : dot3 p p = 1)
    (hpc : dot3 p c = 0) (hpx : dot3 p x = 0) (hpy : dot3 p y = 0)
    (hcc : dot3 c c = 3/4) (hxx : dot3 x x = 3/4) (hyy : dot3 y y = 3/4)
    {α : ℝ} (hcx : dot3 c x = α) (hcy : dot3 c y = α) :
    dot3 x y = 3/4 ∨ dot3 x y = 8*α^2/3 - 3/4 := by
  obtain ⟨A, B, hAB⟩ := exists_planar_coords hp c hpc hcc
  set x1 := A c with hx1; set y1 := B c with hy1
  set x2 := A x with hx2; set y2 := B x with hy2
  set x3 := A y with hx3; set y3 := B y with hy3
  have gcc : x1*x1 + y1*y1 = 3/4 := by rw [hx1, hy1, ← hAB c c hpc hpc]; exact hcc
  have gxx : x2*x2 + y2*y2 = 3/4 := by rw [hx2, hy2, ← hAB x x hpx hpx]; exact hxx
  have gyy : x3*x3 + y3*y3 = 3/4 := by rw [hx3, hy3, ← hAB y y hpy hpy]; exact hyy
  have gcx : x1*x2 + y1*y2 = α := by rw [hx1, hy1, hx2, hy2, ← hAB c x hpc hpx]; exact hcx
  have gcy : x1*x3 + y1*y3 = α := by rw [hx1, hy1, hx3, hy3, ← hAB c y hpc hpy]; exact hcy
  have hd : dot3 x y = x2*x3 + y2*y3 := by
    rw [hx2, hy2, hx3, hy3]; exact hAB x y hpx hpy
  set Dx : ℝ := x1*y2 - x2*y1 with hDx
  set Dy : ℝ := x1*y3 - x3*y1 with hDy
  have L1 : Dx^2 = 9/16 - α^2 := by
    rw [hDx]
    linear_combination (x2*x2 + y2*y2) * gcc + (3/4) * gxx - (x1*x2 + y1*y2 + α) * gcx
  have L2 : Dy^2 = 9/16 - α^2 := by
    rw [hDy]
    linear_combination (x3*x3 + y3*y3) * gcc + (3/4) * gyy - (x1*x3 + y1*y3 + α) * gcy
  have R : (3/4) * (x2*x3 + y2*y3) = α^2 + Dx*Dy := by
    rw [hDx, hDy]
    linear_combination (x1*x3 + y1*y3) * gcx + α * gcy - (x2*x3 + y2*y3) * gcc
  have key : ((3/4) * (x2*x3 + y2*y3) - α^2)^2 = (9/16 - α^2)^2 := by
    linear_combination ((3/4) * (x2*x3 + y2*y3) - α^2 + Dx*Dy) * R + Dy^2 * L1
      + (9/16 - α^2) * L2
  have hfact : ((x2*x3 + y2*y3) - 3/4) * ((x2*x3 + y2*y3) - (8*α^2/3 - 3/4)) = 0 := by
    linear_combination (16/9) * key
  rcases mul_eq_zero.mp hfact with h | h
  · left; rw [hd]; linarith
  · right; rw [hd]; linarith

/-- **No pentagon on the ring**: a five-cycle of exact-`1/4` inner products among ring
vectors, with the two skew pairs at `z1` hard-core, is impossible. Chaining the
two-positions identity forces `⟨z1,z3⟩ = ⟨z1,z4⟩ = −7/12`, and then `z3, z4` would have
to sit at inner product `3/4` or `17/108` — but they are adjacent at `1/4`. -/
theorem ring_no_pentagon {p z1 z2 z3 z4 z5 : Fin 3 → ℝ} (hp : dot3 p p = 1)
    (hp1 : dot3 p z1 = 0) (hp2 : dot3 p z2 = 0) (hp3 : dot3 p z3 = 0)
    (hp4 : dot3 p z4 = 0) (hp5 : dot3 p z5 = 0)
    (h11 : dot3 z1 z1 = 3/4) (h22 : dot3 z2 z2 = 3/4) (h33 : dot3 z3 z3 = 3/4)
    (h44 : dot3 z4 z4 = 3/4) (h55 : dot3 z5 z5 = 3/4)
    (h12 : dot3 z1 z2 = 1/4) (h23 : dot3 z2 z3 = 1/4) (h34 : dot3 z3 z4 = 1/4)
    (h45 : dot3 z4 z5 = 1/4) (h51 : dot3 z5 z1 = 1/4)
    (h13 : dot3 z1 z3 ≤ 1/4) (h14 : dot3 z1 z4 ≤ 1/4) : False := by
  have hcomm : ∀ u v : Fin 3 → ℝ, dot3 u v = dot3 v u := by
    intro u v; simp only [dot3]; ring
  -- `⟨z1,z3⟩ = −7/12` via `z2`
  have hd13 : dot3 z1 z3 = -(7/12) := by
    rcases ring_two_positions hp hp2 hp1 hp3 h22 h11 h33
        ((hcomm z2 z1).trans h12) h23 with h | h
    · linarith
    · rw [h]; norm_num
  -- `⟨z1,z4⟩ = −7/12` via `z5`
  have hd14 : dot3 z1 z4 = -(7/12) := by
    rcases ring_two_positions hp hp5 hp1 hp4 h55 h11 h44
        h51 ((hcomm z5 z4).trans h45) with h | h
    · linarith
    · rw [h]; norm_num
  -- `z3, z4` both at `−7/12` from `z1`, yet adjacent
  rcases ring_two_positions hp hp1 hp3 hp4 h11 h33 h44
      hd13 hd14 with h | h
  · rw [h34] at h; norm_num at h
  · rw [h34] at h; norm_num at h

/-- **Degree at most two on the ring**: a ring vector cannot be in exact contact with
three others. Three ring vectors at inner product exactly `1/4` from `c` are pairwise at
`−7/12` (the coincidence branch `3/4` is excluded by the hard-core bound `≤ 1/4`), but
then the two-positions identity at `α = −7/12` puts any two of them at `3/4` or `17/108`
— neither is `−7/12`. Hence the ring contact graph is a disjoint union of paths. -/
theorem ring_degree_le_two {p c x y z : Fin 3 → ℝ} (hp : dot3 p p = 1)
    (hpc : dot3 p c = 0) (hpx : dot3 p x = 0) (hpy : dot3 p y = 0) (hpz : dot3 p z = 0)
    (hcc : dot3 c c = 3/4) (hxx : dot3 x x = 3/4) (hyy : dot3 y y = 3/4)
    (hzz : dot3 z z = 3/4)
    (hcx : dot3 c x = 1/4) (hcy : dot3 c y = 1/4) (hcz : dot3 c z = 1/4)
    (hxy : dot3 x y ≤ 1/4) (hxz : dot3 x z ≤ 1/4) (hyz : dot3 y z ≤ 1/4) : False := by
  have hdxy : dot3 x y = -(7/12) := by
    rcases ring_two_positions hp hpc hpx hpy hcc hxx hyy hcx hcy with h | h
    · linarith
    · rw [h]; norm_num
  have hdxz : dot3 x z = -(7/12) := by
    rcases ring_two_positions hp hpc hpx hpz hcc hxx hzz hcx hcz with h | h
    · linarith
    · rw [h]; norm_num
  have hdyz : dot3 y z = -(7/12) := by
    rcases ring_two_positions hp hpc hpy hpz hcc hyy hzz hcy hcz with h | h
    · linarith
    · rw [h]; norm_num
  rcases ring_two_positions hp hpx hpy hpz hxx hyy hzz hdxy hdxz with h | h
  · rw [hdyz] at h; norm_num at h
  · rw [hdyz] at h; norm_num at h

/-! ### The triangle bound -/

open scoped Classical in
/-- **Two bonded particles have at most five common neighbours.** The common neighbours
sit on the circle of radius `√3/2` about the midpoint of the bond — orthogonal to it,
squared norm `3/4` after recentring — pairwise at least `1` apart, hence at inner product
at most `1/4` there. FCC and HCP realise four; the pentagonal bipyramid realises five. -/
theorem common_neighbors_le_five {X : Finset E3} (hX : HardCore X) {v w : E3}
    (hvw : dist v w = 1) :
    ((neighbors X v) ∩ (neighbors X w)).card ≤ 5 := by
  set C : Finset E3 := (neighbors X v) ∩ (neighbors X w) with hC
  set sh : E3 → E3 := fun u => u - v - (2⁻¹ : ℝ) • (w - v) with hsh
  have hq : ‖w - v‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hvw
  -- membership data
  have hmem : ∀ u ∈ C, u ∈ X ∧ ‖u - v‖ = 1 ∧ ‖u - w‖ = 1 := by
    intro u hu
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hu
    obtain ⟨huX, hd1⟩ := Finset.mem_filter.mp h1
    obtain ⟨_, hd2⟩ := Finset.mem_filter.mp h2
    exact ⟨huX, by rw [← hd1, dist_eq_norm, norm_sub_rev],
      by rw [← hd2, dist_eq_norm, norm_sub_rev]⟩
  -- the axis coordinate of every common neighbour is exactly `1/2`
  have hip : ∀ u ∈ C, inner ℝ (u - v) (w - v) = (2⁻¹ : ℝ) := by
    intro u hu
    obtain ⟨_, h1, h2⟩ := hmem u hu
    have e1 : ‖(u - v) - (w - v)‖ = 1 := by
      rw [show (u - v) - (w - v) = u - w by abel]; exact h2
    have e2 := norm_sub_sq_real (u - v) (w - v)
    rw [e1, h1, hq] at e2
    norm_num at e2
    linarith
  -- the shifted points have squared norm `3/4` and pairwise differences `a − b`
  have hnormsh : ∀ u ∈ C, ‖sh u‖ ^ 2 = 3/4 := by
    intro u hu
    have h1 : inner ℝ (u - v) ((2⁻¹ : ℝ) • (w - v)) = (4⁻¹ : ℝ) := by
      rw [real_inner_smul_right, hip u hu]; norm_num
    have h2 : ‖(2⁻¹ : ℝ) • (w - v)‖ ^ 2 = (4⁻¹ : ℝ) := by
      rw [norm_smul, hq, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
      norm_num
    have h3 := norm_sub_sq_real (u - v) ((2⁻¹ : ℝ) • (w - v))
    rw [h1, h2, (hmem u hu).2.1] at h3
    simp only [hsh]
    rw [h3]
    norm_num
  have hshsub : ∀ a b : E3, sh a - sh b = a - b := by
    intro a b; simp only [hsh]; abel
  -- the recentred points, as plain functions
  have hshinj : Set.InjOn (fun u : E3 => WithLp.ofLp (sh u)) ↑C := by
    intro a _ b _ h
    have h2 : sh a = sh b := WithLp.ofLp_injective _ h
    simp only [hsh, sub_left_inj] at h2
    exact h2
  rw [← Finset.card_image_of_injOn hshinj]
  refine ring_card_le_five (p := WithLp.ofLp (w - v)) (dot3_self_of_norm hq) ?_ ?_ ?_
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    rw [dot3_eq_inner]
    have h1 : inner ℝ (w - v) ((2⁻¹ : ℝ) • (w - v)) = (2⁻¹ : ℝ) := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hq]; norm_num
    have h2 : inner ℝ (w - v) (u - v) = (2⁻¹ : ℝ) := by
      rw [real_inner_comm]; exact hip u hu
    simp only [hsh]
    rw [inner_sub_right, h1, h2]
    ring
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    rw [dot3_eq_inner, real_inner_self_eq_norm_sq]
    exact hnormsh u hu
  · intro x hx x' hx' hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx'
    have hab : a ≠ b := fun h => hne (by rw [h])
    rw [dot3_eq_inner]
    -- polarisation: `‖sh a − sh b‖² = ‖a − b‖² ≥ 1` bounds the inner product
    have hpol := norm_sub_sq_real (sh a) (sh b)
    rw [hshsub a b, ← dist_eq_norm] at hpol
    have hfar : 1 ≤ dist a b := hX a (hmem a ha).1 b (hmem b hb).1 hab
    have hd2 : (1:ℝ) ≤ dist a b ^ 2 := by
      nlinarith [dist_nonneg (x := a) (y := b)]
    have hna := hnormsh a ha
    have hnb := hnormsh b hb
    nlinarith [hpol, hd2, hna, hnb]

/-- Scalar core of the triple bound: a vector `(g0, g1)` killed by the Gram rows of two
vectors *and* by the half-sum row is zero unless the two vectors coincide. Here `N1, N2`
are the squared norms, `Q` the inner product, and `N1 + N2 − 2Q = ‖difference‖² > 0`. -/
private lemma kernel_pair_zero {g0 g1 N1 N2 Q : ℝ}
    (a1 : g0 * N1 + g1 * Q = 0) (a2 : g0 * Q + g1 * N2 = 0)
    (a3 : g0 * N1 + g1 * N2 = 0)
    (hN1 : 0 < N1) (hN2 : 0 < N2) (hD : 0 < N1 + N2 - 2*Q) :
    g0 = 0 ∧ g1 = 0 := by
  by_cases h0 : g0 = 0
  · subst h0
    simp only [zero_mul, zero_add] at a3
    rcases mul_eq_zero.mp a3 with h | h
    · exact ⟨rfl, h⟩
    · linarith
  · exfalso
    have e1 : g0 * (Q - N1) = 0 := by linear_combination a2 - a3
    have hQ1 : Q = N1 := by
      rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h h0
      · linarith
    by_cases h1 : g1 = 0
    · subst h1
      simp only [zero_mul, add_zero] at a3
      rcases mul_eq_zero.mp a3 with h | h
      · exact h0 h
      · linarith
    · have e2 : g1 * (Q - N2) = 0 := by linear_combination a1 - a3
      have hQ2 : Q = N2 := by
        rcases mul_eq_zero.mp e2 with h | h
        · exact absurd h h1
        · linarith
      linarith

open scoped Classical in
/-- **Three distinct particles have at most two common neighbours.** The set of points at
unit distance from three distinct points of `ℝ³` is a line intersected with a sphere.
Formally: differences of common neighbours are orthogonal to `b − a` and `c − a`, so a
nontrivial relation among the four vectors `b − a, c − a, w₂ − w₁, w₃ − w₁` (four vectors
in three dimensions) splits into two vanishing halves; the Gram kernel of either half
collapses two of the five points, contradicting distinctness. No hard-core hypothesis is
needed. -/
theorem common_neighbors_triple_le_two (X : Finset E3) {a b c : E3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (neighbors X a ∩ (neighbors X b ∩ neighbors X c)).card ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ (neighbors X a ∩ (neighbors X b ∩ neighbors X c)).card by omega)
  obtain ⟨w1, w2, w3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hT3
  -- unit-distance data for the three common neighbours
  have hunit : ∀ w ∈ neighbors X a ∩ (neighbors X b ∩ neighbors X c),
      ‖w - a‖ = 1 ∧ ‖w - b‖ = 1 ∧ ‖w - c‖ = 1 := by
    intro w hw
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hw
    obtain ⟨h2, h3⟩ := Finset.mem_inter.mp h2
    refine ⟨?_, ?_, ?_⟩
    · rw [← (Finset.mem_filter.mp h1).2, dist_eq_norm, norm_sub_rev]
    · rw [← (Finset.mem_filter.mp h2).2, dist_eq_norm, norm_sub_rev]
    · rw [← (Finset.mem_filter.mp h3).2, dist_eq_norm, norm_sub_rev]
  have hw1 := hunit w1 (hTsub (by simp))
  have hw2 := hunit w2 (hTsub (by simp))
  have hw3 := hunit w3 (hTsub (by simp))
  -- the half-distance relation: a common neighbour sees each bond vector at half its norm
  have hhalf : ∀ w d : E3, ‖w - a‖ = 1 → ‖w - d‖ = 1 →
      inner ℝ (w - a) (d - a) = ‖d - a‖ ^ 2 / 2 := by
    intro w d hwa hwd
    have key := norm_sub_sq_real (w - a) (d - a)
    rw [show (w - a) - (d - a) = w - d by abel, hwd, hwa] at key
    norm_num at key
    linarith
  -- differences of common neighbours are orthogonal to the bond vectors
  have horth : ∀ d w w' : E3, ‖w - a‖ = 1 → ‖w - d‖ = 1 → ‖w' - a‖ = 1 → ‖w' - d‖ = 1 →
      inner ℝ (d - a) (w - w') = 0 := by
    intro d w w' hwa hwd hw'a hw'd
    have h1 := hhalf w d hwa hwd
    have h2 := hhalf w' d hw'a hw'd
    have hsplit : inner ℝ (d - a) (w - w')
        = inner ℝ (w - a) (d - a) - inner ℝ (w' - a) (d - a) := by
      rw [← inner_sub_left, real_inner_comm]
      congr 1
      abel
    rw [hsplit, h1, h2]
    ring
  have hn1u : inner ℝ (b - a) (w2 - w1) = 0 :=
    horth b w2 w1 hw2.1 hw2.2.1 hw1.1 hw1.2.1
  have hn2u : inner ℝ (c - a) (w2 - w1) = 0 :=
    horth c w2 w1 hw2.1 hw2.2.2 hw1.1 hw1.2.2
  have hn1v : inner ℝ (b - a) (w3 - w1) = 0 :=
    horth b w3 w1 hw3.1 hw3.2.1 hw1.1 hw1.2.1
  have hn2v : inner ℝ (c - a) (w3 - w1) = 0 :=
    horth c w3 w1 hw3.1 hw3.2.2 hw1.1 hw1.2.2
  -- equal norms from `a` control the inner product of a difference with `w1 − a`
  have hself : ∀ w : E3, ‖w - a‖ = 1 →
      2 * inner ℝ (w - w1) (w1 - a) = -(‖w - w1‖ ^ 2) := by
    intro w hwa
    have key := norm_add_sq_real (w1 - a) (w - w1)
    rw [show (w1 - a) + (w - w1) = w - a by abel, hwa, hw1.1] at key
    norm_num at key
    have hc := real_inner_comm (w - w1) (w1 - a)
    linarith
  have hsu := hself w2 hw2.1
  have hsv := hself w3 hw3.1
  -- four vectors in three dimensions are dependent
  set q : Fin 4 → E3 := ![b - a, c - a, w2 - w1, w3 - w1] with hqdef
  have hdep : ¬ LinearIndependent ℝ q := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [finrank_euclideanSpace_fin] at this
    simp at this
  obtain ⟨g, hg0, i₀, hgi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hg0' : g 0 • (b - a) + g 1 • (c - a) + g 2 • (w2 - w1) + g 3 • (w3 - w1) = 0 := by
    have h := hg0
    simp only [Fin.sum_univ_four, hqdef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Matrix.head_fin_const] at h
    convert h using 2
  -- the relation splits: the two halves are orthogonal, so each vanishes
  have hgrp : (g 0 • (b - a) + g 1 • (c - a)) + (g 2 • (w2 - w1) + g 3 • (w3 - w1)) = 0 := by
    rw [← add_assoc]
    exact hg0'
  have hsr : (inner ℝ (g 0 • (b - a) + g 1 • (c - a))
      (g 2 • (w2 - w1) + g 3 • (w3 - w1)) : ℝ) = 0 := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hn1u, hn2u, hn1v, hn2v, mul_zero, add_zero]
  have hs0 : g 0 • (b - a) + g 1 • (c - a) = 0 := by
    have hseq : g 0 • (b - a) + g 1 • (c - a)
        = -(g 2 • (w2 - w1) + g 3 • (w3 - w1)) := by
      rw [add_eq_zero_iff_eq_neg] at hgrp
      exact hgrp
    have hz : (inner ℝ (g 0 • (b - a) + g 1 • (c - a))
        (g 0 • (b - a) + g 1 • (c - a)) : ℝ) = 0 := by
      nth_rewrite 2 [hseq]
      rw [inner_neg_right, hsr, neg_zero]
    exact inner_self_eq_zero.mp hz
  have hr0 : g 2 • (w2 - w1) + g 3 • (w3 - w1) = 0 := by
    rw [hs0, zero_add] at hgrp
    exact hgrp
  -- Gram rows of the first half
  have a1 : g 0 * ‖b - a‖ ^ 2 + g 1 * inner ℝ (b - a) (c - a) = 0 := by
    have h := congrArg (fun x : E3 => (inner ℝ x (b - a) : ℝ)) hs0
    simpa [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_comm (c - a) (b - a)] using h
  have a2 : g 0 * inner ℝ (b - a) (c - a) + g 1 * ‖c - a‖ ^ 2 = 0 := by
    have h := congrArg (fun x : E3 => (inner ℝ x (c - a) : ℝ)) hs0
    simpa [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] using h
  have hhb := hhalf w1 b hw1.1 hw1.2.1
  have hhc := hhalf w1 c hw1.1 hw1.2.2
  have a3 : g 0 * ‖b - a‖ ^ 2 + g 1 * ‖c - a‖ ^ 2 = 0 := by
    have h := congrArg (fun x : E3 => (inner ℝ x (w1 - a) : ℝ)) hs0
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at h
    rw [real_inner_comm (w1 - a) (b - a), real_inner_comm (w1 - a) (c - a), hhb, hhc] at h
    linear_combination 2 * h
  -- Gram rows of the second half
  have b1 : g 2 * ‖w2 - w1‖ ^ 2 + g 3 * inner ℝ (w2 - w1) (w3 - w1) = 0 := by
    have h := congrArg (fun x : E3 => (inner ℝ x (w2 - w1) : ℝ)) hr0
    simpa [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_comm (w3 - w1) (w2 - w1)] using h
  have b2 : g 2 * inner ℝ (w2 - w1) (w3 - w1) + g 3 * ‖w3 - w1‖ ^ 2 = 0 := by
    have h := congrArg (fun x : E3 => (inner ℝ x (w3 - w1) : ℝ)) hr0
    simpa [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] using h
  have b3 : g 2 * ‖w2 - w1‖ ^ 2 + g 3 * ‖w3 - w1‖ ^ 2 = 0 := by
    have h := congrArg (fun x : E3 => (inner ℝ x (w1 - a) : ℝ)) hr0
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at h
    linear_combination g 2 * hsu + g 3 * hsv - 2 * h
  -- positivity of the degeneracy witnesses
  have hN1 : 0 < ‖b - a‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))) 2
  have hN2 : 0 < ‖c - a‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hac))) 2
  have hU : 0 < ‖w2 - w1‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h12))) 2
  have hV : 0 < ‖w3 - w1‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h13))) 2
  have hDs : 0 < ‖b - a‖ ^ 2 + ‖c - a‖ ^ 2 - 2 * inner ℝ (b - a) (c - a) := by
    have hkey := norm_sub_sq_real (b - a) (c - a)
    rw [show (b - a) - (c - a) = b - c by abel] at hkey
    have hpos : 0 < ‖b - c‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hbc)) 2
    linarith
  have hDr : 0 < ‖w2 - w1‖ ^ 2 + ‖w3 - w1‖ ^ 2 - 2 * inner ℝ (w2 - w1) (w3 - w1) := by
    have hkey := norm_sub_sq_real (w2 - w1) (w3 - w1)
    rw [show (w2 - w1) - (w3 - w1) = w2 - w3 by abel] at hkey
    have hpos : 0 < ‖w2 - w3‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h23)) 2
    linarith
  -- both halves have trivial kernel: every coefficient vanishes
  obtain ⟨hg0z, hg1z⟩ := kernel_pair_zero a1 a2 a3 hN1 hN2 hDs
  obtain ⟨hg2z, hg3z⟩ := kernel_pair_zero b1 b2 b3 hU hV hDr
  have hall : ∀ i : Fin 4, g i = 0 := by
    intro i
    fin_cases i
    · exact hg0z
    · exact hg1z
    · exact hg2z
    · exact hg3z
  exact hgi₀ (hall i₀)

/-! ### The handshake parity -/

/-- A finset of pairs closed under swap and without diagonal elements has even
cardinality: remove a pair and its swap and induct. -/
lemma even_card_of_swap_closed {α : Type*} [DecidableEq α] (P : Finset (α × α))
    (hsymm : ∀ q ∈ P, Prod.swap q ∈ P) (hirr : ∀ q ∈ P, q.1 ≠ q.2) :
    Even P.card := by
  classical
  revert hsymm hirr
  induction P using Finset.strongInduction with
  | _ P ih =>
    intro hsymm hirr
    rcases P.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
    · simp
    · have hqs : Prod.swap q ∈ P := hsymm q hq
      have hqne : Prod.swap q ≠ q := by
        intro h
        have h1 : q.2 = q.1 := congrArg Prod.fst h
        exact hirr q hq h1.symm
      set P' : Finset (α × α) := (P.erase q).erase (Prod.swap q) with hP'
      have hsub : P' ⊂ P := by
        refine Finset.ssubset_iff_of_subset
          ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) |>.mpr ?_
        exact ⟨q, hq, fun hmem =>
          (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmem)) rfl⟩
      have hcard : P.card = P'.card + 2 := by
        rw [hP', Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨hqne, hqs⟩), Finset.card_erase_of_mem hq]
        have h1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨q, hq⟩
        have h2 : 2 ≤ P.card := by
          have := Finset.one_lt_card.mpr ⟨q, hq, Prod.swap q, hqs, hqne.symm⟩
          omega
        omega
      have hsymm' : ∀ r ∈ P', Prod.swap r ∈ P' := by
        intro r hr
        have hrq : r ≠ Prod.swap q := Finset.ne_of_mem_erase hr
        have hrq' : r ≠ q := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)
        have hrP : r ∈ P := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hsymm r hrP⟩⟩
        · intro h
          exact hrq' (by simpa using congrArg Prod.swap h)
        · intro h
          exact hrq (by simpa using congrArg Prod.swap h)
      have hirr' : ∀ r ∈ P', r.1 ≠ r.2 :=
        fun r hr => hirr r (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
      obtain ⟨k, hk⟩ := ih P' hsub hsymm' hirr'
      rw [hcard]
      exact ⟨k + 1, by omega⟩

open scoped Classical in
/-- **The handshake lemma**: `contactCount` is even — bonds come in ordered pairs. -/
theorem contactCount_even (X : Finset E3) : Even (contactCount X) := by
  set P : Finset (E3 × E3) := (X ×ˢ X).filter (fun q => dist q.1 q.2 = 1) with hP
  have hcc : contactCount X = P.card := by
    rw [contactCount, hP,
      Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := X)
        (fun q hq => (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1)]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hfib : ((X ×ˢ X).filter (fun q => dist q.1 q.2 = 1)).filter (fun q => q.1 = v)
        = {v} ×ˢ neighbors X v := by
      ext q
      simp only [neighbors, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨h4, h2, by rw [← h4]; exact h3⟩
      · rintro ⟨h4, h2, h3⟩
        exact ⟨⟨⟨by rw [h4]; exact hv, h2⟩, by rw [h4]; exact h3⟩, h4⟩
    rw [hfib, Finset.card_product, Finset.card_singleton, one_mul]
  rw [hcc]
  refine even_card_of_swap_closed P ?_ ?_
  · intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
    obtain ⟨h3, h4⟩ := Finset.mem_product.mp h1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨h4, h3⟩, by rw [Prod.snd_swap, Prod.fst_swap, dist_comm]; exact h2⟩
  · intro q hq
    have h2 := (Finset.mem_filter.mp hq).2
    intro h
    rw [h, dist_self] at h2
    norm_num at h2

end Kissing3D
