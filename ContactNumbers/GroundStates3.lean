import ContactNumbers.Contact3

set_option linter.style.header false
set_option maxHeartbeats 1000000

/-!
# Exact ground states for small `N`

The base cases of three-dimensional crystallization, exactly. For `N ≤ 4` the complete
contact graph is realisable (the regular tetrahedron), so `E_min(4) = −6`. For `N = 5` it
is not: **five points of `ℝ³` cannot be pairwise at distance one** — the regular 4-simplex
needs four dimensions (`pairwise_unit_card_le_four`, a rank argument: the four difference
vectors have Gram matrix `(I+J)/2 ≻ 0`). A degree count then forces `E_min(5) = −9`,
realised by the triangular bipyramid.

These appear to be the first machine-checked exact ground-state energies for the 3D
hard-core sticky-sphere model; informally such results rest on enumerative computation
(Arkus–Manoharan–Brenner). `E(N) = −(3N − 6)` continues through `N = 9` and first breaks
at `N = 10`; those cases need genuinely harder enumeration and are open here.
-/

namespace Kissing3D

open Finset

/-! ### No regular 4-simplex in three dimensions -/

/-- **At most four points of `ℝ³` are pairwise at distance one.** If there were five, the
four difference vectors from one of them would satisfy `⟨qᵢ,qᵢ⟩ = 1`, `⟨qᵢ,qⱼ⟩ = 1/2`; a
nontrivial linear relation `Σ gᵢ qᵢ = 0` (four vectors in three dimensions) then gives
`0 = ‖Σ gᵢ qᵢ‖² = ½ Σgᵢ² + ½ (Σgᵢ)² > 0`. -/
theorem pairwise_unit_card_le_four {S : Finset E3}
    (h : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → dist u v = 1) : S.card ≤ 4 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hTsub, hT5⟩ := Finset.exists_subset_card_eq (show 5 ≤ S.card from hcon)
  set e := T.equivFinOfCardEq hT5 with he
  set p : Fin 5 → E3 := fun i => ((e.symm i : T) : E3) with hp
  have hpmem : ∀ i, p i ∈ S := fun i => hTsub (e.symm i).2
  have hpinj : ∀ i j : Fin 5, i ≠ j → p i ≠ p j := by
    intro i j hij hpij
    exact hij (by simpa using e.symm.injective (Subtype.coe_injective hpij))
  have hpdist : ∀ i j : Fin 5, i ≠ j → dist (p i) (p j) = 1 :=
    fun i j hij => h _ (hpmem i) _ (hpmem j) (hpinj i j hij)
  -- the four difference vectors
  set q : Fin 4 → E3 := fun i => p i.succ - p 0 with hq
  have hqnorm : ∀ i, ‖q i‖ = 1 := by
    intro i
    rw [hq]
    simp only [← dist_eq_norm]
    exact hpdist _ _ (Fin.succ_ne_zero i)
  have hdiag : ∀ i, inner ℝ (q i) (q i) = (1:ℝ) := by
    intro i
    rw [real_inner_self_eq_norm_sq, hqnorm i]
    norm_num
  have hoff : ∀ i j : Fin 4, i ≠ j → inner ℝ (q i) (q j) = (1/2 : ℝ) := by
    intro i j hij
    have hsub : q i - q j = p i.succ - p j.succ := by
      rw [show q i = p i.succ - p 0 from rfl, show q j = p j.succ - p 0 from rfl]
      abel
    have hd : ‖q i - q j‖ = 1 := by
      rw [hsub, ← dist_eq_norm]
      exact hpdist _ _ (fun hs => hij (Fin.succ_injective _ hs))
    have hexp := norm_sub_sq_real (q i) (q j)
    rw [hd, hqnorm i, hqnorm j] at hexp
    norm_num at hexp
    linarith
  -- four vectors in three dimensions are dependent
  have hdep : ¬ LinearIndependent ℝ q := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [finrank_euclideanSpace_fin] at this
    simp at this
  obtain ⟨g, hg0, i₀, hgi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- expand `0 = ‖Σ gᵢ qᵢ‖²`
  have hzero : (inner ℝ (∑ i, g i • q i) (∑ i, g i • q i) : ℝ) = 0 := by
    rw [hg0, inner_zero_left]
  have hexp : (inner ℝ (∑ i, g i • q i) (∑ i, g i • q i) : ℝ)
      = ∑ i, ∑ j, g i * g j * inner ℝ (q i) (q j) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hexp] at hzero
  simp only [Fin.sum_univ_four] at hzero
  rw [hdiag 0, hdiag 1, hdiag 2, hdiag 3,
    hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 0 3 (by decide),
    hoff 1 0 (by decide), hoff 1 2 (by decide), hoff 1 3 (by decide),
    hoff 2 0 (by decide), hoff 2 1 (by decide), hoff 2 3 (by decide),
    hoff 3 0 (by decide), hoff 3 1 (by decide), hoff 3 2 (by decide)] at hzero
  -- `½Σg² + ½(Σg)² = 0` forces `g = 0`
  have hall : ∀ i : Fin 4, g i = 0 := by
    have h0 : g 0 ^ 2 = 0 := by
      nlinarith [hzero, sq_nonneg (g 0 + g 1 + g 2 + g 3),
        sq_nonneg (g 1), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h1 : g 1 ^ 2 = 0 := by
      nlinarith [hzero, sq_nonneg (g 0 + g 1 + g 2 + g 3),
        sq_nonneg (g 0), sq_nonneg (g 2), sq_nonneg (g 3)]
    have h2 : g 2 ^ 2 = 0 := by
      nlinarith [hzero, sq_nonneg (g 0 + g 1 + g 2 + g 3),
        sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 3)]
    have h3 : g 3 ^ 2 = 0 := by
      nlinarith [hzero, sq_nonneg (g 0 + g 1 + g 2 + g 3),
        sq_nonneg (g 0), sq_nonneg (g 1), sq_nonneg (g 2)]
    intro i
    fin_cases i
    · exact pow_eq_zero_iff two_ne_zero |>.mp h0
    · exact pow_eq_zero_iff two_ne_zero |>.mp h1
    · exact pow_eq_zero_iff two_ne_zero |>.mp h2
    · exact pow_eq_zero_iff two_ne_zero |>.mp h3
  exact hgi₀ (hall i₀)

/-! ### The trivial complete-graph bound -/

lemma neighbors_subset_erase (X : Finset E3) (v : E3) :
    neighbors X v ⊆ X.erase v := by
  intro u hu
  obtain ⟨huX, hd⟩ := Finset.mem_filter.mp hu
  refine Finset.mem_erase.mpr ⟨?_, huX⟩
  rintro rfl
  rw [dist_self] at hd
  norm_num at hd

/-- `E ≥ −N(N−1)/2` always: the contact graph has no more edges than the complete graph. -/
theorem energy_ge_complete_graph (X : Finset E3) :
    -((X.card : ℝ) * ((X.card : ℝ) - 1)) / 2 ≤ energy X := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · simp [energy, contactCount]
  have h1 : 1 ≤ X.card := Finset.card_pos.mpr hne
  have hcc : contactCount X ≤ X.card * (X.card - 1) := by
    rw [contactCount]
    calc ∑ z ∈ X, (neighbors X z).card
        ≤ ∑ z ∈ X, (X.card - 1) := by
          refine Finset.sum_le_sum fun z hz => ?_
          calc (neighbors X z).card ≤ (X.erase z).card :=
                Finset.card_le_card (neighbors_subset_erase X z)
            _ = X.card - 1 := Finset.card_erase_of_mem hz
      _ = X.card * (X.card - 1) := by rw [Finset.sum_const, smul_eq_mul]
  rw [energy]
  have hc : (contactCount X : ℝ) ≤ (X.card : ℝ) * ((X.card : ℝ) - 1) := by
    calc (contactCount X : ℝ) ≤ ((X.card * (X.card - 1) : ℕ) : ℝ) := by exact_mod_cast hcc
      _ = (X.card : ℝ) * ((X.card : ℝ) - 1) := by
          push_cast [Nat.cast_sub h1]
          ring
  linarith

/-- **`E_min(4) = −6`, the lower half**: four particles cannot beat the tetrahedron. -/
theorem energy_ge_four_particles {X : Finset E3} (h4 : X.card = 4) :
    -6 ≤ energy X := by
  have := energy_ge_complete_graph X
  rw [h4] at this
  norm_num at this
  linarith

/-! ### Five particles: the complete graph is out of reach -/

/-- **`E_min(5) = −9`, the lower half.** Ten bonds would mean five points pairwise at unit
distance; nineteen ordered contacts force every particle to be bonded to every other. -/
theorem energy_ge_five_particles {X : Finset E3} (h5 : X.card = 5) :
    -9 ≤ energy X := by
  classical
  have hdeg : ∀ v ∈ X, (neighbors X v).card ≤ 4 := by
    intro v hv
    calc (neighbors X v).card ≤ (X.erase v).card :=
          Finset.card_le_card (neighbors_subset_erase X v)
      _ = 4 := by rw [Finset.card_erase_of_mem hv, h5]
  -- nineteen ordered contacts are impossible
  have hcc : contactCount X ≤ 18 := by
    by_contra hcon
    push Not at hcon
    have h19 : 19 ≤ contactCount X := hcon
    -- every particle would have to be fully bonded
    have hall : ∀ v ∈ X, (neighbors X v).card = 4 := by
      intro v hv
      by_contra hne4
      have hv3 : (neighbors X v).card ≤ 3 := by
        have := hdeg v hv
        omega
      -- the other four each have degree 4, hence are bonded to `v`
      have heach : ∀ u ∈ X.erase v, (neighbors X u).card = 4 := by
        intro u hu
        by_contra hne4'
        have hu3 : (neighbors X u).card ≤ 3 := by
          have := hdeg u (Finset.mem_of_mem_erase hu)
          omega
        have hsplit : contactCount X
            = (neighbors X v).card + ∑ z ∈ X.erase v, (neighbors X z).card := by
          rw [contactCount, ← Finset.add_sum_erase X _ hv]
        have hsplit2 : ∑ z ∈ X.erase v, (neighbors X z).card
            = (neighbors X u).card + ∑ z ∈ (X.erase v).erase u, (neighbors X z).card := by
          rw [← Finset.add_sum_erase _ _ hu]
        have hrest : ∑ z ∈ (X.erase v).erase u, (neighbors X z).card ≤ 12 := by
          calc ∑ z ∈ (X.erase v).erase u, (neighbors X z).card
              ≤ ∑ _z ∈ (X.erase v).erase u, 4 :=
                Finset.sum_le_sum fun z hz => hdeg z
                  (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
            _ = 12 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem hu,
                  Finset.card_erase_of_mem hv, h5, smul_eq_mul]
        omega
      -- so `v` is bonded to all of them: contradiction with degree ≤ 3
      have hsub : X.erase v ⊆ neighbors X v := by
        intro u hu
        have hu4 := heach u hu
        have huX := Finset.mem_of_mem_erase hu
        have hfull : neighbors X u = X.erase u :=
          Finset.eq_of_subset_of_card_le (neighbors_subset_erase X u)
            (by rw [Finset.card_erase_of_mem huX, h5, hu4])
        have hvmem : v ∈ neighbors X u := by
          rw [hfull]
          exact Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hu).symm, hv⟩
        have hd : dist u v = 1 := (Finset.mem_filter.mp hvmem).2
        exact Finset.mem_filter.mpr ⟨huX, by rw [dist_comm]; exact hd⟩
      have : 4 ≤ (neighbors X v).card := by
        calc 4 = (X.erase v).card := by rw [Finset.card_erase_of_mem hv, h5]
          _ ≤ (neighbors X v).card := Finset.card_le_card hsub
      omega
    -- fully bonded means five points pairwise at distance one
    have hunit : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → dist u v = 1 := by
      intro u hu v hv huv
      have hfull : neighbors X u = X.erase u :=
        Finset.eq_of_subset_of_card_le (neighbors_subset_erase X u)
          (by rw [Finset.card_erase_of_mem hu, h5, hall u hu])
      have : v ∈ neighbors X u := by
        rw [hfull]
        exact Finset.mem_erase.mpr ⟨huv.symm, hv⟩
      exact (Finset.mem_filter.mp this).2
    have := pairwise_unit_card_le_four hunit
    omega
  rw [energy]
  have : (contactCount X : ℝ) ≤ 18 := by exact_mod_cast hcc
  linarith

/-! ### The realising configurations -/

noncomputable def gp0 : E3 := WithLp.toLp 2 ![0, 0, 0]
noncomputable def gp1 : E3 := WithLp.toLp 2 ![1, 0, 0]
noncomputable def gp2 : E3 := WithLp.toLp 2 ![1/2, Real.sqrt 3 / 2, 0]
noncomputable def gp3 : E3 := WithLp.toLp 2 ![1/2, Real.sqrt 3 / 6, Real.sqrt 6 / 3]
noncomputable def gp4 : E3 := WithLp.toLp 2 ![1/2, Real.sqrt 3 / 6, -(Real.sqrt 6 / 3)]

/-- The regular tetrahedron. -/
noncomputable def tetra : Finset E3 := {gp0, gp1, gp2, gp3}

/-- The triangular bipyramid: two tetrahedra glued along the face `gp0 gp1 gp2`. -/
noncomputable def bipyr : Finset E3 := {gp0, gp1, gp2, gp3, gp4}

lemma dist_coords (a b : E3) :
    dist a b = Real.sqrt ((a 0 - b 0)^2 + (a 1 - b 1)^2 + (a 2 - b 2)^2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Real.dist_eq, sq_abs]

section Distances

private lemma h3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma h6sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

lemma dist_gp01 : dist gp0 gp1 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 1)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - 0)^2) = 1
  rw [show ((0:ℝ) - 1)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 = 1 by norm_num]
  exact Real.sqrt_one

lemma dist_gp02 : dist gp0 gp2 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 2)^2 + ((0:ℝ) - 0)^2) = 1
  rw [show ((0:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 2)^2 + ((0:ℝ) - 0)^2 = 1 by
    linear_combination (1/4) * h3sq]
  exact Real.sqrt_one

lemma dist_gp12 : dist gp1 gp2 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((1:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 2)^2 + ((0:ℝ) - 0)^2) = 1
  rw [show ((1:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 2)^2 + ((0:ℝ) - 0)^2 = 1 by
    linear_combination (1/4) * h3sq]
  exact Real.sqrt_one

lemma dist_gp03 : dist gp0 gp3 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 6)^2
    + ((0:ℝ) - Real.sqrt 6 / 3)^2) = 1
  rw [show ((0:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 6)^2
      + ((0:ℝ) - Real.sqrt 6 / 3)^2 = 1 by
    linear_combination (1/36) * h3sq + (1/9) * h6sq]
  exact Real.sqrt_one

lemma dist_gp13 : dist gp1 gp3 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((1:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 6)^2
    + ((0:ℝ) - Real.sqrt 6 / 3)^2) = 1
  rw [show ((1:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 6)^2
      + ((0:ℝ) - Real.sqrt 6 / 3)^2 = 1 by
    linear_combination (1/36) * h3sq + (1/9) * h6sq]
  exact Real.sqrt_one

lemma dist_gp23 : dist gp2 gp3 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((1:ℝ)/2 - 1/2)^2 + (Real.sqrt 3 / 2 - Real.sqrt 3 / 6)^2
    + ((0:ℝ) - Real.sqrt 6 / 3)^2) = 1
  rw [show ((1:ℝ)/2 - 1/2)^2 + (Real.sqrt 3 / 2 - Real.sqrt 3 / 6)^2
      + ((0:ℝ) - Real.sqrt 6 / 3)^2 = 1 by
    linear_combination (1/9) * h3sq + (1/9) * h6sq]
  exact Real.sqrt_one

lemma dist_gp04 : dist gp0 gp4 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 6)^2
    + ((0:ℝ) - -(Real.sqrt 6 / 3))^2) = 1
  rw [show ((0:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 6)^2
      + ((0:ℝ) - -(Real.sqrt 6 / 3))^2 = 1 by
    linear_combination (1/36) * h3sq + (1/9) * h6sq]
  exact Real.sqrt_one

lemma dist_gp14 : dist gp1 gp4 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((1:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 6)^2
    + ((0:ℝ) - -(Real.sqrt 6 / 3))^2) = 1
  rw [show ((1:ℝ) - 1/2)^2 + ((0:ℝ) - Real.sqrt 3 / 6)^2
      + ((0:ℝ) - -(Real.sqrt 6 / 3))^2 = 1 by
    linear_combination (1/36) * h3sq + (1/9) * h6sq]
  exact Real.sqrt_one

lemma dist_gp24 : dist gp2 gp4 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((1:ℝ)/2 - 1/2)^2 + (Real.sqrt 3 / 2 - Real.sqrt 3 / 6)^2
    + ((0:ℝ) - -(Real.sqrt 6 / 3))^2) = 1
  rw [show ((1:ℝ)/2 - 1/2)^2 + (Real.sqrt 3 / 2 - Real.sqrt 3 / 6)^2
      + ((0:ℝ) - -(Real.sqrt 6 / 3))^2 = 1 by
    linear_combination (1/9) * h3sq + (1/9) * h6sq]
  exact Real.sqrt_one

/-- The apex pair of the bipyramid: distance `2√6/3 ≈ 1.63`, not bonded but hard-core. -/
lemma dist_gp34 : dist gp3 gp4 = Real.sqrt (8/3) := by
  rw [dist_coords]
  show Real.sqrt (((1:ℝ)/2 - 1/2)^2 + (Real.sqrt 3 / 6 - Real.sqrt 3 / 6)^2
    + (Real.sqrt 6 / 3 - -(Real.sqrt 6 / 3))^2) = Real.sqrt (8/3)
  rw [show ((1:ℝ)/2 - 1/2)^2 + (Real.sqrt 3 / 6 - Real.sqrt 3 / 6)^2
      + (Real.sqrt 6 / 3 - -(Real.sqrt 6 / 3))^2 = 8/3 by
    linear_combination (4/9) * h6sq]

lemma dist_gp34_ge : 1 ≤ dist gp3 gp4 := by
  rw [dist_gp34]
  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (by norm_num)

end Distances

/-- Distinctness, from nonzero distances. -/
private lemma ne_of_dist_one {a b : E3} (h : dist a b = 1) : a ≠ b := by
  rintro rfl
  rw [dist_self] at h
  norm_num at h

section Configs

private lemma hne01 : gp0 ≠ gp1 := ne_of_dist_one dist_gp01
private lemma hne02 : gp0 ≠ gp2 := ne_of_dist_one dist_gp02
private lemma hne03 : gp0 ≠ gp3 := ne_of_dist_one dist_gp03
private lemma hne04 : gp0 ≠ gp4 := ne_of_dist_one dist_gp04
private lemma hne12 : gp1 ≠ gp2 := ne_of_dist_one dist_gp12
private lemma hne13 : gp1 ≠ gp3 := ne_of_dist_one dist_gp13
private lemma hne14 : gp1 ≠ gp4 := ne_of_dist_one dist_gp14
private lemma hne23 : gp2 ≠ gp3 := ne_of_dist_one dist_gp23
private lemma hne24 : gp2 ≠ gp4 := ne_of_dist_one dist_gp24
private lemma hne34 : gp3 ≠ gp4 := by
  intro h
  have := dist_gp34_ge
  rw [h, dist_self] at this
  norm_num at this

/-- The ten pairwise distances of the bipyramid, symmetrised. -/
private lemma bipyr_dist : ∀ u ∈ bipyr, ∀ v ∈ bipyr, u ≠ v → 1 ≤ dist u v := by
  have key : ∀ a b : E3, dist a b = 1 → 1 ≤ dist a b ∧ 1 ≤ dist b a := by
    intro a b h
    constructor
    · rw [h]
    · rw [dist_comm, h]
  intro u hu v hv huv
  simp only [bipyr, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl huv
      | exact (key _ _ dist_gp01).1 | exact (key _ _ dist_gp01).2
      | exact (key _ _ dist_gp02).1 | exact (key _ _ dist_gp02).2
      | exact (key _ _ dist_gp03).1 | exact (key _ _ dist_gp03).2
      | exact (key _ _ dist_gp04).1 | exact (key _ _ dist_gp04).2
      | exact (key _ _ dist_gp12).1 | exact (key _ _ dist_gp12).2
      | exact (key _ _ dist_gp13).1 | exact (key _ _ dist_gp13).2
      | exact (key _ _ dist_gp14).1 | exact (key _ _ dist_gp14).2
      | exact (key _ _ dist_gp23).1 | exact (key _ _ dist_gp23).2
      | exact (key _ _ dist_gp24).1 | exact (key _ _ dist_gp24).2
      | exact dist_gp34_ge | (rw [dist_comm]; exact dist_gp34_ge)

theorem hardCore_bipyr : HardCore bipyr := bipyr_dist

theorem hardCore_tetra : HardCore tetra := by
  intro u hu v hv huv
  refine bipyr_dist u ?_ v ?_ huv <;>
  · simp only [tetra, bipyr, Finset.mem_insert, Finset.mem_singleton] at *
    tauto

theorem card_tetra : tetra.card = 4 := by
  rw [tetra]
  rw [Finset.card_insert_of_notMem (by simp [hne01, hne02, hne03]),
    Finset.card_insert_of_notMem (by simp [hne12, hne13]),
    Finset.card_insert_of_notMem (by simp [hne23]),
    Finset.card_singleton]

theorem card_bipyr : bipyr.card = 5 := by
  rw [bipyr]
  rw [Finset.card_insert_of_notMem (by simp [hne01, hne02, hne03, hne04]),
    Finset.card_insert_of_notMem (by simp [hne12, hne13, hne14]),
    Finset.card_insert_of_notMem (by simp [hne23, hne24]),
    Finset.card_insert_of_notMem (by simp [hne34]),
    Finset.card_singleton]

/-- A lower bound on a particle's degree from an explicit set of bonded partners. -/
private lemma le_card_neighbors {X : Finset E3} {v : E3} (B : Finset E3)
    (hB : ∀ u ∈ B, u ∈ X ∧ dist v u = 1) : B.card ≤ (neighbors X v).card := by
  refine Finset.card_le_card fun u hu => ?_
  obtain ⟨huX, hd⟩ := hB u hu
  exact Finset.mem_filter.mpr ⟨huX, hd⟩

theorem energy_tetra : energy tetra = -6 := by
  have hle : energy tetra ≤ -6 := by
    -- each vertex is bonded to the other three
    have hmem : ∀ p ∈ ({gp0, gp1, gp2, gp3} : Finset E3), p ∈ tetra := by
      intro p hp; exact hp
    have hdeg : ∀ v ∈ tetra, 3 ≤ (neighbors tetra v).card := by
      intro v hv
      simp only [tetra, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · refine le_trans (le_of_eq ?_) (le_card_neighbors {gp1, gp2, gp3} ?_)
        · rw [Finset.card_insert_of_notMem (by simp [hne12, hne13]),
            Finset.card_insert_of_notMem (by simp [hne23]), Finset.card_singleton]
        · intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact ⟨by simp [tetra], dist_gp01⟩
          · exact ⟨by simp [tetra], dist_gp02⟩
          · exact ⟨by simp [tetra], dist_gp03⟩
      · refine le_trans (le_of_eq ?_) (le_card_neighbors {gp0, gp2, gp3} ?_)
        · rw [Finset.card_insert_of_notMem (by simp [hne02, hne03]),
            Finset.card_insert_of_notMem (by simp [hne23]), Finset.card_singleton]
        · intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact ⟨by simp [tetra], by rw [dist_comm]; exact dist_gp01⟩
          · exact ⟨by simp [tetra], dist_gp12⟩
          · exact ⟨by simp [tetra], dist_gp13⟩
      · refine le_trans (le_of_eq ?_) (le_card_neighbors {gp0, gp1, gp3} ?_)
        · rw [Finset.card_insert_of_notMem (by simp [hne01, hne03]),
            Finset.card_insert_of_notMem (by simp [hne13]), Finset.card_singleton]
        · intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact ⟨by simp [tetra], by rw [dist_comm]; exact dist_gp02⟩
          · exact ⟨by simp [tetra], by rw [dist_comm]; exact dist_gp12⟩
          · exact ⟨by simp [tetra], dist_gp23⟩
      · refine le_trans (le_of_eq ?_) (le_card_neighbors {gp0, gp1, gp2} ?_)
        · rw [Finset.card_insert_of_notMem (by simp [hne01, hne02]),
            Finset.card_insert_of_notMem (by simp [hne12]), Finset.card_singleton]
        · intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact ⟨by simp [tetra], by rw [dist_comm]; exact dist_gp03⟩
          · exact ⟨by simp [tetra], by rw [dist_comm]; exact dist_gp13⟩
          · exact ⟨by simp [tetra], by rw [dist_comm]; exact dist_gp23⟩
    have hcc : 12 ≤ contactCount tetra := by
      rw [contactCount]
      calc (12 : ℕ) = ∑ _v ∈ tetra, 3 := by
            simp [card_tetra]
        _ ≤ ∑ v ∈ tetra, (neighbors tetra v).card := Finset.sum_le_sum hdeg
    rw [energy]
    have : (12 : ℝ) ≤ (contactCount tetra : ℝ) := by exact_mod_cast hcc
    linarith
  have hge := energy_ge_four_particles card_tetra
  linarith

theorem energy_bipyr : energy bipyr = -9 := by
  have hle : energy bipyr ≤ -9 := by
    -- degree 4 for the equator, 3 for the apexes
    have hd0 : 4 ≤ (neighbors bipyr gp0).card := by
      refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {gp1, gp2, gp3, gp4} ?_)
      · rw [Finset.card_insert_of_notMem (by simp [hne12, hne13, hne14]),
          Finset.card_insert_of_notMem (by simp [hne23, hne24]),
          Finset.card_insert_of_notMem (by simp [hne34]), Finset.card_singleton]
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨by simp [bipyr], dist_gp01⟩
        · exact ⟨by simp [bipyr], dist_gp02⟩
        · exact ⟨by simp [bipyr], dist_gp03⟩
        · exact ⟨by simp [bipyr], dist_gp04⟩
    have hd1 : 4 ≤ (neighbors bipyr gp1).card := by
      refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {gp0, gp2, gp3, gp4} ?_)
      · rw [Finset.card_insert_of_notMem (by simp [hne02, hne03, hne04]),
          Finset.card_insert_of_notMem (by simp [hne23, hne24]),
          Finset.card_insert_of_notMem (by simp [hne34]), Finset.card_singleton]
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨by simp [bipyr], by rw [dist_comm]; exact dist_gp01⟩
        · exact ⟨by simp [bipyr], dist_gp12⟩
        · exact ⟨by simp [bipyr], dist_gp13⟩
        · exact ⟨by simp [bipyr], dist_gp14⟩
    have hd2 : 4 ≤ (neighbors bipyr gp2).card := by
      refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {gp0, gp1, gp3, gp4} ?_)
      · rw [Finset.card_insert_of_notMem (by simp [hne01, hne03, hne04]),
          Finset.card_insert_of_notMem (by simp [hne13, hne14]),
          Finset.card_insert_of_notMem (by simp [hne34]), Finset.card_singleton]
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl | rfl
        · exact ⟨by simp [bipyr], by rw [dist_comm]; exact dist_gp02⟩
        · exact ⟨by simp [bipyr], by rw [dist_comm]; exact dist_gp12⟩
        · exact ⟨by simp [bipyr], dist_gp23⟩
        · exact ⟨by simp [bipyr], dist_gp24⟩
    have hd3 : 3 ≤ (neighbors bipyr gp3).card := by
      refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {gp0, gp1, gp2} ?_)
      · rw [Finset.card_insert_of_notMem (by simp [hne01, hne02]),
          Finset.card_insert_of_notMem (by simp [hne12]), Finset.card_singleton]
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact ⟨by simp [bipyr], by rw [dist_comm]; exact dist_gp03⟩
        · exact ⟨by simp [bipyr], by rw [dist_comm]; exact dist_gp13⟩
        · exact ⟨by simp [bipyr], by rw [dist_comm]; exact dist_gp23⟩
    have hd4 : 3 ≤ (neighbors bipyr gp4).card := by
      refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {gp0, gp1, gp2} ?_)
      · rw [Finset.card_insert_of_notMem (by simp [hne01, hne02]),
          Finset.card_insert_of_notMem (by simp [hne12]), Finset.card_singleton]
      · intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact ⟨by simp [bipyr], by rw [dist_comm]; exact dist_gp04⟩
        · exact ⟨by simp [bipyr], by rw [dist_comm]; exact dist_gp14⟩
        · exact ⟨by simp [bipyr], by rw [dist_comm]; exact dist_gp24⟩
    have hcc : 18 ≤ contactCount bipyr := by
      rw [contactCount, bipyr]
      rw [Finset.sum_insert (by simp [hne01, hne02, hne03, hne04]),
        Finset.sum_insert (by simp [hne12, hne13, hne14]),
        Finset.sum_insert (by simp [hne23, hne24]),
        Finset.sum_insert (by simp [hne34]),
        Finset.sum_singleton]
      have h0 := hd0; have h1 := hd1; have h2 := hd2; have h3 := hd3; have h4 := hd4
      simp only [show ({gp0, gp1, gp2, gp3, gp4} : Finset E3) = bipyr from rfl]
      omega
    rw [energy]
    have : (18 : ℝ) ≤ (contactCount bipyr : ℝ) := by exact_mod_cast hcc
    linarith
  have hge := energy_ge_five_particles card_bipyr
  linarith

/-- **`E_min(4) = −6`**: the regular tetrahedron is the four-particle ground state. -/
theorem groundState_four :
    (∀ X : Finset E3, X.card = 4 → -6 ≤ energy X) ∧
    HardCore tetra ∧ tetra.card = 4 ∧ energy tetra = -6 :=
  ⟨fun _ h => energy_ge_four_particles h, hardCore_tetra, card_tetra, energy_tetra⟩

/-- **`E_min(5) = −9`**: the triangular bipyramid is the five-particle ground state. The
complete graph on five vertices is excluded by `pairwise_unit_card_le_four` — the first
`N` at which geometry, not counting, limits the energy. -/
theorem groundState_five :
    (∀ X : Finset E3, X.card = 5 → -9 ≤ energy X) ∧
    HardCore bipyr ∧ bipyr.card = 5 ∧ energy bipyr = -9 :=
  ⟨fun _ h => energy_ge_five_particles h, hardCore_bipyr, card_bipyr, energy_bipyr⟩

end Configs

/-! ### Six particles: the ring around a bonded pair

The recentring of `common_neighbors_le_five`, packaged: the common neighbours of a bonded
pair live on a circle in the bond's perpendicular bisector plane, and all their `dot3`
data is determined by mutual distances. -/

open scoped Classical in
lemma ring_data {X : Finset E3} {e f : E3} (hef : dist e f = 1) :
    ∃ (p : Fin 3 → ℝ) (z : E3 → Fin 3 → ℝ), dot3 p p = 1 ∧
      ∀ u ∈ neighbors X e ∩ neighbors X f, dot3 p (z u) = 0 ∧
        ∀ u' ∈ neighbors X e ∩ neighbors X f,
          dot3 (z u) (z u') = 3/4 - dist u u' ^ 2 / 2 := by
  set sh : E3 → E3 := fun u => u - e - (2⁻¹ : ℝ) • (f - e) with hsh
  have hq : ‖f - e‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hef
  have hmem : ∀ u ∈ neighbors X e ∩ neighbors X f, ‖u - e‖ = 1 ∧ ‖u - f‖ = 1 := by
    intro u hu
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hu
    exact ⟨by rw [← (Finset.mem_filter.mp h1).2, dist_eq_norm, norm_sub_rev],
      by rw [← (Finset.mem_filter.mp h2).2, dist_eq_norm, norm_sub_rev]⟩
  have hip : ∀ u ∈ neighbors X e ∩ neighbors X f,
      inner ℝ (u - e) (f - e) = (2⁻¹ : ℝ) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hmem u hu
    have e1 : ‖(u - e) - (f - e)‖ = 1 := by
      rw [show (u - e) - (f - e) = u - f by abel]; exact h2
    have e2 := norm_sub_sq_real (u - e) (f - e)
    rw [e1, h1, hq] at e2
    norm_num at e2
    linarith
  have hnormsh : ∀ u ∈ neighbors X e ∩ neighbors X f, ‖sh u‖ ^ 2 = 3/4 := by
    intro u hu
    have h1 : inner ℝ (u - e) ((2⁻¹ : ℝ) • (f - e)) = (4⁻¹ : ℝ) := by
      rw [real_inner_smul_right, hip u hu]; norm_num
    have h2 : ‖(2⁻¹ : ℝ) • (f - e)‖ ^ 2 = (4⁻¹ : ℝ) := by
      rw [norm_smul, hq, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
      norm_num
    have h3 := norm_sub_sq_real (u - e) ((2⁻¹ : ℝ) • (f - e))
    rw [h1, h2, (hmem u hu).1] at h3
    simp only [hsh]
    rw [h3]
    norm_num
  have hshsub : ∀ a b : E3, sh a - sh b = a - b := by
    intro a b; simp only [hsh]; abel
  refine ⟨WithLp.ofLp (f - e), fun u => WithLp.ofLp (sh u), dot3_self_of_norm hq,
    fun u hu => ⟨?_, fun u' hu' => ?_⟩⟩
  · rw [dot3_eq_inner]
    have h1 : inner ℝ (f - e) ((2⁻¹ : ℝ) • (f - e)) = (2⁻¹ : ℝ) := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hq]; norm_num
    have h2 : inner ℝ (f - e) (u - e) = (2⁻¹ : ℝ) := by
      rw [real_inner_comm]; exact hip u hu
    simp only [hsh]
    rw [inner_sub_right, h1, h2]
    ring
  · rw [dot3_eq_inner]
    have hpol := norm_sub_sq_real (sh u) (sh u')
    rw [hshsub u u', ← dist_eq_norm, hnormsh u hu, hnormsh u' hu'] at hpol
    linarith

/-- Three pairwise-bonded common neighbours of a bonded pair are impossible. -/
lemma common_triangle_impossible {X : Finset E3} {e f a b c : E3} (hef : dist e f = 1)
    (ha : a ∈ neighbors X e ∩ neighbors X f) (hb : b ∈ neighbors X e ∩ neighbors X f)
    (hc : c ∈ neighbors X e ∩ neighbors X f)
    (hab : dist a b = 1) (hac : dist a c = 1) (hbc : dist b c = 1) : False := by
  obtain ⟨p, z, hp, hdata⟩ := ring_data (X := X) hef
  obtain ⟨hpa, hcra⟩ := hdata a ha
  obtain ⟨hpb, hcrb⟩ := hdata b hb
  obtain ⟨hpc, hcrc⟩ := hdata c hc
  refine ring_no_triangle hp hpa hpb hpc ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hcra a ha, dist_self]; norm_num
  · rw [hcrb b hb, dist_self]; norm_num
  · rw [hcrc c hc, dist_self]; norm_num
  · rw [hcra b hb, hab]; norm_num
  · rw [hcra c hc, hac]; norm_num
  · rw [hcrb c hc, hbc]; norm_num

/-- A perfect bond four-cycle `a–c, a–d, b–c, b–d` among four distinct common neighbours
of a bonded pair is impossible. -/
lemma common_square_impossible {X : Finset E3} (hX : HardCore X) {e f a b c d : E3}
    (hef : dist e f = 1)
    (ha : a ∈ neighbors X e ∩ neighbors X f) (hb : b ∈ neighbors X e ∩ neighbors X f)
    (hc : c ∈ neighbors X e ∩ neighbors X f) (hd : d ∈ neighbors X e ∩ neighbors X f)
    (hne_ab : a ≠ b) (hne_cd : c ≠ d)
    (hac : dist a c = 1) (had : dist a d = 1) (hbc : dist b c = 1) (hbd : dist b d = 1) :
    False := by
  have hXmem : ∀ u ∈ neighbors X e ∩ neighbors X f, u ∈ X :=
    fun u hu => (Finset.mem_filter.mp (Finset.mem_inter.mp hu).1).1
  obtain ⟨p, z, hp, hdata⟩ := ring_data (X := X) hef
  obtain ⟨hpa, hcra⟩ := hdata a ha
  obtain ⟨hpb, hcrb⟩ := hdata b hb
  obtain ⟨hpc, hcrc⟩ := hdata c hc
  obtain ⟨hpd, hcrd⟩ := hdata d hd
  have hhc : ∀ {u v : E3}, u ∈ X → v ∈ X → u ≠ v → (1:ℝ) ≤ dist u v ^ 2 := by
    intro u v hu hv huv
    have h1 := hX u hu v hv huv
    nlinarith [dist_nonneg (x := u) (y := v)]
  refine ring_no_square hp hpa hpb hpc hpd ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hcra a ha, dist_self]; norm_num
  · rw [hcrb b hb, dist_self]; norm_num
  · rw [hcrc c hc, dist_self]; norm_num
  · rw [hcrd d hd, dist_self]; norm_num
  · rw [hcra c hc, hac]; norm_num
  · rw [hcra d hd, had]; norm_num
  · rw [hcrb c hc, hbc]; norm_num
  · rw [hcrb d hd, hbd]; norm_num
  · rw [hcra b hb]
    linarith [hhc (hXmem a ha) (hXmem b hb) hne_ab]
  · rw [hcrc d hd]
    linarith [hhc (hXmem c hc) (hXmem d hd) hne_cd]

/-- A common neighbour of a bonded pair cannot be bonded to three further distinct common
neighbours: the ring contact graph has maximum degree two. -/
lemma common_degree_impossible {X : Finset E3} (hX : HardCore X) {e f c x y z : E3}
    (hef : dist e f = 1)
    (hc : c ∈ neighbors X e ∩ neighbors X f) (hx : x ∈ neighbors X e ∩ neighbors X f)
    (hy : y ∈ neighbors X e ∩ neighbors X f) (hz : z ∈ neighbors X e ∩ neighbors X f)
    (hne_xy : x ≠ y) (hne_xz : x ≠ z) (hne_yz : y ≠ z)
    (hcx : dist c x = 1) (hcy : dist c y = 1) (hcz : dist c z = 1) : False := by
  have hXmem : ∀ u ∈ neighbors X e ∩ neighbors X f, u ∈ X :=
    fun u hu => (Finset.mem_filter.mp (Finset.mem_inter.mp hu).1).1
  obtain ⟨p, zz, hp, hdata⟩ := ring_data (X := X) hef
  obtain ⟨hpc, hcrc⟩ := hdata c hc
  obtain ⟨hpx, hcrx⟩ := hdata x hx
  obtain ⟨hpy, hcry⟩ := hdata y hy
  obtain ⟨hpz, hcrz⟩ := hdata z hz
  have hhc : ∀ {u v : E3}, u ∈ X → v ∈ X → u ≠ v → (1:ℝ) ≤ dist u v ^ 2 := by
    intro u v hu hv huv
    have h1 := hX u hu v hv huv
    nlinarith [dist_nonneg (x := u) (y := v)]
  refine ring_degree_le_two hp hpc hpx hpy hpz ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hcrc c hc, dist_self]; norm_num
  · rw [hcrx x hx, dist_self]; norm_num
  · rw [hcry y hy, dist_self]; norm_num
  · rw [hcrz z hz, dist_self]; norm_num
  · rw [hcrc x hx, hcx]; norm_num
  · rw [hcrc y hy, hcy]; norm_num
  · rw [hcrc z hz, hcz]; norm_num
  · rw [hcrx y hy]; linarith [hhc (hXmem x hx) (hXmem y hy) hne_xy]
  · rw [hcrx z hz]; linarith [hhc (hXmem x hx) (hXmem z hz) hne_xz]
  · rw [hcry z hz]; linarith [hhc (hXmem y hy) (hXmem z hz) hne_yz]

/-- A five-cycle of bonds among common neighbours of a bonded pair is impossible. Only
the two skew pairs at `z1` need to be distinct — the hard core turns them into the
`≤ 1/4` hypotheses of `ring_no_pentagon`. -/
lemma common_pentagon_impossible {X : Finset E3} (hX : HardCore X)
    {e f z1 z2 z3 z4 z5 : E3} (hef : dist e f = 1)
    (h1 : z1 ∈ neighbors X e ∩ neighbors X f) (h2 : z2 ∈ neighbors X e ∩ neighbors X f)
    (h3 : z3 ∈ neighbors X e ∩ neighbors X f) (h4 : z4 ∈ neighbors X e ∩ neighbors X f)
    (h5 : z5 ∈ neighbors X e ∩ neighbors X f)
    (hne13 : z1 ≠ z3) (hne14 : z1 ≠ z4)
    (h12 : dist z1 z2 = 1) (h23 : dist z2 z3 = 1) (h34 : dist z3 z4 = 1)
    (h45 : dist z4 z5 = 1) (h51 : dist z5 z1 = 1) : False := by
  have hXmem : ∀ u ∈ neighbors X e ∩ neighbors X f, u ∈ X :=
    fun u hu => (Finset.mem_filter.mp (Finset.mem_inter.mp hu).1).1
  obtain ⟨p, zz, hp, hdata⟩ := ring_data (X := X) hef
  obtain ⟨hp1, hcr1⟩ := hdata z1 h1
  obtain ⟨hp2, hcr2⟩ := hdata z2 h2
  obtain ⟨hp3, hcr3⟩ := hdata z3 h3
  obtain ⟨hp4, hcr4⟩ := hdata z4 h4
  obtain ⟨hp5, hcr5⟩ := hdata z5 h5
  have hhc : ∀ {u v : E3}, u ∈ X → v ∈ X → u ≠ v → (1:ℝ) ≤ dist u v ^ 2 := by
    intro u v hu hv huv
    have h1 := hX u hu v hv huv
    nlinarith [dist_nonneg (x := u) (y := v)]
  refine ring_no_pentagon hp hp1 hp2 hp3 hp4 hp5
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hcr1 z1 h1, dist_self]; norm_num
  · rw [hcr2 z2 h2, dist_self]; norm_num
  · rw [hcr3 z3 h3, dist_self]; norm_num
  · rw [hcr4 z4 h4, dist_self]; norm_num
  · rw [hcr5 z5 h5, dist_self]; norm_num
  · rw [hcr1 z2 h2, h12]; norm_num
  · rw [hcr2 z3 h3, h23]; norm_num
  · rw [hcr3 z4 h4, h34]; norm_num
  · rw [hcr4 z5 h5, h45]; norm_num
  · rw [hcr5 z1 h1, h51]; norm_num
  · rw [hcr1 z3 h3]; linarith [hhc (hXmem z1 h1) (hXmem z3 h3) hne13]
  · rw [hcr1 z4 h4]; linarith [hhc (hXmem z1 h1) (hXmem z4 h4) hne14]

/-- **`E_min(6) = −12`, the lower half.** Twenty-six ordered contacts force two fully
bonded particles `e, f`; their four common neighbours then carry at least four bonds
among themselves, hence a triangle or a perfect four-cycle on the ring — both impossible.
The count `25` is excluded by the handshake parity. -/
theorem energy_ge_six_particles {X : Finset E3} (hX : HardCore X) (h6 : X.card = 6) :
    -12 ≤ energy X := by
  classical
  have hdeg : ∀ v ∈ X, (neighbors X v).card ≤ 5 := by
    intro v hv
    calc (neighbors X v).card ≤ (X.erase v).card :=
          Finset.card_le_card (neighbors_subset_erase X v)
      _ = 5 := by rw [Finset.card_erase_of_mem hv, h6]
  have hcc : contactCount X ≤ 24 := by
    by_contra hcon
    push Not at hcon
    have h26 : 26 ≤ contactCount X := by
      obtain ⟨k, hk⟩ := contactCount_even X
      omega
    -- a fully bonded particle
    have he : ∃ e ∈ X, (neighbors X e).card = 5 := by
      by_contra hno
      push Not at hno
      have : contactCount X ≤ 24 := by
        rw [contactCount]
        calc ∑ z ∈ X, (neighbors X z).card ≤ ∑ _z ∈ X, 4 := by
              refine Finset.sum_le_sum fun z hz => ?_
              have := hdeg z hz
              have := hno z hz
              omega
          _ = 24 := by rw [Finset.sum_const, h6, smul_eq_mul]
      omega
    obtain ⟨e, heX, hdege⟩ := he
    -- a second one
    have hf : ∃ g ∈ X.erase e, (neighbors X g).card = 5 := by
      by_contra hno
      push Not at hno
      have hsum : ∑ z ∈ X.erase e, (neighbors X z).card ≤ 20 := by
        calc ∑ z ∈ X.erase e, (neighbors X z).card ≤ ∑ _z ∈ X.erase e, 4 := by
              refine Finset.sum_le_sum fun z hz => ?_
              have := hdeg z (Finset.mem_of_mem_erase hz)
              have := hno z hz
              omega
          _ = 20 := by
              rw [Finset.sum_const, Finset.card_erase_of_mem heX, h6, smul_eq_mul]
      have hsplit : contactCount X
          = (neighbors X e).card + ∑ z ∈ X.erase e, (neighbors X z).card := by
        rw [contactCount, ← Finset.add_sum_erase X _ heX]
      omega
    obtain ⟨f, hfE, hdegf⟩ := hf
    have hfX : f ∈ X := Finset.mem_of_mem_erase hfE
    have hfe : f ≠ e := Finset.ne_of_mem_erase hfE
    -- both are bonded to everything
    have hfulle : neighbors X e = X.erase e :=
      Finset.eq_of_subset_of_card_le (neighbors_subset_erase X e)
        (by rw [Finset.card_erase_of_mem heX, h6, hdege])
    have hfullf : neighbors X f = X.erase f :=
      Finset.eq_of_subset_of_card_le (neighbors_subset_erase X f)
        (by rw [Finset.card_erase_of_mem hfX, h6, hdegf])
    have hef : dist e f = 1 := by
      have : f ∈ neighbors X e := by rw [hfulle]; exact hfE
      exact (Finset.mem_filter.mp this).2
    -- the four common neighbours
    set Y : Finset E3 := (X.erase e).erase f with hY
    have hYcard : Y.card = 4 := by
      rw [hY, Finset.card_erase_of_mem hfE, Finset.card_erase_of_mem heX, h6]
    have hYX : ∀ u ∈ Y, u ∈ X :=
      fun u hu => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hu)
    have hYne : ∀ u ∈ Y, u ≠ e ∧ u ≠ f := fun u hu =>
      ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hu), Finset.ne_of_mem_erase hu⟩
    have hYC : ∀ u ∈ Y, u ∈ neighbors X e ∩ neighbors X f := by
      intro u hu
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · rw [hfulle]; exact Finset.mem_of_mem_erase hu
      · rw [hfullf]
        exact Finset.mem_erase.mpr ⟨(hYne u hu).2, hYX u hu⟩
    -- membership of `e, f` in every `Y`-particle's neighbourhood
    have hefY : ∀ u ∈ Y, e ∈ neighbors X u ∧ f ∈ neighbors X u := by
      intro u hu
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp (hYC u hu)
      exact ⟨Finset.mem_filter.mpr ⟨heX, by
          rw [dist_comm]; exact (Finset.mem_filter.mp h1).2⟩,
        Finset.mem_filter.mpr ⟨hfX, by
          rw [dist_comm]; exact (Finset.mem_filter.mp h2).2⟩⟩
    -- the `Y`-degree sum
    have hsplit : contactCount X
        = 5 + (5 + ∑ u ∈ Y, (neighbors X u).card) := by
      rw [contactCount, ← Finset.add_sum_erase X _ heX, hdege,
        ← Finset.add_sum_erase _ _ hfE, hdegf]
    have hsumY : 16 ≤ ∑ u ∈ Y, (neighbors X u).card := by omega
    -- bonds inside `X.erase` sets, for reuse
    have hbond : ∀ u ∈ X, ∀ v ∈ X, (neighbors X u).card = 5 → v ≠ u → dist u v = 1 := by
      intro u hu v hv h5 hvu
      have hfull : neighbors X u = X.erase u :=
        Finset.eq_of_subset_of_card_le (neighbors_subset_erase X u)
          (by rw [Finset.card_erase_of_mem hu, h6, h5])
      have : v ∈ neighbors X u := by rw [hfull]; exact Finset.mem_erase.mpr ⟨hvu, hv⟩
      exact (Finset.mem_filter.mp this).2
    by_cases hT : ∃ u ∈ Y, (neighbors X u).card = 5
    · -- a full particle in `Y` gives a triangle on the ring
      obtain ⟨u, huY, hdegu⟩ := hT
      have hsum2 : 11 ≤ ∑ x ∈ Y.erase u, (neighbors X x).card := by
        have := Finset.add_sum_erase Y (fun x => (neighbors X x).card) huY
        omega
      have hv' : ∃ x ∈ Y.erase u, 4 ≤ (neighbors X x).card := by
        by_contra hno
        push Not at hno
        have : ∑ x ∈ Y.erase u, (neighbors X x).card ≤ 9 := by
          calc ∑ x ∈ Y.erase u, (neighbors X x).card ≤ ∑ _x ∈ Y.erase u, 3 := by
                refine Finset.sum_le_sum fun x hx => ?_
                have := hno x hx
                omega
            _ = 9 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem huY, hYcard, smul_eq_mul]
        omega
      obtain ⟨v', hv'E, hdegv'⟩ := hv'
      have hv'Y : v' ∈ Y := Finset.mem_of_mem_erase hv'E
      have hv'u : v' ≠ u := Finset.ne_of_mem_erase hv'E
      -- a second `Y`-neighbour of `v'`, distinct from `u`
      have hsubW : (neighbors X v') \ {e, f} ⊆ Y.erase v' := by
        intro x hx
        obtain ⟨hxN, hxef⟩ := Finset.mem_sdiff.mp hx
        obtain ⟨hxX, hxd⟩ := Finset.mem_filter.mp hxN
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxef
        have hxv' : x ≠ v' := by
          rintro rfl
          rw [dist_self] at hxd
          norm_num at hxd
        exact Finset.mem_erase.mpr ⟨hxv',
          Finset.mem_erase.mpr ⟨hxef.2, Finset.mem_erase.mpr ⟨hxef.1, hxX⟩⟩⟩
      have hcard2 : 2 ≤ ((neighbors X v') \ {e, f}).card := by
        have h1 := Finset.le_card_sdiff ({e, f} : Finset E3) (neighbors X v')
        have h2 : ({e, f} : Finset E3).card ≤ 2 := Finset.card_insert_le _ _ |>.trans
          (by rw [Finset.card_singleton])
        omega
      obtain ⟨w, hw, hwu⟩ :=
        Finset.exists_mem_ne (by omega : 1 < ((neighbors X v') \ {e, f}).card) u
      have hwY : w ∈ Y := Finset.mem_of_mem_erase (hsubW hw)
      have hwv' : w ≠ v' := Finset.ne_of_mem_erase (hsubW hw)
      -- the triangle `u, v', w`
      have b1 : dist u v' = 1 := hbond u (hYX u huY) v' (hYX v' hv'Y) hdegu hv'u
      have b2 : dist u w = 1 := hbond u (hYX u huY) w (hYX w hwY) hdegu hwu
      have b3 : dist v' w = 1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw).1).2
      exact common_triangle_impossible hef (hYC u huY) (hYC v' hv'Y) (hYC w hwY) b1 b2 b3
    · -- all `Y`-degrees are four: the ring carries a perfect four-cycle
      push Not at hT
      have hdeg4 : ∀ u ∈ Y, (neighbors X u).card = 4 := by
        intro u huY
        have h5 := hdeg u (hYX u huY)
        have hne5 := hT u huY
        by_contra hne4
        have hu3 : (neighbors X u).card ≤ 3 := by omega
        have hrest : ∑ x ∈ Y.erase u, (neighbors X x).card ≤ 12 := by
          calc ∑ x ∈ Y.erase u, (neighbors X x).card ≤ ∑ _x ∈ Y.erase u, 4 := by
                refine Finset.sum_le_sum fun x hx => ?_
                have := hdeg x (hYX x (Finset.mem_of_mem_erase hx))
                have := hT x (Finset.mem_of_mem_erase hx)
                omega
            _ = 12 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem huY, hYcard, smul_eq_mul]
        have := Finset.add_sum_erase Y (fun x => (neighbors X x).card) huY
        omega
      -- each `Y`-particle has a unique non-partner, and it lies in `Y`
      have huniq : ∀ u ∈ Y, ∃ b, (X.erase u) \ (neighbors X u) = {b} ∧ b ∈ Y ∧
          b ∉ neighbors X u := by
        intro u huY
        have hcard1 : ((X.erase u) \ (neighbors X u)).card = 1 := by
          rw [Finset.card_sdiff_of_subset (neighbors_subset_erase X u),
            Finset.card_erase_of_mem (hYX u huY), h6, hdeg4 u huY]
        obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard1
        have hbmem : b ∈ (X.erase u) \ (neighbors X u) := by
          rw [hb]; exact Finset.mem_singleton_self b
        obtain ⟨hbE, hbN⟩ := Finset.mem_sdiff.mp hbmem
        have hbe : b ≠ e := by
          rintro rfl
          exact hbN (hefY u huY).1
        have hbf : b ≠ f := by
          rintro rfl
          exact hbN (hefY u huY).2
        exact ⟨b, hb, Finset.mem_erase.mpr ⟨hbf,
          Finset.mem_erase.mpr ⟨hbe, Finset.mem_of_mem_erase hbE⟩⟩, hbN⟩
      obtain ⟨a, haY⟩ : Y.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨b, hsd_a, hbY, hbN⟩ := huniq a haY
      have hba : b ≠ a := by
        have : b ∈ (X.erase a) \ (neighbors X a) := by
          rw [hsd_a]; exact Finset.mem_singleton_self b
        exact Finset.ne_of_mem_erase (Finset.mem_sdiff.mp this).1
      -- the two remaining particles
      have h2card : ((Y.erase a).erase b).card = 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hba, hbY⟩),
          Finset.card_erase_of_mem haY, hYcard]
      obtain ⟨c, d, hcd_ne, hcdset⟩ := Finset.card_eq_two.mp h2card
      have hcmem : c ∈ (Y.erase a).erase b := by rw [hcdset]; simp
      have hdmem : d ∈ (Y.erase a).erase b := by rw [hcdset]; simp
      have hcY : c ∈ Y := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcmem)
      have hdY : d ∈ Y := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hdmem)
      have hca : c ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcmem)
      have hda : d ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hdmem)
      have hcb : c ≠ b := Finset.ne_of_mem_erase hcmem
      have hdb : d ≠ b := Finset.ne_of_mem_erase hdmem
      -- bonds from `a`: everything in `X.erase a` except `b`
      have habond : ∀ x, x ∈ X → x ≠ a → x ≠ b → dist a x = 1 := by
        intro x hxX hxa hxb
        have hxE : x ∈ X.erase a := Finset.mem_erase.mpr ⟨hxa, hxX⟩
        have : x ∈ neighbors X a := by
          by_contra hno
          have : x ∈ (X.erase a) \ (neighbors X a) := Finset.mem_sdiff.mpr ⟨hxE, hno⟩
          rw [hsd_a, Finset.mem_singleton] at this
          exact hxb this
        exact (Finset.mem_filter.mp this).2
      -- bonds from `b`: its unique non-partner is `a`
      obtain ⟨a', hsd_b, _, _⟩ := huniq b hbY
      have haa' : a' = a := by
        have haN : a ∉ neighbors X b := by
          intro hmem
          have : b ∈ neighbors X a := Finset.mem_filter.mpr
            ⟨hYX b hbY, by rw [dist_comm]; exact (Finset.mem_filter.mp hmem).2⟩
          exact hbN this
        have : a ∈ (X.erase b) \ (neighbors X b) :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hba.symm, hYX a haY⟩, haN⟩
        rw [hsd_b, Finset.mem_singleton] at this
        exact this.symm
      have hbbond : ∀ x, x ∈ X → x ≠ b → x ≠ a → dist b x = 1 := by
        intro x hxX hxb hxa
        have hxE : x ∈ X.erase b := Finset.mem_erase.mpr ⟨hxb, hxX⟩
        have : x ∈ neighbors X b := by
          by_contra hno
          have : x ∈ (X.erase b) \ (neighbors X b) := Finset.mem_sdiff.mpr ⟨hxE, hno⟩
          rw [hsd_b, haa', Finset.mem_singleton] at this
          exact hxa this
        exact (Finset.mem_filter.mp this).2
      exact common_square_impossible hX hef (hYC a haY) (hYC b hbY) (hYC c hcY)
        (hYC d hdY) (Ne.symm hba) hcd_ne
        (habond c (hYX c hcY) hca hcb) (habond d (hYX d hdY) hda hdb)
        (hbbond c (hYX c hcY) hcb hca) (hbbond d (hYX d hdY) hdb hda)
  rw [energy]
  have : (contactCount X : ℝ) ≤ 24 := by exact_mod_cast hcc
  linarith

/-! ### The octahedron -/

noncomputable def oc0 : E3 := WithLp.toLp 2 ![Real.sqrt 2 / 2, 0, 0]
noncomputable def oc1 : E3 := WithLp.toLp 2 ![-(Real.sqrt 2 / 2), 0, 0]
noncomputable def oc2 : E3 := WithLp.toLp 2 ![0, Real.sqrt 2 / 2, 0]
noncomputable def oc3 : E3 := WithLp.toLp 2 ![0, -(Real.sqrt 2 / 2), 0]
noncomputable def oc4 : E3 := WithLp.toLp 2 ![0, 0, Real.sqrt 2 / 2]
noncomputable def oc5 : E3 := WithLp.toLp 2 ![0, 0, -(Real.sqrt 2 / 2)]

/-- The regular octahedron with unit edge. -/
noncomputable def octa : Finset E3 := {oc0, oc1, oc2, oc3, oc4, oc5}

section OctaDistances

private lemma h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma ne_of_dist_sqrt2 {a b : E3} (h : dist a b = Real.sqrt 2) : a ≠ b := by
  rintro rfl
  rw [dist_self] at h
  have h1 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith [h.symm]

private lemma od02 : dist oc0 oc2 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2 + ((0:ℝ) - 0)^2) = 1
  rw [show ((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2 + ((0:ℝ) - 0)^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od03 : dist oc0 oc3 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2 + ((0:ℝ) - 0)^2) = 1
  rw [show ((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2 + ((0:ℝ) - 0)^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od04 : dist oc0 oc4 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2) = 1
  rw [show ((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od05 : dist oc0 oc5 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2) = 1
  rw [show ((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od12 : dist oc1 oc2 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2 + ((0:ℝ) - 0)^2) = 1
  rw [show ((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2 + ((0:ℝ) - 0)^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od13 : dist oc1 oc3 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2 + ((0:ℝ) - 0)^2) = 1
  rw [show ((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2 + ((0:ℝ) - 0)^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od14 : dist oc1 oc4 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2) = 1
  rw [show ((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od15 : dist oc1 oc5 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2) = 1
  rw [show ((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od24 : dist oc2 oc4 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 0)^2 + ((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2) = 1
  rw [show ((0:ℝ) - 0)^2 + ((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od25 : dist oc2 oc5 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 0)^2 + ((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2) = 1
  rw [show ((0:ℝ) - 0)^2 + ((Real.sqrt 2 / 2:ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od34 : dist oc3 oc4 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 0)^2 + ((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2) = 1
  rw [show ((0:ℝ) - 0)^2 + ((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - Real.sqrt 2 / 2)^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od35 : dist oc3 oc5 = 1 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 0)^2 + ((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2) = 1
  rw [show ((0:ℝ) - 0)^2 + ((-(Real.sqrt 2 / 2):ℝ) - 0)^2 + ((0:ℝ) - -(Real.sqrt 2 / 2))^2 = 1 by linear_combination (1/2) * h2sq]
  exact Real.sqrt_one

private lemma od01 : dist oc0 oc1 = Real.sqrt 2 := by
  rw [dist_coords]
  show Real.sqrt (((Real.sqrt 2 / 2:ℝ) - -(Real.sqrt 2 / 2))^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - 0)^2) = Real.sqrt 2
  rw [show ((Real.sqrt 2 / 2:ℝ) - -(Real.sqrt 2 / 2))^2 + ((0:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 = 2 by linear_combination h2sq]

private lemma od23 : dist oc2 oc3 = Real.sqrt 2 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 0)^2 + ((Real.sqrt 2 / 2:ℝ) - -(Real.sqrt 2 / 2))^2 + ((0:ℝ) - 0)^2) = Real.sqrt 2
  rw [show ((0:ℝ) - 0)^2 + ((Real.sqrt 2 / 2:ℝ) - -(Real.sqrt 2 / 2))^2 + ((0:ℝ) - 0)^2 = 2 by linear_combination h2sq]

private lemma od45 : dist oc4 oc5 = Real.sqrt 2 := by
  rw [dist_coords]
  show Real.sqrt (((0:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((Real.sqrt 2 / 2:ℝ) - -(Real.sqrt 2 / 2))^2) = Real.sqrt 2
  rw [show ((0:ℝ) - 0)^2 + ((0:ℝ) - 0)^2 + ((Real.sqrt 2 / 2:ℝ) - -(Real.sqrt 2 / 2))^2 = 2 by linear_combination h2sq]

end OctaDistances

section OctaConfig

private lemma one01 : oc0 ≠ oc1 := ne_of_dist_sqrt2 od01
private lemma one02 : oc0 ≠ oc2 := ne_of_dist_one od02
private lemma one03 : oc0 ≠ oc3 := ne_of_dist_one od03
private lemma one04 : oc0 ≠ oc4 := ne_of_dist_one od04
private lemma one05 : oc0 ≠ oc5 := ne_of_dist_one od05
private lemma one12 : oc1 ≠ oc2 := ne_of_dist_one od12
private lemma one13 : oc1 ≠ oc3 := ne_of_dist_one od13
private lemma one14 : oc1 ≠ oc4 := ne_of_dist_one od14
private lemma one15 : oc1 ≠ oc5 := ne_of_dist_one od15
private lemma one23 : oc2 ≠ oc3 := ne_of_dist_sqrt2 od23
private lemma one24 : oc2 ≠ oc4 := ne_of_dist_one od24
private lemma one25 : oc2 ≠ oc5 := ne_of_dist_one od25
private lemma one34 : oc3 ≠ oc4 := ne_of_dist_one od34
private lemma one35 : oc3 ≠ oc5 := ne_of_dist_one od35
private lemma one45 : oc4 ≠ oc5 := ne_of_dist_sqrt2 od45

private lemma octa_dist : ∀ u ∈ octa, ∀ v ∈ octa, u ≠ v → 1 ≤ dist u v := by
  have key : ∀ a b : E3, dist a b = 1 → 1 ≤ dist a b ∧ 1 ≤ dist b a := by
    intro a b h
    exact ⟨by rw [h], by rw [dist_comm, h]⟩
  have key2 : ∀ a b : E3, dist a b = Real.sqrt 2 → 1 ≤ dist a b ∧ 1 ≤ dist b a := by
    intro a b h
    have h1 : (1:ℝ) ≤ Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact ⟨by rw [h]; exact h1, by rw [dist_comm, h]; exact h1⟩
  intro u hu v hv huv
  simp only [octa, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl huv
      | exact (key _ _ od02).1 | exact (key _ _ od02).2
      | exact (key _ _ od03).1 | exact (key _ _ od03).2
      | exact (key _ _ od04).1 | exact (key _ _ od04).2
      | exact (key _ _ od05).1 | exact (key _ _ od05).2
      | exact (key _ _ od12).1 | exact (key _ _ od12).2
      | exact (key _ _ od13).1 | exact (key _ _ od13).2
      | exact (key _ _ od14).1 | exact (key _ _ od14).2
      | exact (key _ _ od15).1 | exact (key _ _ od15).2
      | exact (key _ _ od24).1 | exact (key _ _ od24).2
      | exact (key _ _ od25).1 | exact (key _ _ od25).2
      | exact (key _ _ od34).1 | exact (key _ _ od34).2
      | exact (key _ _ od35).1 | exact (key _ _ od35).2
      | exact (key2 _ _ od01).1 | exact (key2 _ _ od01).2
      | exact (key2 _ _ od23).1 | exact (key2 _ _ od23).2
      | exact (key2 _ _ od45).1 | exact (key2 _ _ od45).2

theorem hardCore_octa : HardCore octa := octa_dist

theorem card_octa : octa.card = 6 := by
  rw [octa]
  rw [Finset.card_insert_of_notMem (by simp [one01, one02, one03, one04, one05]),
    Finset.card_insert_of_notMem (by simp [one12, one13, one14, one15]),
    Finset.card_insert_of_notMem (by simp [one23, one24, one25]),
    Finset.card_insert_of_notMem (by simp [one34, one35]),
    Finset.card_insert_of_notMem (by simp [one45]),
    Finset.card_singleton]

private lemma hd0 : 4 ≤ (neighbors octa oc0).card := by
  refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {oc2, oc3, oc4, oc5} ?_)
  · rw [Finset.card_insert_of_notMem (by simp [one23, one24, one25]),
      Finset.card_insert_of_notMem (by simp [one34, one35]),
      Finset.card_insert_of_notMem (by simp [one45]), Finset.card_singleton]
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨by simp [octa], od02⟩
    · exact ⟨by simp [octa], od03⟩
    · exact ⟨by simp [octa], od04⟩
    · exact ⟨by simp [octa], od05⟩

private lemma hd1 : 4 ≤ (neighbors octa oc1).card := by
  refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {oc2, oc3, oc4, oc5} ?_)
  · rw [Finset.card_insert_of_notMem (by simp [one23, one24, one25]),
      Finset.card_insert_of_notMem (by simp [one34, one35]),
      Finset.card_insert_of_notMem (by simp [one45]), Finset.card_singleton]
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨by simp [octa], od12⟩
    · exact ⟨by simp [octa], od13⟩
    · exact ⟨by simp [octa], od14⟩
    · exact ⟨by simp [octa], od15⟩

private lemma hd2 : 4 ≤ (neighbors octa oc2).card := by
  refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {oc0, oc1, oc4, oc5} ?_)
  · rw [Finset.card_insert_of_notMem (by simp [one01, one04, one05]),
      Finset.card_insert_of_notMem (by simp [one14, one15]),
      Finset.card_insert_of_notMem (by simp [one45]), Finset.card_singleton]
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od02⟩
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od12⟩
    · exact ⟨by simp [octa], od24⟩
    · exact ⟨by simp [octa], od25⟩

private lemma hd3 : 4 ≤ (neighbors octa oc3).card := by
  refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {oc0, oc1, oc4, oc5} ?_)
  · rw [Finset.card_insert_of_notMem (by simp [one01, one04, one05]),
      Finset.card_insert_of_notMem (by simp [one14, one15]),
      Finset.card_insert_of_notMem (by simp [one45]), Finset.card_singleton]
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od03⟩
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od13⟩
    · exact ⟨by simp [octa], od34⟩
    · exact ⟨by simp [octa], od35⟩

private lemma hd4 : 4 ≤ (neighbors octa oc4).card := by
  refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {oc0, oc1, oc2, oc3} ?_)
  · rw [Finset.card_insert_of_notMem (by simp [one01, one02, one03]),
      Finset.card_insert_of_notMem (by simp [one12, one13]),
      Finset.card_insert_of_notMem (by simp [one23]), Finset.card_singleton]
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od04⟩
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od14⟩
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od24⟩
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od34⟩

private lemma hd5 : 4 ≤ (neighbors octa oc5).card := by
  refine le_trans (le_of_eq (Eq.symm ?_)) (le_card_neighbors {oc0, oc1, oc2, oc3} ?_)
  · rw [Finset.card_insert_of_notMem (by simp [one01, one02, one03]),
      Finset.card_insert_of_notMem (by simp [one12, one13]),
      Finset.card_insert_of_notMem (by simp [one23]), Finset.card_singleton]
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od05⟩
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od15⟩
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od25⟩
    · exact ⟨by simp [octa], by rw [dist_comm]; exact od35⟩

theorem energy_octa : energy octa = -12 := by
  have hle : energy octa ≤ -12 := by
    have hcc : 24 ≤ contactCount octa := by
      rw [contactCount, octa]
      rw [Finset.sum_insert (by simp [one01, one02, one03, one04, one05]),
        Finset.sum_insert (by simp [one12, one13, one14, one15]),
        Finset.sum_insert (by simp [one23, one24, one25]),
        Finset.sum_insert (by simp [one34, one35]),
        Finset.sum_insert (by simp [one45]),
        Finset.sum_singleton]
      simp only [show ({oc0, oc1, oc2, oc3, oc4, oc5} : Finset E3) = octa from rfl]
      have h0 := hd0; have h1 := hd1; have h2 := hd2
      have h3 := hd3; have h4 := hd4; have h5 := hd5
      omega
    rw [energy]
    have : (24 : ℝ) ≤ (contactCount octa : ℝ) := by exact_mod_cast hcc
    linarith
  have hge := energy_ge_six_particles hardCore_octa card_octa
  linarith

/-- **`E_min(6) = −12`**: the regular octahedron is the six-particle ground state. The
route is no longer counting: it needs the kissing-style ring geometry of a bonded pair. -/
theorem groundState_six :
    (∀ X : Finset E3, HardCore X → X.card = 6 → -12 ≤ energy X) ∧
    HardCore octa ∧ octa.card = 6 ∧ energy octa = -12 :=
  ⟨fun _ hX h => energy_ge_six_particles hX h, hardCore_octa, card_octa, energy_octa⟩

end OctaConfig

end Kissing3D
