import ContactNumbers.MinDegree

set_option linter.style.header false

/-!
# The results, in contact-number language

The development below this file is stated in terms of `energy X = -contactCount X / 2`,
inherited from the hard-sphere energy-minimisation setting it grew out of, and
`contactCount` counts *ordered* touching pairs. This file restates the four results in
the language of the contact-number problem, with no dictionary required of the reader:

* `contacts X` is the number of touching pairs (unordered);
* `realised n` is the set of contact numbers achieved by hard-core packings of `n` balls;
* `IsGreatest (realised n) c` says exactly that `c(n,3) = c`;
* `MinimallyRigid` is Definition 1 of Bezdek–Khan, after Arkus–Manoharan–Brenner.

These are the statements referred to in the accompanying paper, and the ones checked by
`Axioms.lean`.
-/

namespace ContactNumbers

open Kissing3D Finset

/-- The number of touching pairs of the packing whose centres are `X`. -/
noncomputable def contacts (X : Finset E3) : ℕ := contactCount X / 2

/-- **Minimal rigidity** (Bezdek–Khan, Definition 1, after Arkus–Manoharan–Brenner):
every ball touches at least three others, and there are at least `3n - 6` contacts. -/
def MinimallyRigid (X : Finset E3) : Prop :=
  (∀ v ∈ X, 3 ≤ (neighbors X v).card) ∧ 3 * X.card - 6 ≤ contacts X

/-- The set of contact numbers realised by hard-core packings of `n` congruent balls.
`IsGreatest (realised n) c` is the statement `c(n,3) = c`. -/
def realised (n : ℕ) : Set ℕ :=
  {k | ∃ X : Finset E3, HardCore X ∧ X.card = n ∧ contacts X = k}

private lemma two_mul_div (m : ℕ) : 2 * m / 2 = m := Nat.mul_div_cancel_left m (by norm_num)

/-- A matching upper bound and witness give the exact contact number. -/
private lemma isGreatest_of {n c : ℕ} {W : Finset E3}
    (hub : ∀ X : Finset E3, HardCore X → X.card = n → contactCount X ≤ 2 * c)
    (hW : HardCore W) (hcard : W.card = n) (hcc : contactCount W = 2 * c) :
    IsGreatest (realised n) c := by
  refine ⟨⟨W, hW, hcard, by rw [contacts, hcc, two_mul_div]⟩, ?_⟩
  rintro k ⟨X, hX, hn, rfl⟩
  calc contacts X = contactCount X / 2 := rfl
    _ ≤ (2 * c) / 2 := Nat.div_le_div_right (hub X hX hn)
    _ = c := two_mul_div c

/-! ### The contact numbers -/

/-- **`c(6,3) = 12`.** -/
theorem contactNumber_six : IsGreatest (realised 6) 12 :=
  isGreatest_of (c := 12) (fun _ hX h => six_particle_bound hX h) hardCore_octa card_octa
    (contactCount_eq_of_energy (k := 12) (by exact_mod_cast energy_octa))

/-- **`c(7,3) = 15`.** -/
theorem contactNumber_seven : IsGreatest (realised 7) 15 :=
  isGreatest_of (c := 15) (fun _ hX h => seven_particle_bound hX h) hardCore_bipyr7 card_bipyr7
    (contactCount_eq_of_energy (k := 15) (by exact_mod_cast energy_bipyr7))

/-- **`c(8,3) = 18`.** -/
theorem contactNumber_eight : IsGreatest (realised 8) 18 :=
  isGreatest_of (c := 18) (fun _ hX h => eight_particle_bound hX h) hardCore_capBipyr8
    card_capBipyr8 (contactCount_eq_of_energy (k := 18) (by exact_mod_cast energy_capBipyr8))

/-- **`c(9,3) = 21`.** -/
theorem contactNumber_nine : IsGreatest (realised 9) 21 :=
  isGreatest_of (c := 21) (fun _ hX h => nine_particle_bound hX h) hardCore_capBipyr9
    card_capBipyr9 (contactCount_eq_of_energy (k := 21) (by exact_mod_cast energy_capBipyr9))

/-! ### Bezdek–Khan Conjecture 5.2 at `n = 6, 7, 8, 9`

The conjecture has two halves: `c(n,3) = 3n - 6` for `n = 6,…,9`, and, for every
`n ≥ 6`, minimal rigidity of every packing attaining `c(n,3)`. Both are proved here at
each `n` for which the conjecture asserts a value. -/

private lemma minimallyRigid_of {n c : ℕ} {X : Finset E3}
    (hdeg : ∀ v ∈ X, 3 ≤ (neighbors X v).card) (hn : X.card = n) (hc : contacts X = c)
    (hge : 3 * n - 6 ≤ c) : MinimallyRigid X :=
  ⟨hdeg, by rw [hn, hc]; exact hge⟩

theorem conjecture52_six :
    IsGreatest (realised 6) 12 ∧
    ∀ X : Finset E3, HardCore X → X.card = 6 → contacts X = 12 → MinimallyRigid X := by
  refine ⟨contactNumber_six, fun X _ h6 hc => ?_⟩
  have h24 : 24 ≤ contactCount X := by rw [contacts] at hc; omega
  exact minimallyRigid_of (minDegree_six h6 h24) h6 hc (by norm_num)

theorem conjecture52_seven :
    IsGreatest (realised 7) 15 ∧
    ∀ X : Finset E3, HardCore X → X.card = 7 → contacts X = 15 → MinimallyRigid X := by
  refine ⟨contactNumber_seven, fun X hX h7 hc => ?_⟩
  have h30 : 30 ≤ contactCount X := by rw [contacts] at hc; omega
  exact minimallyRigid_of (minDegree_seven hX h7 h30) h7 hc (by norm_num)

theorem conjecture52_eight :
    IsGreatest (realised 8) 18 ∧
    ∀ X : Finset E3, HardCore X → X.card = 8 → contacts X = 18 → MinimallyRigid X := by
  refine ⟨contactNumber_eight, fun X hX h8 hc => ?_⟩
  have h36 : 36 ≤ contactCount X := by rw [contacts] at hc; omega
  exact minimallyRigid_of (minDegree_eight hX h8 h36) h8 hc (by norm_num)

theorem conjecture52_nine :
    IsGreatest (realised 9) 21 ∧
    ∀ X : Finset E3, HardCore X → X.card = 9 → contacts X = 21 → MinimallyRigid X := by
  refine ⟨contactNumber_nine, fun X hX h9 hc => ?_⟩
  have h42 : 42 ≤ contactCount X := by rw [contacts] at hc; omega
  exact minimallyRigid_of (minDegree_nine hX h9 h42) h9 hc (by norm_num)

end ContactNumbers
