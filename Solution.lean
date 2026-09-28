/-
Copyright (c) 2026 Marek Wrzos. All rights reserved.
Released under Apache 2.0 licence.

Proofs of the statements in `Challenge.lean`.

The definitions below are repeated verbatim from the Challenge module so that the
statements compared are literally the same. The mathematics lives in the
`ContactNumbers` library that this file imports; everything here is plumbing.
-/

module

public import ContactNumbers.MinDegree

@[expose] public section

namespace ContactNumbers

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def HardCore (X : Finset E3) : Prop :=
  ∀ z ∈ X, ∀ w ∈ X, z ≠ w → 1 ≤ dist z w

open scoped Classical in
noncomputable def neighbors (X : Finset E3) (z : E3) : Finset E3 :=
  X.filter (fun w => dist z w = 1)

noncomputable def contacts (X : Finset E3) : ℕ := (∑ z ∈ X, (neighbors X z).card) / 2

def realised (n : ℕ) : Set ℕ :=
  {k | ∃ X : Finset E3, HardCore X ∧ X.card = n ∧ contacts X = k}

def MinimallyRigid (X : Finset E3) : Prop :=
  (∀ v ∈ X, 3 ≤ (neighbors X v).card) ∧ 3 * X.card - 6 ≤ contacts X

/-! ### Bridges to the library.  Each holds by definitional unfolding. -/

private lemma hardCore_iff {X : Finset E3} : HardCore X ↔ Kissing3D.HardCore X := Iff.rfl

private lemma neighbors_eq (X : Finset E3) (z : E3) :
    neighbors X z = Kissing3D.neighbors X z := rfl

private lemma contacts_eq (X : Finset E3) : contacts X = Kissing3D.contactCount X / 2 := rfl

private lemma two_mul_div (m : ℕ) : 2 * m / 2 = m := Nat.mul_div_cancel_left m (by norm_num)

/-- A matching upper bound and a witness give the exact contact number. -/
private lemma isGreatest_of {n c : ℕ} {W : Finset E3}
    (hub : ∀ X : Finset E3, Kissing3D.HardCore X → X.card = n →
      Kissing3D.contactCount X ≤ 2 * c)
    (hW : Kissing3D.HardCore W) (hcard : W.card = n)
    (hcc : Kissing3D.contactCount W = 2 * c) :
    IsGreatest (realised n) c := by
  refine ⟨⟨W, hardCore_iff.mpr hW, hcard, by rw [contacts_eq, hcc, two_mul_div]⟩, ?_⟩
  rintro k ⟨X, hX, hn, rfl⟩
  calc contacts X = Kissing3D.contactCount X / 2 := contacts_eq X
    _ ≤ (2 * c) / 2 := Nat.div_le_div_right (hub X (hardCore_iff.mp hX) hn)
    _ = c := two_mul_div c

theorem contactNumber_six : IsGreatest (realised 6) 12 :=
  isGreatest_of (c := 12) (fun _ hX h => Kissing3D.six_particle_bound hX h)
    Kissing3D.hardCore_octa Kissing3D.card_octa
    (Kissing3D.contactCount_eq_of_energy (k := 12) (by exact_mod_cast Kissing3D.energy_octa))

theorem contactNumber_seven : IsGreatest (realised 7) 15 :=
  isGreatest_of (c := 15) (fun _ hX h => Kissing3D.seven_particle_bound hX h)
    Kissing3D.hardCore_bipyr7 Kissing3D.card_bipyr7
    (Kissing3D.contactCount_eq_of_energy (k := 15) (by exact_mod_cast Kissing3D.energy_bipyr7))

theorem contactNumber_eight : IsGreatest (realised 8) 18 :=
  isGreatest_of (c := 18) (fun _ hX h => Kissing3D.eight_particle_bound hX h)
    Kissing3D.hardCore_capBipyr8 Kissing3D.card_capBipyr8
    (Kissing3D.contactCount_eq_of_energy (k := 18) (by exact_mod_cast Kissing3D.energy_capBipyr8))

theorem contactNumber_nine : IsGreatest (realised 9) 21 :=
  isGreatest_of (c := 21) (fun _ hX h => Kissing3D.nine_particle_bound hX h)
    Kissing3D.hardCore_capBipyr9 Kissing3D.card_capBipyr9
    (Kissing3D.contactCount_eq_of_energy (k := 21) (by exact_mod_cast Kissing3D.energy_capBipyr9))

/-! ### Minimal rigidity of the maximisers -/

private lemma minimallyRigid_of {n c : ℕ} {X : Finset E3}
    (hdeg : ∀ v ∈ X, 3 ≤ (Kissing3D.neighbors X v).card) (hn : X.card = n)
    (hc : contacts X = c) (hge : 3 * n - 6 ≤ c) : MinimallyRigid X := by
  refine ⟨fun v hv => ?_, by rw [hn, hc]; exact hge⟩
  rw [neighbors_eq]; exact hdeg v hv

private lemma cc_of_contacts {X : Finset E3} {c : ℕ} (h : contacts X = c) :
    2 * c ≤ Kissing3D.contactCount X := by
  obtain ⟨m, hm⟩ := Kissing3D.contactCount_even X
  rw [contacts_eq] at h; omega

theorem conjecture52_six :
    IsGreatest (realised 6) 12 ∧
    ∀ X : Finset E3, HardCore X → X.card = 6 → contacts X = 12 → MinimallyRigid X := by
  refine ⟨contactNumber_six, fun X _ h6 hc => ?_⟩
  exact minimallyRigid_of (Kissing3D.minDegree_six h6 (cc_of_contacts hc)) h6 hc (by norm_num)

theorem conjecture52_seven :
    IsGreatest (realised 7) 15 ∧
    ∀ X : Finset E3, HardCore X → X.card = 7 → contacts X = 15 → MinimallyRigid X := by
  refine ⟨contactNumber_seven, fun X hX h7 hc => ?_⟩
  exact minimallyRigid_of
    (Kissing3D.minDegree_seven (hardCore_iff.mp hX) h7 (cc_of_contacts hc)) h7 hc (by norm_num)

theorem conjecture52_eight :
    IsGreatest (realised 8) 18 ∧
    ∀ X : Finset E3, HardCore X → X.card = 8 → contacts X = 18 → MinimallyRigid X := by
  refine ⟨contactNumber_eight, fun X hX h8 hc => ?_⟩
  exact minimallyRigid_of
    (Kissing3D.minDegree_eight (hardCore_iff.mp hX) h8 (cc_of_contacts hc)) h8 hc (by norm_num)

theorem conjecture52_nine :
    IsGreatest (realised 9) 21 ∧
    ∀ X : Finset E3, HardCore X → X.card = 9 → contacts X = 21 → MinimallyRigid X := by
  refine ⟨contactNumber_nine, fun X hX h9 hc => ?_⟩
  exact minimallyRigid_of
    (Kissing3D.minDegree_nine (hardCore_iff.mp hX) h9 (cc_of_contacts hc)) h9 hc (by norm_num)

end ContactNumbers
