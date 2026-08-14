import ContactNumbers.Emin9Final

set_option linter.style.header false
set_option maxHeartbeats 1000000

/-!
# Minimal rigidity of the maximum-contact packings

Bezdek–Khan, Conjecture 5.2, has two halves. The numerical half — `c(n,3) = 3n-6` for
`n = 6,…,9` — is `groundState_six/seven/eight/nine`. This file supplies the *structural*
half at those `n`: every packing attaining the maximum is **minimally rigid** in the
sense of Definition 1 of the survey (following Arkus–Manoharan–Brenner), namely

* every sphere is in contact with at least three others, and
* the packing has at least `3n - 6` contacts.

The second bullet is immediate at a maximiser. The first is the same erase-a-vertex
recursion that gives `degree_ge_four`, run one step lower: a particle of degree at most
two, deleted from an `n`-particle maximiser, would leave `n-1` particles carrying
`2(3n-6) - 4 = 2(3(n-1)-6) + 2` ordered contacts, one bond more than `c(n-1,3)` allows.

So each case rests on the case below it, and the chain bottoms out at `c(5,3) = 9`.
-/

namespace Kissing3D

open Finset

/-! ### Contact counts from energies -/

lemma contactCount_le_of_energy {X : Finset E3} {k : ℕ} (h : -(k : ℝ) ≤ energy X) :
    contactCount X ≤ 2 * k := by
  rw [energy] at h
  have h2 : (contactCount X : ℝ) ≤ (2 * k : ℕ) := by push_cast; linarith
  exact_mod_cast h2

lemma contactCount_eq_of_energy {X : Finset E3} {k : ℕ} (h : energy X = -(k : ℝ)) :
    contactCount X = 2 * k := by
  rw [energy] at h
  have h2 : (contactCount X : ℝ) = (2 * k : ℕ) := by push_cast; linarith
  exact_mod_cast h2

/-- `c(5,3) ≤ 9`. -/
theorem five_particle_bound {X : Finset E3} (h5 : X.card = 5) : contactCount X ≤ 18 :=
  contactCount_le_of_energy (k := 9) (by exact_mod_cast energy_ge_five_particles h5)

/-- `c(6,3) ≤ 12`. -/
theorem six_particle_bound {X : Finset E3} (hX : HardCore X) (h6 : X.card = 6) :
    contactCount X ≤ 24 :=
  contactCount_le_of_energy (k := 12) (by exact_mod_cast energy_ge_six_particles hX h6)

/-! ### Minimum degree three at a maximiser -/

private lemma erase_hardCore {X : Finset E3} (hX : HardCore X) (v : E3) :
    HardCore (X.erase v) := fun a ha b hb hab =>
  hX a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab

/-- **Six particles, minimum degree three.** A twelve-contact six-particle packing has
no particle of degree at most two: deleting one would leave five particles with ten
bonds, and `c(5,3) = 9`. -/
theorem minDegree_six {X : Finset E3} (h6 : X.card = 6)
    (hcc : 24 ≤ contactCount X) : ∀ v ∈ X, 3 ≤ (neighbors X v).card := by
  intro v hv
  by_contra hlt
  push_neg at hlt
  have herase := contactCount_erase (X := X) (v := v) hv
  have hcard : (X.erase v).card = 5 := by rw [Finset.card_erase_of_mem hv, h6]
  have hbound := five_particle_bound hcard
  omega

/-- **Seven particles, minimum degree three**, from `c(6,3) = 12`. -/
theorem minDegree_seven {X : Finset E3} (hX : HardCore X) (h7 : X.card = 7)
    (hcc : 30 ≤ contactCount X) : ∀ v ∈ X, 3 ≤ (neighbors X v).card := by
  intro v hv
  by_contra hlt
  push_neg at hlt
  have herase := contactCount_erase (X := X) (v := v) hv
  have hcard : (X.erase v).card = 6 := by rw [Finset.card_erase_of_mem hv, h7]
  have hbound := six_particle_bound (erase_hardCore hX v) hcard
  omega

/-- **Eight particles, minimum degree three**, from `c(7,3) = 15`. -/
theorem minDegree_eight {X : Finset E3} (hX : HardCore X) (h8 : X.card = 8)
    (hcc : 36 ≤ contactCount X) : ∀ v ∈ X, 3 ≤ (neighbors X v).card := by
  intro v hv
  by_contra hlt
  push_neg at hlt
  have herase := contactCount_erase (X := X) (v := v) hv
  have hcard : (X.erase v).card = 7 := by rw [Finset.card_erase_of_mem hv, h8]
  have hbound := seven_particle_bound (erase_hardCore hX v) hcard
  omega


/-- **Nine particles, minimum degree three**, from `c(8,3) = 18`. -/
theorem minDegree_nine {X : Finset E3} (hX : HardCore X) (h9 : X.card = 9)
    (hcc : 42 ≤ contactCount X) : ∀ v ∈ X, 3 ≤ (neighbors X v).card := by
  intro v hv
  by_contra hlt
  push_neg at hlt
  have herase := contactCount_erase (X := X) (v := v) hv
  have hcard : (X.erase v).card = 8 := by rw [Finset.card_erase_of_mem hv, h9]
  have hbound := eight_particle_bound (erase_hardCore hX v) hcard
  omega

/-! ### Bezdek–Khan Conjecture 5.2, in full, for `n = 6, 7, 8, 9`

Each statement below is the conjunction of

1. the upper bound `c(n,3) ≤ 3n - 6`,
2. a packing attaining it, and
3. minimal rigidity of *every* packing attaining it: minimum degree at least three,
   and at least `3n - 6` contacts.

Contact counts are ordered, so `2 * (3n - 6)` is `3n - 6` contacts. -/

theorem conj52_six :
    (∀ X : Finset E3, HardCore X → X.card = 6 → contactCount X ≤ 24) ∧
    (HardCore octa ∧ octa.card = 6 ∧ contactCount octa = 24) ∧
    (∀ X : Finset E3, HardCore X → X.card = 6 → contactCount X = 24 →
      (∀ v ∈ X, 3 ≤ (neighbors X v).card) ∧ 24 ≤ contactCount X) := by
  refine ⟨fun _ hX h => six_particle_bound hX h,
    ⟨hardCore_octa, card_octa, contactCount_eq_of_energy (k := 12) (by exact_mod_cast energy_octa)⟩,
    fun X _ h6 heq => ⟨minDegree_six h6 heq.ge, heq.ge⟩⟩

theorem conj52_seven :
    (∀ X : Finset E3, HardCore X → X.card = 7 → contactCount X ≤ 30) ∧
    (HardCore bipyr7 ∧ bipyr7.card = 7 ∧ contactCount bipyr7 = 30) ∧
    (∀ X : Finset E3, HardCore X → X.card = 7 → contactCount X = 30 →
      (∀ v ∈ X, 3 ≤ (neighbors X v).card) ∧ 30 ≤ contactCount X) := by
  refine ⟨fun _ hX h => seven_particle_bound hX h,
    ⟨hardCore_bipyr7, card_bipyr7,
      contactCount_eq_of_energy (k := 15) (by exact_mod_cast energy_bipyr7)⟩,
    fun X hX h7 heq => ⟨minDegree_seven hX h7 heq.ge, heq.ge⟩⟩

theorem conj52_eight :
    (∀ X : Finset E3, HardCore X → X.card = 8 → contactCount X ≤ 36) ∧
    (HardCore capBipyr8 ∧ capBipyr8.card = 8 ∧ contactCount capBipyr8 = 36) ∧
    (∀ X : Finset E3, HardCore X → X.card = 8 → contactCount X = 36 →
      (∀ v ∈ X, 3 ≤ (neighbors X v).card) ∧ 36 ≤ contactCount X) := by
  refine ⟨fun _ hX h => eight_particle_bound hX h,
    ⟨hardCore_capBipyr8, card_capBipyr8,
      contactCount_eq_of_energy (k := 18) (by exact_mod_cast energy_capBipyr8)⟩,
    fun X hX h8 heq => ⟨minDegree_eight hX h8 heq.ge, heq.ge⟩⟩

theorem conj52_nine :
    (∀ X : Finset E3, HardCore X → X.card = 9 → contactCount X ≤ 42) ∧
    (HardCore capBipyr9 ∧ capBipyr9.card = 9 ∧ contactCount capBipyr9 = 42) ∧
    (∀ X : Finset E3, HardCore X → X.card = 9 → contactCount X = 42 →
      (∀ v ∈ X, 3 ≤ (neighbors X v).card) ∧ 42 ≤ contactCount X) := by
  refine ⟨fun _ hX h => nine_particle_bound hX h,
    ⟨hardCore_capBipyr9, card_capBipyr9,
      contactCount_eq_of_energy (k := 21) (by exact_mod_cast energy_capBipyr9)⟩,
    fun X hX h9 heq => ⟨minDegree_nine hX h9 heq.ge, heq.ge⟩⟩

end Kissing3D
