import ContactNumbers.Emin8Final
import ContactNumbers.Emin9Kills

set_option linter.style.header false
set_option maxHeartbeats 1600000

/-!
# Canonical (lex-maximal) enumerations for the `E_min(9)` walk

The `N = 9` kill tree uses orderly-generation pruning: branches whose decided
bond prefix is lex-dominated by a relabeling die by a permutation certificate.
Soundness rests on two facts proven here:

* every nine-particle configuration admits an enumeration whose bond string
  (36 bits in incremental pair order, edge = 1) is lex-maximal — equivalently,
  maximal as the natural number `bondCode`;
* if two bond strings agree strictly below position `i` and differ at `i` in
  favour of the second, the second's `bondCode` is strictly larger.
-/

namespace Kissing3D

namespace Emin9T

/-- First vertex of the `k`-th pair of `Fin 9` in incremental (colex) order. -/
def cPairFst (k : ℕ) : ℕ :=
  if k < 1 then 0 else if k < 3 then k - 1 else if k < 6 then k - 3
  else if k < 10 then k - 6 else if k < 15 then k - 10 else if k < 21 then k - 15
  else if k < 28 then k - 21 else k - 28

/-- Second vertex of the `k`-th pair. -/
def cPairSnd (k : ℕ) : ℕ :=
  if k < 1 then 1 else if k < 3 then 2 else if k < 6 then 3 else if k < 10 then 4
  else if k < 15 then 5 else if k < 21 then 6 else if k < 28 then 7 else 8

lemma cPair_lt : ∀ k < 36, cPairFst k < 9 ∧ cPairSnd k < 9 := by decide

open scoped Classical in
/-- Bit `k` of the bond string of an enumeration: `1` iff the `k`-th pair is a
bond. -/
noncomputable def bbit (p : Fin 9 → E3) (k : ℕ) : ℕ :=
  if dist (p ⟨cPairFst k % 9, Nat.mod_lt _ (by norm_num)⟩)
       (p ⟨cPairSnd k % 9, Nat.mod_lt _ (by norm_num)⟩) = 1 then 1 else 0

/-- The bond string packed as a natural number, most significant bit = pair 0. -/
noncomputable def bondCode (p : Fin 9 → E3) : ℕ :=
  ∑ k ∈ Finset.range 36, bbit p k * 2 ^ (35 - k)

lemma bbit_le_one (p : Fin 9 → E3) (k : ℕ) : bbit p k ≤ 1 := by
  unfold bbit
  split <;> norm_num

private lemma sum_two_pow (n : ℕ) : ∑ j ∈ Finset.range n, 2 ^ j = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := Nat.one_le_two_pow (n := n)
    have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    omega

/-- **Lex domination**: agreement below `i`, strict advantage at `i < 36`, gives a
strictly larger `bondCode`. -/
lemma bondCode_lt {p q : Fin 9 → E3} {i : ℕ} (hi : i < 36)
    (hagree : ∀ j < i, bbit p j = bbit q j)
    (hlt : bbit p i < bbit q i) : bondCode p < bondCode q := by
  unfold bondCode
  have hIi : Finset.Ico i (i + 1) = {i} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  have hsplit : ∀ r : Fin 9 → E3, ∑ k ∈ Finset.range 36, bbit r k * 2 ^ (35 - k)
      = (∑ k ∈ Finset.range i, bbit r k * 2 ^ (35 - k))
        + bbit r i * 2 ^ (35 - i)
        + ∑ k ∈ Finset.Ico (i + 1) 36, bbit r k * 2 ^ (35 - k) := by
    intro r
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le i) (by omega : i ≤ 36),
      ← Finset.sum_Ico_consecutive _ (by omega : i ≤ i + 1) (by omega : i + 1 ≤ 36),
      hIi, Finset.sum_singleton, ← Finset.range_eq_Ico]
    ring
  rw [hsplit p, hsplit q]
  have heq : ∑ k ∈ Finset.range i, bbit p k * 2 ^ (35 - k)
      = ∑ k ∈ Finset.range i, bbit q k * 2 ^ (35 - k) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hagree j (Finset.mem_range.mp hj)]
  have htail : ∑ k ∈ Finset.Ico (i + 1) 36, bbit p k * 2 ^ (35 - k)
      < 2 ^ (35 - i) := by
    have hb : ∀ k ∈ Finset.Ico (i + 1) 36, bbit p k * 2 ^ (35 - k) ≤ 2 ^ (35 - k) := by
      intro k _
      simpa using mul_le_mul_right' (bbit_le_one p k) (2 ^ (35 - k))
    have h1 : ∑ k ∈ Finset.Ico (i + 1) 36, bbit p k * 2 ^ (35 - k)
        ≤ ∑ k ∈ Finset.Ico (i + 1) 36, 2 ^ (35 - k) := Finset.sum_le_sum hb
    have h2 : ∑ k ∈ Finset.Ico (i + 1) 36, 2 ^ (35 - k)
        = ∑ j ∈ Finset.range (35 - i), 2 ^ j := by
      apply Finset.sum_nbij' (fun k => 35 - k) (fun j => 35 - j)
      · intro k hk
        have := Finset.mem_Ico.mp hk
        exact Finset.mem_range.mpr (by omega)
      · intro j hj
        have := Finset.mem_range.mp hj
        exact Finset.mem_Ico.mpr (by omega)
      · intro k hk
        have := Finset.mem_Ico.mp hk
        omega
      · intro j hj
        have := Finset.mem_range.mp hj
        omega
      · intro k _
        rfl
    have h3 := sum_two_pow (35 - i)
    have h4 : (1 : ℕ) ≤ 2 ^ (35 - i) := Nat.one_le_two_pow
    omega
  have hstep : bbit p i * 2 ^ (35 - i) + 2 ^ (35 - i)
      ≤ bbit q i * 2 ^ (35 - i) := by
    have h5 : bbit p i + 1 ≤ bbit q i := hlt
    calc bbit p i * 2 ^ (35 - i) + 2 ^ (35 - i)
        = (bbit p i + 1) * 2 ^ (35 - i) := by ring
      _ ≤ bbit q i * 2 ^ (35 - i) := mul_le_mul_right' h5 _
  omega

open scoped Classical in
/-- **Existence of a lex-maximal enumeration**: every nine-point configuration
admits an injective enumeration whose `bondCode` dominates every other
enumeration of the same set. -/
lemma exists_lexmax_enum {X : Finset E3} (h9 : X.card = 9) :
    ∃ p : Fin 9 → E3, Function.Injective p ∧ Finset.image p Finset.univ = X ∧
      ∀ q : Fin 9 → E3, Function.Injective q → Finset.image q Finset.univ = X →
        bondCode q ≤ bondCode p := by
  classical
  have hcard : Fintype.card {x // x ∈ X} = Fintype.card (Fin 9) := by
    rw [Fintype.card_coe, h9, Fintype.card_fin]
  set e : {x // x ∈ X} ≃ Fin 9 := Fintype.equivFinOfCardEq hcard with he
  set p0 : Fin 9 → E3 := fun i => (e.symm i : E3) with hp0
  have hp0inj : Function.Injective p0 := by
    intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  have hp0im : Finset.image p0 Finset.univ = X := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact (e.symm i).2
    · rw [h9, Finset.card_image_of_injective _ hp0inj, Finset.card_univ,
        Fintype.card_fin]
  obtain ⟨σmax, _, hσmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Equiv.Perm (Fin 9)))
    (fun σ => bondCode (p0 ∘ σ)) ⟨1, Finset.mem_univ 1⟩
  refine ⟨p0 ∘ σmax, hp0inj.comp σmax.injective, ?_, ?_⟩
  · rw [← hp0im]
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr ⟨σmax i, Finset.mem_univ _, rfl⟩
    · simp only [Finset.card_image_of_injective _ hp0inj,
        Finset.card_image_of_injective _ (hp0inj.comp σmax.injective), le_refl]
  · intro q hqinj hqim
    have hmem : ∀ i, q i ∈ X := by
      intro i
      rw [← hqim]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    set f : Fin 9 → Fin 9 := fun i => e ⟨q i, hmem i⟩ with hf
    have hfinj : Function.Injective f := by
      intro a b hab
      apply hqinj
      have h6 := e.injective hab
      exact congrArg Subtype.val h6
    have hfsurj : Function.Surjective f :=
      Finite.surjective_of_injective hfinj
    set σ : Equiv.Perm (Fin 9) := Equiv.ofBijective f ⟨hfinj, hfsurj⟩ with hσ
    have hqeq : q = p0 ∘ σ := by
      funext i
      simp only [hσ, Function.comp_apply, Equiv.ofBijective_apply, hf, hp0]
      rw [Equiv.symm_apply_apply]
    rw [hqeq]
    exact hσmax σ (Finset.mem_univ σ)

end Emin9T

end Kissing3D
