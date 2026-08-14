import ContactNumbers.Emin8Kills

set_option linter.style.header false
set_option maxHeartbeats 1000000

/-!
# Towards `E_min(8) = −18`: the assembly layer

The first reduction is recursion into `seven_particle_bound`: deleting a particle
removes twice its degree from the contact count, so in an eight-particle configuration
with 37 or more ordered contacts every particle has at least four bonds — otherwise the
remaining seven particles would carry more than 30 ordered contacts.
-/

namespace Kissing3D

open Finset

open scoped Classical in
/-- Deleting a particle removes exactly twice its degree from the contact count. -/
lemma contactCount_erase {X : Finset E3} {v : E3} (hv : v ∈ X) :
    contactCount (X.erase v) = contactCount X - 2 * (neighbors X v).card := by
  have hvnotin : v ∉ X.erase v := Finset.notMem_erase v X
  have hins : insert v (X.erase v) = X := Finset.insert_erase hv
  -- degree of `v` is unchanged by passing to the erased set, and `v` is not a neighbour
  have hnbv : neighbors X v = (X.erase v).filter (fun w => dist v w = 1) := by
    rw [neighbors, ← hins, Finset.filter_insert]
    simp [dist_self]
  -- neighbours of `z ≠ v` split off the possible bond to `v`
  have hsplit : ∀ z ∈ X.erase v,
      (neighbors X z).card
        = (neighbors (X.erase v) z).card + (if dist z v = 1 then 1 else 0) := by
    intro z hz
    have h1 : neighbors (X.erase v) z = (neighbors X z).erase v := by
      rw [neighbors, neighbors, Finset.filter_erase]
    by_cases hd : dist z v = 1
    · have hvmem : v ∈ neighbors X z := Finset.mem_filter.mpr ⟨hv, hd⟩
      rw [if_pos hd, h1, Finset.card_erase_of_mem hvmem]
      have hpos : 0 < (neighbors X z).card := Finset.card_pos.mpr ⟨v, hvmem⟩
      omega
    · have hvnot : v ∉ neighbors X z := fun hmem => hd (Finset.mem_filter.mp hmem).2
      rw [if_neg hd, add_zero, h1, Finset.erase_eq_of_notMem hvnot]
  have hsum : contactCount X
      = (neighbors X v).card + ∑ z ∈ X.erase v, (neighbors X z).card :=
    (Finset.add_sum_erase X (fun z => (neighbors X z).card) hv).symm
  have hsum2 : ∑ z ∈ X.erase v, (neighbors X z).card
      = contactCount (X.erase v) + (neighbors X v).card := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.card_filter, hnbv]
    congr 1
    apply Finset.filter_congr
    intro z _
    constructor
    · intro h; rwa [dist_comm]
    · intro h; rwa [dist_comm]
  omega

open scoped Classical in
/-- **Minimum degree four**: in an eight-particle hard-core configuration with at least
37 ordered contacts, every particle has at least four bonds — deleting a particle of
degree three or less would leave seven particles with at least 31 ordered contacts,
contradicting `seven_particle_bound`. -/
theorem degree_ge_four {X : Finset E3} (hX : HardCore X) (h8 : X.card = 8)
    (hcc : 37 ≤ contactCount X) : ∀ v ∈ X, 4 ≤ (neighbors X v).card := by
  intro v hv
  by_contra hlt
  push Not at hlt
  have herase := contactCount_erase (X := X) (v := v) hv
  have hY : (X.erase v).card = 7 := by rw [Finset.card_erase_of_mem hv, h8]
  have hXY : HardCore (X.erase v) := fun a ha b hb hab =>
    hX a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
  have hbound := seven_particle_bound hXY hY
  omega

/-! ### The certified kill tree: codec and checker

The finite fact is delivered as a machine-generated decision tree over the 28
vertex-major pair decisions: `0` opens a branch (edge / non-edge on the next pair),
`2·cert + 1` is a kill leaf. The walker `walk` verifies the tree shape and every leaf
certificate; coverage of all bond patterns is intrinsic to the tree shape. -/

namespace Emin8T

/-- First vertex of the `k`-th pair of `Fin 8` in incremental (colex) order:
`(0,1), (0,2), (1,2), (0,3), …` — all pairs within `{0..t}` precede vertex `t+1`. -/
def pairFst (k : ℕ) : ℕ :=
  if k < 1 then 0 else if k < 3 then k - 1 else if k < 6 then k - 3
  else if k < 10 then k - 6 else if k < 15 then k - 10 else if k < 21 then k - 15
  else k - 21

/-- Second vertex of the `k`-th pair. -/
def pairSnd (k : ℕ) : ℕ :=
  if k < 1 then 1 else if k < 3 then 2 else if k < 6 then 3 else if k < 10 then 4
  else if k < 15 then 5 else if k < 21 then 6 else 7

/-- Index of the pair `{i, j}` (for `i < j < 8`) in incremental order:
`j·(j−1)/2 + i`. -/
def pairIdx8 (i j : ℕ) : ℕ :=
  let a := min i j
  let b := max i j
  b * (b - 1) / 2 + a

/-- Bond test against the decided edge list. -/
def eMem (es : List ℕ) (i j : ℕ) : Bool :=
  decide (i < 8) && decide (j < 8) && (i != j) && es.contains (pairIdx8 i j)

/-- Base-8 payload field `k` of a packed certificate (after the base-16 kind digit). -/
def fld (cert k : ℕ) : ℕ := cert / (16 * 8 ^ k) % 8

/-- Certificate check against the decided edge and non-edge index lists. -/
def checkCert (es ns : List ℕ) (cert : ℕ) : Bool :=
  let kind := cert % 16
  if kind == 0 then
    -- a vertex with at least four decided non-bonds
    let v := fld cert 0
    decide (v < 8) &&
      decide (4 ≤ (ns.filter (fun k => (pairFst k == v) || (pairSnd k == v))).length)
  else if kind == 1 then
    decide (10 ≤ ns.length)
  else if kind == 2 then
    let a := fld cert 0; let b := fld cert 1; let c := fld cert 2
    let d := fld cert 3; let e := fld cert 4
    eMem es a b && eMem es a c && eMem es a d && eMem es a e &&
    eMem es b c && eMem es b d && eMem es b e &&
    eMem es c d && eMem es c e && eMem es d e
  else if kind == 3 then
    let u := fld cert 0; let v := fld cert 1; let c := fld cert 2
    let x := fld cert 3; let y := fld cert 4; let z := fld cert 5
    eMem es u v && eMem es u c && eMem es v c && eMem es u x && eMem es v x &&
    eMem es u y && eMem es v y && eMem es u z && eMem es v z &&
    eMem es c x && eMem es c y && eMem es c z &&
    (x != y) && (x != z) && (y != z)
  else if kind == 4 then
    let u := fld cert 0; let v := fld cert 1
    let w1 := fld cert 2; let w2 := fld cert 3; let w3 := fld cert 4
    let w4 := fld cert 5; let w5 := fld cert 6; let w6 := fld cert 7
    eMem es u v &&
    eMem es u w1 && eMem es v w1 && eMem es u w2 && eMem es v w2 &&
    eMem es u w3 && eMem es v w3 && eMem es u w4 && eMem es v w4 &&
    eMem es u w5 && eMem es v w5 && eMem es u w6 && eMem es v w6 &&
    (w1 != w2) && (w1 != w3) && (w1 != w4) && (w1 != w5) && (w1 != w6) &&
    (w2 != w3) && (w2 != w4) && (w2 != w5) && (w2 != w6) &&
    (w3 != w4) && (w3 != w5) && (w3 != w6) &&
    (w4 != w5) && (w4 != w6) && (w5 != w6)
  else if kind == 5 then
    let a := fld cert 0; let b := fld cert 1; let c := fld cert 2
    let w1 := fld cert 3; let w2 := fld cert 4; let w3 := fld cert 5
    (a != b) && (a != c) && (b != c) &&
    (w1 != w2) && (w1 != w3) && (w2 != w3) &&
    eMem es a w1 && eMem es b w1 && eMem es c w1 &&
    eMem es a w2 && eMem es b w2 && eMem es c w2 &&
    eMem es a w3 && eMem es b w3 && eMem es c w3
  else if kind == 6 then
    -- P1: labels 0..5 shell, 6 cone
    let m := fun t => fld cert t
    (List.range 7).all (fun t => decide (m t < 8)) &&
    ((List.range 7).all fun t => ((List.range t).all fun t' => m t != m t')) &&
    eMem es (m 0) (m 3) && eMem es (m 0) (m 4) && eMem es (m 0) (m 5) &&
    eMem es (m 1) (m 2) && eMem es (m 1) (m 4) && eMem es (m 1) (m 5) &&
    eMem es (m 2) (m 3) && eMem es (m 2) (m 4) && eMem es (m 3) (m 4) &&
    eMem es (m 0) (m 6) && eMem es (m 1) (m 6) && eMem es (m 2) (m 6) &&
    eMem es (m 3) (m 6) && eMem es (m 4) (m 6) && eMem es (m 5) (m 6)
  else if kind == 7 then
    -- P4
    let m := fun t => fld cert t
    (List.range 7).all (fun t => decide (m t < 8)) &&
    ((List.range 7).all fun t => ((List.range t).all fun t' => m t != m t')) &&
    eMem es (m 0) (m 1) && eMem es (m 0) (m 4) && eMem es (m 0) (m 5) &&
    eMem es (m 1) (m 2) && eMem es (m 1) (m 3) && eMem es (m 2) (m 3) &&
    eMem es (m 2) (m 5) && eMem es (m 3) (m 4) && eMem es (m 4) (m 5) &&
    eMem es (m 0) (m 6) && eMem es (m 1) (m 6) && eMem es (m 2) (m 6) &&
    eMem es (m 3) (m 6) && eMem es (m 4) (m 6) && eMem es (m 5) (m 6)
  else if kind == 8 then
    -- P5: m 6 = centre, m 0 = the non-neighbour
    let m := fun t => fld cert t
    (List.range 7).all (fun t => decide (m t < 8)) &&
    ((List.range 7).all fun t => ((List.range t).all fun t' => m t != m t')) &&
    eMem es (m 0) (m 3) && eMem es (m 0) (m 4) && eMem es (m 0) (m 5) &&
    eMem es (m 1) (m 2) && eMem es (m 1) (m 4) && eMem es (m 1) (m 5) &&
    eMem es (m 2) (m 3) && eMem es (m 2) (m 5) && eMem es (m 3) (m 4) &&
    eMem es (m 1) (m 6) && eMem es (m 2) (m 6) && eMem es (m 3) (m 6) &&
    eMem es (m 4) (m 6) && eMem es (m 5) (m 6)
  else if kind == 9 then
    -- degree order: position i's maximal degree falls below position i+1's minimum
    let i := fld cert 0
    decide (i < 7) &&
      decide (8 ≤ (es.filter (fun k => (pairFst k == i+1) || (pairSnd k == i+1))).length
        + (ns.filter (fun k => (pairFst k == i) || (pairSnd k == i))).length)
  else false

/-- Walk the serialized tree: `0` = branch on pair `k`, odd = kill leaf. Returns the
unconsumed tail on success. -/
def walk : ℕ → List ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, _ => none
  | _, [], _, _, _ => none
  | fuel + 1, c :: rest, k, es, ns =>
    if c == 0 then
      if k < 28 then
        match walk fuel rest (k + 1) (k :: es) ns with
        | none => none
        | some rest2 => walk fuel rest2 (k + 1) es (k :: ns)
      else none
    else if checkCert es ns ((c - 1) / 2) then some rest else none

/-- Composition: a sub-walk returning remainder `r` extends over an appended tail. -/
lemma walk_append {fuel : ℕ} {l1 l2 r : List ℕ} {k : ℕ} {es ns : List ℕ}
    (h : walk fuel l1 k es ns = some r) :
    walk fuel (l1 ++ l2) k es ns = some (r ++ l2) := by
  induction fuel generalizing l1 r k es ns with
  | zero => simp [walk] at h
  | succ fuel ih =>
    match l1 with
    | [] => simp [walk] at h
    | c :: rest =>
      rw [List.cons_append]
      rw [show walk (fuel + 1) (c :: rest) k es ns
          = (if c == 0 then
              if k < 28 then
                match walk fuel rest (k + 1) (k :: es) ns with
                | none => none
                | some rest2 => walk fuel rest2 (k + 1) es (k :: ns)
              else none
            else if checkCert es ns ((c - 1) / 2) then some rest else none) from rfl] at h
      rw [show walk (fuel + 1) ((c :: (rest ++ l2))) k es ns
          = (if c == 0 then
              if k < 28 then
                match walk fuel (rest ++ l2) (k + 1) (k :: es) ns with
                | none => none
                | some rest2 => walk fuel rest2 (k + 1) es (k :: ns)
              else none
            else if checkCert es ns ((c - 1) / 2) then some (rest ++ l2)
            else none) from rfl]
      by_cases hc : c == 0
      · rw [if_pos hc] at h ⊢
        by_cases hk : k < 28
        · rw [if_pos hk] at h ⊢
          cases hw : walk fuel rest (k + 1) (k :: es) ns with
          | none => rw [hw] at h; simp at h
          | some rest2 =>
            rw [hw] at h
            simp only at h
            rw [ih hw]
            simp only
            exact ih h
        · rw [if_neg hk] at h
          exact absurd h (by simp)
      · rw [if_neg hc] at h ⊢
        by_cases hcc : checkCert es ns ((c - 1) / 2)
        · rw [if_pos hcc] at h ⊢
          simp only [Option.some.injEq] at h
          rw [h]
        · rw [if_neg hcc] at h
          exact absurd h (by simp)

/-- Codec facts, kernel-checked: decoding inverts encoding on the 28 pair indices. -/
lemma pair_codec : ∀ i < 8, ∀ j < 8, i ≠ j →
    pairIdx8 i j < 28 ∧ pairFst (pairIdx8 i j) = min i j ∧
      pairSnd (pairIdx8 i j) = max i j := by decide

/-- Distinct pair indices decode to distinct pairs. -/
lemma pair_decode_inj : ∀ i < 28, ∀ i' < 28,
    pairFst i = pairFst i' → pairSnd i = pairSnd i' → i = i' := by decide

/-- Decoded endpoints are ordered and bounded. -/
lemma pair_decode_lt : ∀ i < 28, pairFst i < pairSnd i ∧ pairSnd i < 8 := by decide

open scoped Classical in
/-- The unordered bonded pairs, over an enumeration of the configuration. -/
lemma contactCount_eq_twice_unordered {n : ℕ} {X : Finset E3} {p : Fin n → E3}
    (hpinj : Function.Injective p) (hXim : Finset.image p Finset.univ = X) :
    contactCount X = 2 * ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun q => q.1 < q.2 ∧ dist (p q.1) (p q.2) = 1)).card := by
  classical
  have hpmem : ∀ i, p i ∈ X := by
    intro i
    rw [← hXim]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hsum : ∑ z ∈ X, (neighbors X z).card = ∑ i : Fin n, (neighbors X (p i)).card := by
    refine (Finset.sum_bij (fun i _ => p i) (fun i _ => hpmem i)
      (fun i _ j _ h => hpinj h) ?_ (fun i _ => rfl)).symm
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (by rw [hXim]; exact hz)
    exact ⟨i, Finset.mem_univ i, rfl⟩
  set A : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun q => dist (p q.1) (p q.2) = 1) with hA
  have hAcard : A.card = contactCount X := by
    rw [hA, Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun q _ => Finset.mem_univ _), contactCount, hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hinj2 : Set.InjOn (fun q : Fin n × Fin n => p q.2)
        ((Finset.univ.filter (fun q : Fin n × Fin n => dist (p q.1) (p q.2) = 1)).filter
          (fun q => q.1 = i)) := by
      intro q hq q' hq' hpq
      have h1 := (Finset.mem_filter.mp hq).2
      have h2 := (Finset.mem_filter.mp hq').2
      exact Prod.ext (h1.trans h2.symm) (hpinj hpq)
    have hfib : ((Finset.univ.filter
        (fun q : Fin n × Fin n => dist (p q.1) (p q.2) = 1)).filter
          (fun q => q.1 = i)).image (fun q => p q.2) = neighbors X (p i) := by
      ext w
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, neighbors]
      constructor
      · rintro ⟨q, ⟨hd, hq1⟩, rfl⟩
        exact ⟨hpmem _, by rw [← hq1]; exact hd⟩
      · rintro ⟨hwX, hwd⟩
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (by rw [hXim]; exact hwX)
        exact ⟨(i, j), ⟨hwd, rfl⟩, rfl⟩
    rw [← hfib, Finset.card_image_of_injOn hinj2]
  set U := A.filter (fun q => q.1 < q.2) with hU
  set W := A.filter (fun q => q.2 < q.1) with hW
  have hAne : ∀ q ∈ A, q.1 ≠ q.2 := by
    intro q hq
    have hd := (Finset.mem_filter.mp hq).2
    intro h
    rw [h, dist_self] at hd
    norm_num at hd
  have hsplit : A.card = U.card + W.card := by
    rw [hU, hW, ← Finset.card_filter_add_card_filter_not (s := A) (fun q => q.1 < q.2)]
    congr 1
    congr 1
    apply Finset.filter_congr
    intro q hq
    have hne := hAne q hq
    simp only [not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (fun hh => hne hh.symm), fun h => le_of_lt h⟩
  have hWU : W.card = U.card := by
    apply Finset.card_bij (fun q _ => Prod.swap q)
    · intro q hq
      obtain ⟨hqA, hlt⟩ := Finset.mem_filter.mp hq
      have hd := (Finset.mem_filter.mp hqA).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [Prod.fst_swap, Prod.snd_swap, dist_comm]; exact hd
      · rw [Prod.fst_swap, Prod.snd_swap]; exact hlt
    · intro q hq q' hq' h
      exact Prod.swap_injective h
    · intro q hq
      obtain ⟨hqA, hlt⟩ := Finset.mem_filter.mp hq
      have hd := (Finset.mem_filter.mp hqA).2
      refine ⟨Prod.swap q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩, ?_⟩, (Prod.swap_swap q).symm⟩
      · rw [Prod.fst_swap, Prod.snd_swap, dist_comm]; exact hd
      · rw [Prod.fst_swap, Prod.snd_swap]; exact hlt
  have hUU : U = (Finset.univ : Finset (Fin n × Fin n)).filter
      (fun q => q.1 < q.2 ∧ dist (p q.1) (p q.2) = 1) := by
    rw [hU, hA, Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    exact and_comm
  rw [← hUU]
  omega

/-- The other endpoint of pair `k`, seen from vertex `v`. -/
private def ptn (v k : ℕ) : ℕ := if pairFst k = v then pairSnd k else pairFst k

/-- Interpret a raw certificate vertex as a particle. -/
private def qf (p : Fin 8 → E3) (n : ℕ) : E3 := p ⟨n % 8, Nat.mod_lt _ (by norm_num)⟩

open scoped Classical in
/-- **Certificate soundness**: no verified kill certificate is compatible with a
hard-core eight-particle realization carrying at least 38 ordered contacts. -/
theorem checkCert_sound {X : Finset E3} (hX : HardCore X) {p : Fin 8 → E3}
    (hpmem : ∀ i, p i ∈ X) (hpinj : Function.Injective p)
    (h8 : X.card = 8) (hXim : Finset.image p Finset.univ = X)
    (hcc : 38 ≤ contactCount X)
    (hsort : ∀ i j : Fin 8, i ≤ j → (neighbors X (p j)).card ≤ (neighbors X (p i)).card)
    {es ns : List ℕ}
    (hes : ∀ i ∈ es, i < 28 ∧ dist (qf p (pairFst i)) (qf p (pairSnd i)) = 1)
    (hns : ∀ i ∈ ns, i < 28 ∧ ¬ dist (qf p (pairFst i)) (qf p (pairSnd i)) = 1)
    (hesnd : es.Nodup) (hnsnd : ns.Nodup)
    {cert : ℕ} (hkill : checkCert es ns cert = true) : False := by
  -- particle-level helpers
  have hqmem : ∀ m : ℕ, qf p m ∈ X := fun m => hpmem _
  have hqne : ∀ {i j : ℕ}, i < 8 → j < 8 → i ≠ j → qf p i ≠ qf p j := by
    intro i j hi hj hne heq
    apply hne
    have hv := hpinj heq
    simp only [Fin.mk.injEq] at hv
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
  have hqdist : ∀ {i j : ℕ}, eMem es i j = true → dist (qf p i) (qf p j) = 1 := by
    intro i j h
    simp only [eMem, Bool.and_eq_true, and_assoc, decide_eq_true_eq, bne_iff_ne,
      List.contains_iff_mem] at h
    obtain ⟨hi, hj, hne, hmem⟩ := h
    have hd := (hes _ hmem).2
    obtain ⟨_, hf, hs⟩ := pair_codec i hi j hj hne
    rw [hf, hs] at hd
    rcases lt_or_gt_of_ne hne with h' | h'
    · rwa [min_eq_left h'.le, max_eq_right h'.le] at hd
    · rw [min_eq_right h'.le, max_eq_left h'.le] at hd
      rwa [dist_comm]
  have hqlt : ∀ {i j : ℕ}, eMem es i j = true → i < 8 ∧ j < 8 ∧ i ≠ j := by
    intro i j h
    simp only [eMem, Bool.and_eq_true, and_assoc, decide_eq_true_eq, bne_iff_ne,
      List.contains_iff_mem] at h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hmemN : ∀ {u t : ℕ}, eMem es u t = true → qf p t ∈ neighbors X (qf p u) := by
    intro u t h
    exact Finset.mem_filter.mpr ⟨hqmem t, hqdist h⟩
  have hcomm2 : ∀ {u v t : ℕ}, eMem es u t = true → eMem es v t = true →
      qf p t ∈ neighbors X (qf p u) ∩ neighbors X (qf p v) := by
    intro u v t h1 h2
    exact Finset.mem_inter.mpr ⟨hmemN h1, hmemN h2⟩
  -- dispatch on the kind
  have hb : cert % 16 = 0 ∨ cert % 16 = 1 ∨ cert % 16 = 2 ∨ cert % 16 = 3 ∨
      cert % 16 = 4 ∨ cert % 16 = 5 ∨ cert % 16 = 6 ∨ cert % 16 = 7 ∨
      cert % 16 = 8 ∨ cert % 16 = 9 ∨ 10 ≤ cert % 16 := by omega
  rcases hb with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
  · -- kind 0: min-degree
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    obtain ⟨hv8, hlen⟩ := hkill
    set v := fld cert 0 with hvdef
    set l := ns.filter (fun k => (pairFst k == v) || (pairSnd k == v)) with hldef
    have hlsub : ∀ k ∈ l, k ∈ ns ∧ (pairFst k = v ∨ pairSnd k = v) := by
      intro k hkmem
      rw [hldef] at hkmem
      have h1 := List.mem_of_mem_filter hkmem
      have h2 := List.of_mem_filter hkmem
      simp only [Bool.or_eq_true, beq_iff_eq] at h2
      exact ⟨h1, h2⟩
    have hlnd : l.Nodup := by
      rw [hldef]
      exact hnsnd.filter _
    have hp1 : ∀ k ∈ l, ptn v k < 8 ∧ ptn v k ≠ v ∧
        ¬ dist (qf p v) (qf p (ptn v k)) = 1 := by
      intro k hkmem
      obtain ⟨hkns, hkinc⟩ := hlsub k hkmem
      obtain ⟨hk28, hnd⟩ := hns k hkns
      obtain ⟨hfs, hs8⟩ := pair_decode_lt k hk28
      by_cases hfeq : pairFst k = v
      · refine ⟨by simp only [ptn, if_pos hfeq]; omega,
          by simp only [ptn, if_pos hfeq]; omega, ?_⟩
        simp only [ptn, if_pos hfeq]
        rw [← hfeq]
        exact hnd
      · have hseq : pairSnd k = v := by
          rcases hkinc with hc | hc
          · exact absurd hc hfeq
          · exact hc
        refine ⟨by simp only [ptn, if_neg hfeq]; omega,
          by simp only [ptn, if_neg hfeq]; exact hfeq, ?_⟩
        simp only [ptn, if_neg hfeq]
        intro hd
        apply hnd
        rw [← hseq, dist_comm] at hd
        exact hd
    have hpinj2 : ∀ k ∈ l, ∀ k' ∈ l, ptn v k = ptn v k' → k = k' := by
      intro k hkmem k' hkmem' hpp
      obtain ⟨hkns, hkinc⟩ := hlsub k hkmem
      obtain ⟨hkns', hkinc'⟩ := hlsub k' hkmem'
      obtain ⟨hk28, _⟩ := hns k hkns
      obtain ⟨hk28', _⟩ := hns k' hkns'
      obtain ⟨hlt, h8'⟩ := pair_decode_lt k hk28
      obtain ⟨hlt', h8''⟩ := pair_decode_lt k' hk28'
      simp only [ptn] at hpp
      apply pair_decode_inj k hk28 k' hk28'
      all_goals
        rcases hkinc with hc | hc <;> rcases hkinc' with hc' | hc' <;>
        [ (rw [if_pos hc, if_pos hc'] at hpp);
          (rw [if_pos hc, if_neg (by omega : ¬ pairFst k' = v)] at hpp);
          (rw [if_neg (by omega : ¬ pairFst k = v), if_pos hc'] at hpp);
          (rw [if_neg (by omega : ¬ pairFst k = v),
               if_neg (by omega : ¬ pairFst k' = v)] at hpp) ] <;>
        omega
    -- the four partner particles exclude four slots of the seven
    have hlen4 : 4 ≤ l.length := hlen
    have hTsub : l.toFinset.card = l.length := List.toFinset_card_of_nodup hlnd
    set PS : Finset E3 := l.toFinset.image (fun k => qf p (ptn v k)) with hPS
    have hPScard : 4 ≤ PS.card := by
      rw [hPS, Finset.card_image_of_injOn]
      · omega
      · intro k hk k' hk' heq
        rw [Finset.mem_coe, List.mem_toFinset] at hk hk'
        obtain ⟨hlt8, _, _⟩ := hp1 k hk
        obtain ⟨hlt8', _, _⟩ := hp1 k' hk'
        by_cases hpe : ptn v k = ptn v k'
        · exact hpinj2 k hk k' hk' hpe
        · exact absurd heq (hqne hlt8 hlt8' hpe).elim
    have hPSdisj : ∀ w ∈ PS, w ∈ X.erase (qf p v) ∧ w ∉ neighbors X (qf p v) := by
      intro w hw
      rw [hPS] at hw
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
      rw [List.mem_toFinset] at hk
      obtain ⟨hlt8, hnev, hnd⟩ := hp1 k hk
      refine ⟨Finset.mem_erase.mpr ⟨hqne hlt8 (by omega) hnev, hqmem _⟩, ?_⟩
      intro hmem
      exact hnd (Finset.mem_filter.mp hmem).2
    have hnb : (neighbors X (qf p v)).card ≤ 3 := by
      have hunion : neighbors X (qf p v) ∪ PS ⊆ X.erase (qf p v) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact Finset.mem_erase.mpr ⟨fun h => by
            have := (Finset.mem_filter.mp hw).2
            rw [h, dist_self] at this
            norm_num at this, (Finset.mem_filter.mp hw).1⟩
        · exact (hPSdisj w hw).1
      have hdisj : Disjoint (neighbors X (qf p v)) PS := by
        rw [Finset.disjoint_right]
        intro w hw
        exact (hPSdisj w hw).2
      have hcard7 : (X.erase (qf p v)).card = 7 := by
        rw [Finset.card_erase_of_mem (hqmem v), h8]
      have := Finset.card_le_card hunion
      rw [Finset.card_union_of_disjoint hdisj] at this
      omega
    have hd4 := degree_ge_four hX h8 (by omega) (qf p v) (hqmem v)
    omega
  · -- kind 1: ten decided non-bonds
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    have hU := contactCount_eq_twice_unordered hpinj hXim
    set U := (Finset.univ : Finset (Fin 8 × Fin 8)).filter
      (fun q => q.1 < q.2 ∧ dist (p q.1) (p q.2) = 1) with hUdef
    have hU19 : 19 ≤ U.card := by omega
    set T : Finset (Fin 8 × Fin 8) := ns.toFinset.image
      (fun k => ((⟨pairFst k % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8),
                 (⟨pairSnd k % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8))) with hTdef
    have hT10 : 10 ≤ T.card := by
      rw [hTdef, Finset.card_image_of_injOn]
      · rw [List.toFinset_card_of_nodup hnsnd]
        exact hkill
      · intro k hk1 k' hk2 heq
        rw [Finset.mem_coe, List.mem_toFinset] at hk1 hk2
        obtain ⟨hk28, _⟩ := hns k hk1
        obtain ⟨hk28', _⟩ := hns k' hk2
        obtain ⟨hlt, h8'⟩ := pair_decode_lt k hk28
        obtain ⟨hlt', h8''⟩ := pair_decode_lt k' hk28'
        have h1 := congrArg (fun q : Fin 8 × Fin 8 => q.1.val) heq
        have h2 := congrArg (fun q : Fin 8 × Fin 8 => q.2.val) heq
        simp only at h1 h2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
        rw [Nat.mod_eq_of_lt h8', Nat.mod_eq_of_lt h8''] at h2
        exact pair_decode_inj k hk28 k' hk28' h1 h2
    have hTdisjU : Disjoint T U := by
      rw [Finset.disjoint_left]
      intro q hqT hqU
      rw [hTdef] at hqT
      obtain ⟨k, hkmem, rfl⟩ := Finset.mem_image.mp hqT
      rw [List.mem_toFinset] at hkmem
      obtain ⟨hk28, hnd⟩ := hns k hkmem
      have hd := (Finset.mem_filter.mp hqU).2.2
      exact hnd hd
    have hTU : T ∪ U ⊆ (Finset.univ : Finset (Fin 8 × Fin 8)).filter
        (fun q => q.1 < q.2) := by
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · rw [hTdef] at hq
        obtain ⟨k, hkmem, rfl⟩ := Finset.mem_image.mp hq
        rw [List.mem_toFinset] at hkmem
        obtain ⟨hk28, _⟩ := hns k hkmem
        obtain ⟨hlt, h8'⟩ := pair_decode_lt k hk28
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [Fin.mk_lt_mk, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h8']
        exact hlt
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2.1⟩
    have h28 : ((Finset.univ : Finset (Fin 8 × Fin 8)).filter
        (fun q => q.1 < q.2)).card = 28 := by decide
    have hle := Finset.card_le_card hTU
    rw [Finset.card_union_of_disjoint hTdisjU] at hle
    omega
  · -- kind 2: K5
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    simp only [and_assoc] at hkill
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8', h9, h10⟩ := hkill
    exact Emin7.five_points_impossible (hqdist h1) (hqdist h2) (hqdist h3) (hqdist h4)
      (hqdist h5) (hqdist h6) (hqdist h7) (hqdist h8') (hqdist h9) (hqdist h10)
  · -- kind 3: ring degree three
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    simp only [and_assoc] at hkill
    obtain ⟨huv, huc, hvc, hux, hvx, huy, hvy, huz, hvz, hcx, hcy, hcz,
      hxy, hxz, hyz⟩ := hkill
    obtain ⟨_, hx8, _⟩ := hqlt hux
    obtain ⟨_, hy8, _⟩ := hqlt huy
    obtain ⟨_, hz8, _⟩ := hqlt huz
    exact common_degree_impossible hX (hqdist huv) (hcomm2 huc hvc) (hcomm2 hux hvx)
      (hcomm2 huy hvy) (hcomm2 huz hvz)
      (hqne hx8 hy8 hxy) (hqne hx8 hz8 hxz) (hqne hy8 hz8 hyz)
      (hqdist hcx) (hqdist hcy) (hqdist hcz)
  · -- kind 4: six common neighbours
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    simp only [and_assoc] at hkill
    obtain ⟨huv, hu1, hv1, hu2, hv2, hu3, hv3, hu4, hv4, hu5, hv5, hu6, hv6,
      h12', h13', h14', h15', h16', h23', h24', h25', h26', h34', h35', h36',
      h45', h46', h56'⟩ := hkill
    obtain ⟨_, hw18, _⟩ := hqlt hu1
    obtain ⟨_, hw28, _⟩ := hqlt hu2
    obtain ⟨_, hw38, _⟩ := hqlt hu3
    obtain ⟨_, hw48, _⟩ := hqlt hu4
    obtain ⟨_, hw58, _⟩ := hqlt hu5
    obtain ⟨_, hw68, _⟩ := hqlt hu6
    have hn12 := hqne hw18 hw28 h12'
    have hn13 := hqne hw18 hw38 h13'
    have hn14 := hqne hw18 hw48 h14'
    have hn15 := hqne hw18 hw58 h15'
    have hn16 := hqne hw18 hw68 h16'
    have hn23 := hqne hw28 hw38 h23'
    have hn24 := hqne hw28 hw48 h24'
    have hn25 := hqne hw28 hw58 h25'
    have hn26 := hqne hw28 hw68 h26'
    have hn34 := hqne hw38 hw48 h34'
    have hn35 := hqne hw38 hw58 h35'
    have hn36 := hqne hw38 hw68 h36'
    have hn45 := hqne hw48 hw58 h45'
    have hn46 := hqne hw48 hw68 h46'
    have hn56 := hqne hw58 hw68 h56'
    have hsub : ({qf p (fld cert 2), qf p (fld cert 3), qf p (fld cert 4),
        qf p (fld cert 5), qf p (fld cert 6), qf p (fld cert 7)} : Finset E3)
        ⊆ neighbors X (qf p (fld cert 0)) ∩ neighbors X (qf p (fld cert 1)) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hcomm2 hu1 hv1
      · exact hcomm2 hu2 hv2
      · exact hcomm2 hu3 hv3
      · exact hcomm2 hu4 hv4
      · exact hcomm2 hu5 hv5
      · exact hcomm2 hu6 hv6
    have hcard6 : ({qf p (fld cert 2), qf p (fld cert 3), qf p (fld cert 4),
        qf p (fld cert 5), qf p (fld cert 6), qf p (fld cert 7)} : Finset E3).card = 6 := by
      rw [Finset.card_insert_of_notMem (by simp [hn12, hn13, hn14, hn15, hn16]),
        Finset.card_insert_of_notMem (by simp [hn23, hn24, hn25, hn26]),
        Finset.card_insert_of_notMem (by simp [hn34, hn35, hn36]),
        Finset.card_insert_of_notMem (by simp [hn45, hn46]),
        Finset.card_insert_of_notMem (by simp [hn56]), Finset.card_singleton]
    have hle5 := common_neighbors_le_five hX (hqdist huv)
    have hle6 := Finset.card_le_card hsub
    omega
  · -- kind 5: three particles with three common neighbours
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    simp only [and_assoc] at hkill
    obtain ⟨hab, hac, hbc, h12', h13', h23', haw1, hbw1, hcw1, haw2, hbw2, hcw2,
      haw3, hbw3, hcw3⟩ := hkill
    obtain ⟨ha8, hw18, _⟩ := hqlt haw1
    obtain ⟨hb8, _, _⟩ := hqlt hbw1
    obtain ⟨hc8, _, _⟩ := hqlt hcw1
    obtain ⟨_, hw28, _⟩ := hqlt haw2
    obtain ⟨_, hw38, _⟩ := hqlt haw3
    have hsub : ({qf p (fld cert 3), qf p (fld cert 4), qf p (fld cert 5)} : Finset E3)
        ⊆ neighbors X (qf p (fld cert 0)) ∩
          (neighbors X (qf p (fld cert 1)) ∩ neighbors X (qf p (fld cert 2))) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hmemN haw1, Finset.mem_inter.mpr ⟨hmemN hbw1, hmemN hcw1⟩⟩
      · exact Finset.mem_inter.mpr ⟨hmemN haw2, Finset.mem_inter.mpr ⟨hmemN hbw2, hmemN hcw2⟩⟩
      · exact Finset.mem_inter.mpr ⟨hmemN haw3, Finset.mem_inter.mpr ⟨hmemN hbw3, hmemN hcw3⟩⟩
    have hcard3 : ({qf p (fld cert 3), qf p (fld cert 4), qf p (fld cert 5)} :
        Finset E3).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp [hqne hw18 hw28 h12', hqne hw18 hw38 h13']),
        Finset.card_insert_of_notMem (by
          simp [hqne hw28 hw38 h23']), Finset.card_singleton]
    have hle2 := common_neighbors_triple_le_two X
      (hqne ha8 hb8 hab) (hqne ha8 hc8 hac) (hqne hb8 hc8 hbc)
    have hle := Finset.card_le_card hsub
    omega
  · -- kind 6: pattern_p1_impossible
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    simp only [and_assoc] at hkill
    obtain ⟨hall1, hall2, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hb0, hb1, hb2, hb3, hb4, hb5⟩ := hkill
    have hm8 : ∀ t, t < 7 → fld cert t < 8 := fun t ht => hall1 t ht
    have hmne : ∀ t t', t < 7 → t' < t → fld cert t ≠ fld cert t' :=
      fun t t' ht ht' => hall2 t ht t' ht'
    refine pattern_p1_impossible hX (c := qf p (fld cert 6))
      (u := fun k : Fin 6 => qf p (fld cert k.val)) (hqmem _) (fun i => hqmem _)
      ?_ ?_ (hqdist hs0) (hqdist hs1) (hqdist hs2) (hqdist hs3) (hqdist hs4) (hqdist hs5) (hqdist hs6) (hqdist hs7) (hqdist hs8)
    · intro a b hab
      by_contra hne
      have ha6 := a.isLt
      have hb6 := b.isLt
      have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_ge a.val b.val with h | h
      · exact hqne (hm8 _ (by omega)) (hm8 _ (by omega))
          (hmne b.val a.val (by omega) h) hab.symm
      · have h' : b.val < a.val := by omega
        exact hqne (hm8 _ (by omega)) (hm8 _ (by omega))
          (hmne a.val b.val (by omega) h') hab
    · intro i
      fin_cases i
      · rw [dist_comm]; exact hqdist hb0
      · rw [dist_comm]; exact hqdist hb1
      · rw [dist_comm]; exact hqdist hb2
      · rw [dist_comm]; exact hqdist hb3
      · rw [dist_comm]; exact hqdist hb4
      · rw [dist_comm]; exact hqdist hb5
  · -- kind 7: pattern_p4_impossible
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    simp only [and_assoc] at hkill
    obtain ⟨hall1, hall2, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hb0, hb1, hb2, hb3, hb4, hb5⟩ := hkill
    have hm8 : ∀ t, t < 7 → fld cert t < 8 := fun t ht => hall1 t ht
    have hmne : ∀ t t', t < 7 → t' < t → fld cert t ≠ fld cert t' :=
      fun t t' ht ht' => hall2 t ht t' ht'
    refine pattern_p4_impossible hX (c := qf p (fld cert 6))
      (u := fun k : Fin 6 => qf p (fld cert k.val)) (hqmem _) (fun i => hqmem _)
      ?_ ?_ (hqdist hs0) (hqdist hs1) (hqdist hs2) (hqdist hs3) (hqdist hs4) (hqdist hs5) (hqdist hs6) (hqdist hs7) (hqdist hs8)
    · intro a b hab
      by_contra hne
      have ha6 := a.isLt
      have hb6 := b.isLt
      have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_ge a.val b.val with h | h
      · exact hqne (hm8 _ (by omega)) (hm8 _ (by omega))
          (hmne b.val a.val (by omega) h) hab.symm
      · have h' : b.val < a.val := by omega
        exact hqne (hm8 _ (by omega)) (hm8 _ (by omega))
          (hmne a.val b.val (by omega) h') hab
    · intro i
      fin_cases i
      · rw [dist_comm]; exact hqdist hb0
      · rw [dist_comm]; exact hqdist hb1
      · rw [dist_comm]; exact hqdist hb2
      · rw [dist_comm]; exact hqdist hb3
      · rw [dist_comm]; exact hqdist hb4
      · rw [dist_comm]; exact hqdist hb5
  · -- kind 8: pattern_p5_impossible
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    simp only [and_assoc] at hkill
    obtain ⟨hall1, hall2, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hb0, hb1, hb2, hb3, hb4⟩ := hkill
    have hm8 : ∀ t, t < 7 → fld cert t < 8 := fun t ht => hall1 t ht
    have hmne : ∀ t t', t < 7 → t' < t → fld cert t ≠ fld cert t' :=
      fun t t' ht ht' => hall2 t ht t' ht'
    refine pattern_p5_impossible hX (c := qf p (fld cert 6))
      (u := fun k : Fin 6 => qf p (fld cert k.val)) (hqmem _) (fun i => hqmem _)
      ?_ (hqne (hm8 0 (by omega)) (hm8 6 (by omega))
        (hmne 6 0 (by omega) (by omega)).symm)
      (by rw [dist_comm]; exact hqdist hb0) (by rw [dist_comm]; exact hqdist hb1) (by rw [dist_comm]; exact hqdist hb2) (by rw [dist_comm]; exact hqdist hb3) (by rw [dist_comm]; exact hqdist hb4)
      (hqdist hs0) (hqdist hs1) (hqdist hs2) (hqdist hs3) (hqdist hs4) (hqdist hs5) (hqdist hs6) (hqdist hs7) (hqdist hs8)
    · intro a b hab
      by_contra hne
      have ha6 := a.isLt
      have hb6 := b.isLt
      have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_ge a.val b.val with h | h
      · exact hqne (hm8 _ (by omega)) (hm8 _ (by omega))
          (hmne b.val a.val (by omega) h) hab.symm
      · have h' : b.val < a.val := by omega
        exact hqne (hm8 _ (by omega)) (hm8 _ (by omega))
          (hmne a.val b.val (by omega) h') hab
  · -- kind 9: degree order violated
    simp only [checkCert, hk] at hkill
    norm_num at hkill
    obtain ⟨hi7, hlen⟩ := hkill
    set i := fld cert 0 with hidef
    -- lower bound: the decided edges at position i+1 are distinct neighbours
    set le' := es.filter (fun k => (pairFst k == i+1) || (pairSnd k == i+1)) with hledef
    have hlsub' : ∀ k ∈ le', k ∈ es ∧ (pairFst k = i+1 ∨ pairSnd k = i+1) := by
      intro k hkmem
      rw [hledef] at hkmem
      have h1 := List.mem_of_mem_filter hkmem
      have h2 := List.of_mem_filter hkmem
      simp only [Bool.or_eq_true, beq_iff_eq] at h2
      exact ⟨h1, h2⟩
    have hlnd' : le'.Nodup := by
      rw [hledef]
      exact hesnd.filter _
    have hp1' : ∀ k ∈ le', ptn (i+1) k < 8 ∧ ptn (i+1) k ≠ i+1 ∧
        dist (qf p (i+1)) (qf p (ptn (i+1) k)) = 1 := by
      intro k hkmem
      obtain ⟨hkes, hkinc⟩ := hlsub' k hkmem
      obtain ⟨hk28, hd⟩ := hes k hkes
      obtain ⟨hfs, hs8⟩ := pair_decode_lt k hk28
      by_cases hfeq : pairFst k = i+1
      · refine ⟨by simp only [ptn, if_pos hfeq]; omega,
          by simp only [ptn, if_pos hfeq]; omega, ?_⟩
        simp only [ptn, if_pos hfeq]
        rw [← hfeq]
        exact hd
      · have hseq : pairSnd k = i+1 := by
          rcases hkinc with hc | hc
          · exact absurd hc hfeq
          · exact hc
        refine ⟨by simp only [ptn, if_neg hfeq]; omega,
          by simp only [ptn, if_neg hfeq]; exact hfeq, ?_⟩
        simp only [ptn, if_neg hfeq]
        rw [← hseq, dist_comm]
        exact hd
    have hpinj2' : ∀ k ∈ le', ∀ k' ∈ le', ptn (i+1) k = ptn (i+1) k' → k = k' := by
      intro k hkmem k' hkmem' hpp
      obtain ⟨hkes, hkinc⟩ := hlsub' k hkmem
      obtain ⟨hkes', hkinc'⟩ := hlsub' k' hkmem'
      obtain ⟨hk28, _⟩ := hes k hkes
      obtain ⟨hk28', _⟩ := hes k' hkes'
      obtain ⟨hlt, h8'⟩ := pair_decode_lt k hk28
      obtain ⟨hlt', h8''⟩ := pair_decode_lt k' hk28'
      simp only [ptn] at hpp
      apply pair_decode_inj k hk28 k' hk28'
      all_goals
        rcases hkinc with hc | hc <;> rcases hkinc' with hc' | hc' <;>
        [ (rw [if_pos hc, if_pos hc'] at hpp);
          (rw [if_pos hc, if_neg (by omega : ¬ pairFst k' = i+1)] at hpp);
          (rw [if_neg (by omega : ¬ pairFst k = i+1), if_pos hc'] at hpp);
          (rw [if_neg (by omega : ¬ pairFst k = i+1),
               if_neg (by omega : ¬ pairFst k' = i+1)] at hpp) ] <;>
        omega
    have hTcard' : le'.toFinset.card = le'.length := List.toFinset_card_of_nodup hlnd'
    have hlow : le'.length ≤ (neighbors X (qf p (i+1))).card := by
      have hsubn : le'.toFinset.image (fun k => qf p (ptn (i+1) k))
          ⊆ neighbors X (qf p (i+1)) := by
        intro w hw
        obtain ⟨k, hkmem, rfl⟩ := Finset.mem_image.mp hw
        rw [List.mem_toFinset] at hkmem
        obtain ⟨_, _, hd⟩ := hp1' k hkmem
        exact Finset.mem_filter.mpr ⟨hqmem _, hd⟩
      have hcardim : (le'.toFinset.image (fun k => qf p (ptn (i+1) k))).card
          = le'.length := by
        rw [Finset.card_image_of_injOn, hTcard']
        intro k hk k' hk' heq
        rw [Finset.mem_coe, List.mem_toFinset] at hk hk'
        obtain ⟨hlt8, _, _⟩ := hp1' k hk
        obtain ⟨hlt8', _, _⟩ := hp1' k' hk'
        by_cases hpe : ptn (i+1) k = ptn (i+1) k'
        · exact hpinj2' k hk k' hk' hpe
        · exact absurd heq (hqne hlt8 hlt8' hpe).elim
      calc le'.length = _ := hcardim.symm
        _ ≤ _ := Finset.card_le_card hsubn
    -- upper bound: the decided non-edges at position i exclude neighbours
    set ln := ns.filter (fun k => (pairFst k == i) || (pairSnd k == i)) with hlndef
    have hlsub : ∀ k ∈ ln, k ∈ ns ∧ (pairFst k = i ∨ pairSnd k = i) := by
      intro k hkmem
      rw [hlndef] at hkmem
      have h1 := List.mem_of_mem_filter hkmem
      have h2 := List.of_mem_filter hkmem
      simp only [Bool.or_eq_true, beq_iff_eq] at h2
      exact ⟨h1, h2⟩
    have hlnnd : ln.Nodup := by
      rw [hlndef]
      exact hnsnd.filter _
    have hp1n : ∀ k ∈ ln, ptn i k < 8 ∧ ptn i k ≠ i ∧
        ¬ dist (qf p i) (qf p (ptn i k)) = 1 := by
      intro k hkmem
      obtain ⟨hkns, hkinc⟩ := hlsub k hkmem
      obtain ⟨hk28, hnd⟩ := hns k hkns
      obtain ⟨hfs, hs8⟩ := pair_decode_lt k hk28
      by_cases hfeq : pairFst k = i
      · refine ⟨by simp only [ptn, if_pos hfeq]; omega,
          by simp only [ptn, if_pos hfeq]; omega, ?_⟩
        simp only [ptn, if_pos hfeq]
        rw [← hfeq]
        exact hnd
      · have hseq : pairSnd k = i := by
          rcases hkinc with hc | hc
          · exact absurd hc hfeq
          · exact hc
        refine ⟨by simp only [ptn, if_neg hfeq]; omega,
          by simp only [ptn, if_neg hfeq]; exact hfeq, ?_⟩
        simp only [ptn, if_neg hfeq]
        intro hd
        apply hnd
        rw [← hseq, dist_comm] at hd
        exact hd
    have hpinj2n : ∀ k ∈ ln, ∀ k' ∈ ln, ptn i k = ptn i k' → k = k' := by
      intro k hkmem k' hkmem' hpp
      obtain ⟨hkns, hkinc⟩ := hlsub k hkmem
      obtain ⟨hkns', hkinc'⟩ := hlsub k' hkmem'
      obtain ⟨hk28, _⟩ := hns k hkns
      obtain ⟨hk28', _⟩ := hns k' hkns'
      obtain ⟨hlt, h8'⟩ := pair_decode_lt k hk28
      obtain ⟨hlt', h8''⟩ := pair_decode_lt k' hk28'
      simp only [ptn] at hpp
      apply pair_decode_inj k hk28 k' hk28'
      all_goals
        rcases hkinc with hc | hc <;> rcases hkinc' with hc' | hc' <;>
        [ (rw [if_pos hc, if_pos hc'] at hpp);
          (rw [if_pos hc, if_neg (by omega : ¬ pairFst k' = i)] at hpp);
          (rw [if_neg (by omega : ¬ pairFst k = i), if_pos hc'] at hpp);
          (rw [if_neg (by omega : ¬ pairFst k = i),
               if_neg (by omega : ¬ pairFst k' = i)] at hpp) ] <;>
        omega
    have hup : (neighbors X (qf p i)).card + ln.length ≤ 7 := by
      set PS : Finset E3 := ln.toFinset.image (fun k => qf p (ptn i k)) with hPS
      have hPScard : PS.card = ln.length := by
        rw [hPS, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hlnnd]
        intro k hk k' hk' heq
        rw [Finset.mem_coe, List.mem_toFinset] at hk hk'
        obtain ⟨hlt8, _, _⟩ := hp1n k hk
        obtain ⟨hlt8', _, _⟩ := hp1n k' hk'
        by_cases hpe : ptn i k = ptn i k'
        · exact hpinj2n k hk k' hk' hpe
        · exact absurd heq (hqne hlt8 hlt8' hpe).elim
      have hPSdisj : ∀ w ∈ PS, w ∈ X.erase (qf p i) ∧ w ∉ neighbors X (qf p i) := by
        intro w hw
        rw [hPS] at hw
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        rw [List.mem_toFinset] at hk
        obtain ⟨hlt8, hnev, hnd⟩ := hp1n k hk
        refine ⟨Finset.mem_erase.mpr ⟨hqne hlt8 (by omega) hnev, hqmem _⟩, ?_⟩
        intro hmem
        exact hnd (Finset.mem_filter.mp hmem).2
      have hunion : neighbors X (qf p i) ∪ PS ⊆ X.erase (qf p i) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact Finset.mem_erase.mpr ⟨fun h => by
            have := (Finset.mem_filter.mp hw).2
            rw [h, dist_self] at this
            norm_num at this, (Finset.mem_filter.mp hw).1⟩
        · exact (hPSdisj w hw).1
      have hdisj : Disjoint (neighbors X (qf p i)) PS := by
        rw [Finset.disjoint_right]
        intro w hw
        exact (hPSdisj w hw).2
      have hcard7 : (X.erase (qf p i)).card = 7 := by
        rw [Finset.card_erase_of_mem (hqmem i), h8]
      have hle := Finset.card_le_card hunion
      rw [Finset.card_union_of_disjoint hdisj, hPScard] at hle
      omega
    -- degree sortedness contradicts the two bounds
    have hqi : qf p i = p ⟨i, by omega⟩ := by
      simp only [qf]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt (by omega))
    have hqi1 : qf p (i+1) = p ⟨i+1, by omega⟩ := by
      simp only [qf]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt (by omega))
    have hs := hsort ⟨i, by omega⟩ ⟨i+1, by omega⟩ (by
      rw [Fin.mk_le_mk]; omega)
    rw [← hqi, ← hqi1] at hs
    omega
  · -- impossible kind
    have h0 : cert % 16 ≠ 0 := by omega
    have h1 : cert % 16 ≠ 1 := by omega
    have h2 : cert % 16 ≠ 2 := by omega
    have h3 : cert % 16 ≠ 3 := by omega
    have h4 : cert % 16 ≠ 4 := by omega
    have h5 : cert % 16 ≠ 5 := by omega
    have h6 : cert % 16 ≠ 6 := by omega
    have h7 : cert % 16 ≠ 7 := by omega
    have h8' : cert % 16 ≠ 8 := by omega
    have h9' : cert % 16 ≠ 9 := by omega
    simp [checkCert, beq_iff_eq, h0, h1, h2, h3, h4, h5, h6, h7, h8', h9'] at hkill

open scoped Classical in
/-- **Walk soundness**: a successful walk of any kill tree is incompatible with a
hard-core eight-particle realization carrying 38 ordered contacts. The branch at pair
`k` is decided by the realization itself. -/
theorem walk_impossible {X : Finset E3} (hX : HardCore X) {p : Fin 8 → E3}
    (hpmem : ∀ i, p i ∈ X) (hpinj : Function.Injective p)
    (h8 : X.card = 8) (hXim : Finset.image p Finset.univ = X)
    (hcc : 38 ≤ contactCount X)
    (hsort : ∀ i j : Fin 8, i ≤ j → (neighbors X (p j)).card ≤ (neighbors X (p i)).card) :
    ∀ (fuel : ℕ) (data : List ℕ) (k : ℕ) (es ns rest : List ℕ),
    walk fuel data k es ns = some rest →
    (∀ i ∈ es, i < 28 ∧ dist (qf p (pairFst i)) (qf p (pairSnd i)) = 1) →
    (∀ i ∈ ns, i < 28 ∧ ¬ dist (qf p (pairFst i)) (qf p (pairSnd i)) = 1) →
    es.Nodup → ns.Nodup → (∀ i ∈ es, i < k) → (∀ i ∈ ns, i < k) → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro data k es ns rest hwalk hes hns hesnd hnsnd heslt hnslt
    simp [walk] at hwalk
  | succ fuel ih =>
    intro data k es ns rest hwalk hes hns hesnd hnsnd heslt hnslt
    match data with
    | [] => simp [walk] at hwalk
    | c :: rest' =>
      rw [show walk (fuel + 1) (c :: rest') k es ns
          = (if c == 0 then
              if k < 28 then
                match walk fuel rest' (k + 1) (k :: es) ns with
                | none => none
                | some rest2 => walk fuel rest2 (k + 1) es (k :: ns)
              else none
            else if checkCert es ns ((c - 1) / 2) then some rest'
            else none) from rfl] at hwalk
      by_cases hc : c == 0
      · rw [if_pos hc] at hwalk
        by_cases hklt : k < 28
        · rw [if_pos hklt] at hwalk
          by_cases hbond : dist (qf p (pairFst k)) (qf p (pairSnd k)) = 1
          · cases hw : walk fuel rest' (k + 1) (k :: es) ns with
            | none => rw [hw] at hwalk; simp at hwalk
            | some rest2 =>
              refine ih rest' (k + 1) (k :: es) ns rest2 hw ?_ hns ?_ hnsnd ?_
                (fun i hi => Nat.lt_succ_of_lt (hnslt i hi))
              · intro i hi
                rcases List.mem_cons.mp hi with rfl | hi
                · exact ⟨hklt, hbond⟩
                · exact hes i hi
              · refine List.nodup_cons.mpr ⟨?_, hesnd⟩
                intro hmem
                exact absurd (heslt k hmem) (lt_irrefl k)
              · intro i hi
                rcases List.mem_cons.mp hi with rfl | hi
                · omega
                · exact Nat.lt_succ_of_lt (heslt i hi)
          · cases hw : walk fuel rest' (k + 1) (k :: es) ns with
            | none => rw [hw] at hwalk; simp at hwalk
            | some rest2 =>
              rw [hw] at hwalk
              simp only at hwalk
              refine ih rest2 (k + 1) es (k :: ns) rest hwalk hes ?_ hesnd ?_
                (fun i hi => Nat.lt_succ_of_lt (heslt i hi)) ?_
              · intro i hi
                rcases List.mem_cons.mp hi with rfl | hi
                · exact ⟨hklt, hbond⟩
                · exact hns i hi
              · refine List.nodup_cons.mpr ⟨?_, hnsnd⟩
                intro hmem
                exact absurd (hnslt k hmem) (lt_irrefl k)
              · intro i hi
                rcases List.mem_cons.mp hi with rfl | hi
                · omega
                · exact Nat.lt_succ_of_lt (hnslt i hi)
        · rw [if_neg hklt] at hwalk
          simp at hwalk
      · rw [if_neg hc] at hwalk
        by_cases hcert : checkCert es ns ((c - 1) / 2) = true
        · exact checkCert_sound hX hpmem hpinj h8 hXim hcc hsort hes hns hesnd hnsnd hcert
        · rw [if_neg hcert] at hwalk
          simp at hwalk

open scoped Classical in
/-- Every eight-particle configuration admits a degree-sorted enumeration. -/
lemma exists_sorted_enum {X : Finset E3} (h8 : X.card = 8) :
    ∃ p : Fin 8 → E3, Function.Injective p ∧ Finset.image p Finset.univ = X ∧
      ∀ i j : Fin 8, i ≤ j → (neighbors X (p j)).card ≤ (neighbors X (p i)).card := by
  classical
  set le : E3 → E3 → Bool :=
    fun x y => decide ((neighbors X y).card ≤ (neighbors X x).card) with hle
  set l := X.toList.mergeSort le with hl
  have hperm : l.Perm X.toList := List.mergeSort_perm _ _
  have hlen : l.length = 8 := by rw [hperm.length_eq, Finset.length_toList, h8]
  have hnd : l.Nodup := hperm.nodup_iff.mpr X.nodup_toList
  have hpw : l.Pairwise (fun x y => le x y = true) := by
    apply List.pairwise_mergeSort
    · intro a b c hab hbc
      simp only [hle, decide_eq_true_eq] at hab hbc ⊢
      omega
    · intro a b
      simp only [hle, Bool.or_eq_true, decide_eq_true_eq]
      omega
  have hinj : Function.Injective (fun i : Fin 8 => l.get (i.cast hlen.symm)) := by
    intro i j hij
    have h := List.nodup_iff_injective_get.mp hnd hij
    have := congrArg Fin.val h
    simp only [Fin.val_cast] at this
    exact Fin.ext this
  refine ⟨fun i => l.get (i.cast hlen.symm), hinj, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      have := List.get_mem l (i.cast hlen.symm)
      rw [hperm.mem_iff, Finset.mem_toList] at this
      exact this
    · rw [h8, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_refl _
    · have h := List.pairwise_iff_get.mp hpw (i.cast hlen.symm) (j.cast hlen.symm)
        (by simpa using hlt)
      simpa [hle] using h
  
open scoped Classical in
/-- **The finite fact, parametrized by a verified kill tree**: any serialized tree
accepted by `walk` bounds every hard-core eight-particle configuration at 36 ordered
contacts. -/
theorem eight_particle_bound_of_tree {fuel : ℕ} {data : List ℕ}
    (htree : walk fuel data 0 [] [] = some [])
    {X : Finset E3} (hX : HardCore X) (h8 : X.card = 8) : contactCount X ≤ 36 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hm⟩ := contactCount_even X
  have hcc : 38 ≤ contactCount X := by omega
  obtain ⟨p, hpinj, hXim, hsort⟩ := exists_sorted_enum h8
  have hpmem : ∀ i, p i ∈ X := by
    intro i
    rw [← hXim]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  exact walk_impossible hX hpmem hpinj h8 hXim hcc hsort
    fuel data 0 [] [] [] htree
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

/-- Fuel monotonicity: extra fuel never hurts a successful walk. -/
lemma walk_fuel_mono {f f' : ℕ} (hf : f ≤ f') :
    ∀ {d : List ℕ} {k : ℕ} {es ns r : List ℕ},
    walk f d k es ns = some r → walk f' d k es ns = some r := by
  induction f' generalizing f with
  | zero =>
    intro d k es ns r h
    interval_cases f
    simp [walk] at h
  | succ f' ih =>
    intro d k es ns r h
    match f, h with
    | 0, h => simp [walk] at h
    | f + 1, h =>
      have hff : f ≤ f' := by omega
      match d with
      | [] => simp [walk] at h
      | c :: rest =>
        rw [show walk (f + 1) (c :: rest) k es ns
            = (if c == 0 then
                if k < 28 then
                  match walk f rest (k + 1) (k :: es) ns with
                  | none => none
                  | some rest2 => walk f rest2 (k + 1) es (k :: ns)
                else none
              else if checkCert es ns ((c - 1) / 2) then some rest else none) from rfl] at h
        rw [show walk (f' + 1) (c :: rest) k es ns
            = (if c == 0 then
                if k < 28 then
                  match walk f' rest (k + 1) (k :: es) ns with
                  | none => none
                  | some rest2 => walk f' rest2 (k + 1) es (k :: ns)
                else none
              else if checkCert es ns ((c - 1) / 2) then some rest else none) from rfl]
        by_cases hc : c == 0
        · rw [if_pos hc] at h ⊢
          by_cases hk : k < 28
          · rw [if_pos hk] at h ⊢
            cases hw : walk f rest (k + 1) (k :: es) ns with
            | none => rw [hw] at h; simp at h
            | some rest2 =>
              rw [hw] at h
              simp only at h
              rw [ih hff hw]
              simpa using ih hff h
          · rw [if_neg hk] at h
            exact absurd h (by simp)
        · rw [if_neg hc] at h ⊢
          exact h

/-- Symbolic branch composition for chunked kernel checks. -/
lemma walk_branch {fuel : ℕ} {dL dR : List ℕ} {k : ℕ} {es ns : List ℕ}
    (hk : k < 28)
    (hL : walk fuel dL (k + 1) (k :: es) ns = some [])
    (hR : walk fuel dR (k + 1) es (k :: ns) = some []) :
    walk (fuel + 1) ((0 : ℕ) :: (dL ++ dR)) k es ns = some [] := by
  have hcomp := walk_append (l2 := dR) hL
  rw [List.nil_append] at hcomp
  rw [show walk (fuel + 1) ((0 : ℕ) :: (dL ++ dR)) k es ns
      = (if (0 : ℕ) == 0 then
          if k < 28 then
            match walk fuel (dL ++ dR) (k + 1) (k :: es) ns with
            | none => none
            | some rest2 => walk fuel rest2 (k + 1) es (k :: ns)
          else none
        else if checkCert es ns (((0 : ℕ) - 1) / 2) then some (dL ++ dR)
        else none) from rfl]
  rw [if_pos (by norm_num), if_pos hk, hcomp]
  simpa using hR

end Emin8T

end Kissing3D
