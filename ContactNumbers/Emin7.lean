import ContactNumbers.Emin7Cert
import ContactNumbers.GroundStates3

set_option linter.style.header false
set_option maxHeartbeats 4000000

/-!
# The finite graph fact behind `E_min(7) = −15`

A hard-core 7-particle configuration with 16 bonds is impossible. The contact graph is
`K7` minus five (or fewer) non-edges, and for **every** choice of five removed edges —
`C(21,5) = 20349` cases — one of four local geometric facts is violated:

* a `K5` (five points pairwise at distance one — `pairwise_unit_card_le_four`),
* a ring vertex of degree three (`common_degree_impossible`),
* a ring four-cycle (`common_square_impossible`) or five-cycle
  (`common_pentagon_impossible`),
* three particles with three common neighbours (`common_neighbors_triple_le_two`).

The case analysis is delegated to the kernel: `emin7Certs` (machine-generated) stores one
packed witness per case, aligned with `(List.range 21).sublistsLen 5`, and `killcheck`
verifies a witness against its case. `all_killed` is the `decide`-checked totality; the
`sound` lemmas interpret a verified witness geometrically.
-/

namespace Kissing3D

namespace Emin7

/-- Lexicographic index of the unordered pair `{i, j}` among the 21 edges of `K7`:
`(0,1) ↦ 0, (0,2) ↦ 1, …, (5,6) ↦ 20`. -/
def pairIdx (i j : Nat) : Nat :=
  let a := min i j
  let b := max i j
  a * 6 - a * (a - 1) / 2 + b - a - 1

/-- Adjacency in `K7` minus the `removed` edge list: distinct vertices below seven whose
pair index was not removed. -/
def adjB (removed : List Nat) (i j : Nat) : Bool :=
  decide (i < 7) && decide (j < 7) && (i != j) && !(removed.contains (pairIdx i j))

/-- Base-8 payload field `k` of a packed certificate (field `0` is the digit after the
kind digit). -/
def fld (cert k : Nat) : Nat := cert / 8 ^ (k + 1) % 8

/-- Witness check, kind 0: five pairwise-adjacent vertices. -/
def checkK5 (rm : List Nat) (c : Nat) : Bool :=
  let a := fld c 0; let b := fld c 1; let d := fld c 2; let e := fld c 3; let f := fld c 4
  adjB rm a b && adjB rm a d && adjB rm a e && adjB rm a f &&
  adjB rm b d && adjB rm b e && adjB rm b f &&
  adjB rm d e && adjB rm d f && adjB rm e f

/-- Witness check, kind 1: an edge `uv`, a common neighbour `c` bonded to three further
distinct common neighbours `x, y, z`. -/
def checkRingDeg (rm : List Nat) (cert : Nat) : Bool :=
  let u := fld cert 0; let v := fld cert 1; let c := fld cert 2
  let x := fld cert 3; let y := fld cert 4; let z := fld cert 5
  adjB rm u v &&
  adjB rm u c && adjB rm v c && adjB rm u x && adjB rm v x &&
  adjB rm u y && adjB rm v y && adjB rm u z && adjB rm v z &&
  adjB rm c x && adjB rm c y && adjB rm c z &&
  (x != y) && (x != z) && (y != z)

/-- Witness check, kind 2: an edge `uv` with three pairwise-bonded common neighbours. -/
def checkRingC3 (rm : List Nat) (cert : Nat) : Bool :=
  let u := fld cert 0; let v := fld cert 1
  let x := fld cert 2; let y := fld cert 3; let z := fld cert 4
  adjB rm u v &&
  adjB rm u x && adjB rm v x && adjB rm u y && adjB rm v y &&
  adjB rm u z && adjB rm v z &&
  adjB rm x y && adjB rm x z && adjB rm y z

/-- Witness check, kind 3: an edge `uv` with a bond four-cycle `w–x–y–z` among its
common neighbours (`w ≠ y`, `x ≠ z`). -/
def checkRingC4 (rm : List Nat) (cert : Nat) : Bool :=
  let u := fld cert 0; let v := fld cert 1
  let w := fld cert 2; let x := fld cert 3; let y := fld cert 4; let z := fld cert 5
  adjB rm u v &&
  adjB rm u w && adjB rm v w && adjB rm u x && adjB rm v x &&
  adjB rm u y && adjB rm v y && adjB rm u z && adjB rm v z &&
  adjB rm w x && adjB rm x y && adjB rm y z && adjB rm z w &&
  (w != y) && (x != z)

/-- Witness check, kind 4: an edge `uv` with a bond five-cycle `z1–…–z5` among its
common neighbours (`z1 ≠ z3`, `z1 ≠ z4`). -/
def checkRingC5 (rm : List Nat) (cert : Nat) : Bool :=
  let u := fld cert 0; let v := fld cert 1
  let z1 := fld cert 2; let z2 := fld cert 3; let z3 := fld cert 4
  let z4 := fld cert 5; let z5 := fld cert 6
  adjB rm u v &&
  adjB rm u z1 && adjB rm v z1 && adjB rm u z2 && adjB rm v z2 &&
  adjB rm u z3 && adjB rm v z3 && adjB rm u z4 && adjB rm v z4 &&
  adjB rm u z5 && adjB rm v z5 &&
  adjB rm z1 z2 && adjB rm z2 z3 && adjB rm z3 z4 && adjB rm z4 z5 && adjB rm z5 z1 &&
  (z1 != z3) && (z1 != z4)

/-- Witness check, kind 5: three distinct vertices with three distinct common
neighbours. -/
def checkTriple (rm : List Nat) (cert : Nat) : Bool :=
  let a := fld cert 0; let b := fld cert 1; let c := fld cert 2
  let w1 := fld cert 3; let w2 := fld cert 4; let w3 := fld cert 5
  (a != b) && (a != c) && (b != c) &&
  (w1 != w2) && (w1 != w3) && (w2 != w3) &&
  adjB rm a w1 && adjB rm b w1 && adjB rm c w1 &&
  adjB rm a w2 && adjB rm b w2 && adjB rm c w2 &&
  adjB rm a w3 && adjB rm b w3 && adjB rm c w3

/-- Full witness check: dispatch on the kind digit. -/
def killcheck (rm : List Nat) (cert : Nat) : Bool :=
  let k := cert % 8
  if k == 0 then checkK5 rm cert
  else if k == 1 then checkRingDeg rm cert
  else if k == 2 then checkRingC3 rm cert
  else if k == 3 then checkRingC4 rm cert
  else if k == 4 then checkRingC5 rm cert
  else if k == 5 then checkTriple rm cert
  else false

/-! ### The kernel case check

`killAll` folds `killcheck` over a case list and a parallel certificate list, demanding
that both are consumed exactly. Totality over all 20349 cases is checked by the kernel in
seven chunks (the monolithic fold exceeds the kernel's recursion depth), then reassembled
with `killAll_append`. -/

/-- Paired fold of `killcheck`; `false` on length mismatch. -/
def killAll : List (List Nat) → List Nat → Bool
  | [], [] => true
  | c :: cs, w :: ws => killcheck c w && killAll cs ws
  | _, _ => false

lemma killAll_append {cs₁ cs₂ : List (List Nat)} {ws₁ ws₂ : List Nat}
    (h1 : killAll cs₁ ws₁ = true) (h2 : killAll cs₂ ws₂ = true) :
    killAll (cs₁ ++ cs₂) (ws₁ ++ ws₂) = true := by
  induction cs₁ generalizing ws₁ with
  | nil =>
    cases ws₁ with
    | nil => simpa using h2
    | cons w ws => simp [killAll] at h1
  | cons c cs ih =>
    cases ws₁ with
    | nil => simp [killAll] at h1
    | cons w ws =>
      simp only [killAll, List.cons_append, Bool.and_eq_true] at h1 ⊢
      exact ⟨h1.1, ih h1.2⟩

lemma killAll_forall {cs : List (List Nat)} {ws : List Nat}
    (h : killAll cs ws = true) : ∀ l ∈ cs, ∃ w, killcheck l w = true := by
  induction cs generalizing ws with
  | nil => intro l hl; cases hl
  | cons c cs ih =>
    cases ws with
    | nil => simp [killAll] at h
    | cons w ws' =>
      simp only [killAll, Bool.and_eq_true] at h
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact ⟨w, h.1⟩
      · exact ih h.2 l hl'

/-- The 20349 five-edge complements, in `sublistsLen` order. -/
def combos : List (List Nat) := (List.range 21).sublistsLen 5

private lemma chunk0 : killAll (combos.take 3000) (emin7Certs.take 3000) = true := by
  decide +kernel

private lemma chunk1 :
    killAll ((combos.drop 3000).take 3000) ((emin7Certs.drop 3000).take 3000) = true := by
  decide +kernel

private lemma chunk2 :
    killAll ((combos.drop 6000).take 3000) ((emin7Certs.drop 6000).take 3000) = true := by
  decide +kernel

private lemma chunk3 :
    killAll ((combos.drop 9000).take 3000) ((emin7Certs.drop 9000).take 3000) = true := by
  decide +kernel

private lemma chunk4 :
    killAll ((combos.drop 12000).take 3000) ((emin7Certs.drop 12000).take 3000) = true := by
  decide +kernel

private lemma chunk5 :
    killAll ((combos.drop 15000).take 3000) ((emin7Certs.drop 15000).take 3000) = true := by
  decide +kernel

private lemma chunk6 : killAll (combos.drop 18000) (emin7Certs.drop 18000) = true := by
  decide +kernel

/-- Reassemble a suffix fact from a chunk and the next suffix. -/
private lemma killAll_drop_step {n m : Nat}
    (h1 : killAll ((combos.drop n).take m) ((emin7Certs.drop n).take m) = true)
    (h2 : killAll (combos.drop (n + m)) (emin7Certs.drop (n + m)) = true) :
    killAll (combos.drop n) (emin7Certs.drop n) = true := by
  have e1 : (combos.drop n).drop m = combos.drop (n + m) := by
    rw [List.drop_drop, Nat.add_comm]
  have e2 : (emin7Certs.drop n).drop m = emin7Certs.drop (n + m) := by
    rw [List.drop_drop, Nat.add_comm]
  rw [← List.take_append_drop m (combos.drop n),
    ← List.take_append_drop m (emin7Certs.drop n)]
  exact killAll_append h1 (by rw [e1, e2]; exact h2)

/-- **Every five-edge complement of `K7` carries a verified kill certificate.** -/
theorem all_killed : killAll combos emin7Certs = true := by
  have h18 := chunk6
  have h15 := killAll_drop_step (n := 15000) (m := 3000) chunk5 (by norm_num at h18 ⊢; exact h18)
  have h12 := killAll_drop_step (n := 12000) (m := 3000) chunk4 (by norm_num at h15 ⊢; exact h15)
  have h9 := killAll_drop_step (n := 9000) (m := 3000) chunk3 (by norm_num at h12 ⊢; exact h12)
  have h6 := killAll_drop_step (n := 6000) (m := 3000) chunk2 (by norm_num at h9 ⊢; exact h9)
  have h3 := killAll_drop_step (n := 3000) (m := 3000) chunk1 (by norm_num at h6 ⊢; exact h6)
  have h0 := killAll_drop_step (n := 0) (m := 3000)
    (by simpa using chunk0) (by norm_num at h3 ⊢; exact h3)
  simpa using h0

/-! ### Soundness of the witness check -/

lemma adjB_true {rm : List Nat} {i j : Nat} (h : adjB rm i j = true) :
    i < 7 ∧ j < 7 ∧ i ≠ j ∧ rm.contains (pairIdx i j) = false := by
  simp only [adjB, Bool.and_eq_true, and_assoc, decide_eq_true_eq, bne_iff_ne,
    Bool.not_eq_true'] at h
  exact h

lemma pairIdx_comm (i j : Nat) : pairIdx i j = pairIdx j i := by
  simp only [pairIdx]
  rw [Nat.min_comm j i, Nat.max_comm j i]

lemma pairIdx_lt_of : ∀ i j : Fin 7, i < j → pairIdx i.1 j.1 < 21 := by decide

/-- Interpret a raw certificate vertex as a particle. -/
private def ppf (p : Fin 7 → E3) (n : Nat) : E3 := p ⟨n % 7, Nat.mod_lt _ (by norm_num)⟩

/-- Five points of `ℝ³` pairwise at distance one are impossible. -/
lemma five_points_impossible {q0 q1 q2 q3 q4 : E3}
    (h01 : dist q0 q1 = 1) (h02 : dist q0 q2 = 1) (h03 : dist q0 q3 = 1)
    (h04 : dist q0 q4 = 1) (h12 : dist q1 q2 = 1) (h13 : dist q1 q3 = 1)
    (h14 : dist q1 q4 = 1) (h23 : dist q2 q3 = 1) (h24 : dist q2 q4 = 1)
    (h34 : dist q3 q4 = 1) : False := by
  classical
  have hne : ∀ {a b : E3}, dist a b = 1 → a ≠ b := by
    intro a b h heq
    rw [heq, dist_self] at h
    norm_num at h
  have hS : ({q0, q1, q2, q3, q4} : Finset E3).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hne h01, hne h02, hne h03, hne h04]),
      Finset.card_insert_of_notMem (by simp [hne h12, hne h13, hne h14]),
      Finset.card_insert_of_notMem (by simp [hne h23, hne h24]),
      Finset.card_insert_of_notMem (by simp [hne h34]), Finset.card_singleton]
  have hpw : ∀ u ∈ ({q0, q1, q2, q3, q4} : Finset E3),
      ∀ v ∈ ({q0, q1, q2, q3, q4} : Finset E3), u ≠ v → dist u v = 1 := by
    intro u hu v hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl huv
        | assumption
        | (rw [dist_comm]; assumption)
  have hle := pairwise_unit_card_le_four hpw
  omega

open scoped Classical in
/-- **Soundness**: a hard-core realization compatible with a removed-edge list cannot
carry a verified kill certificate. -/
theorem killcheck_sound {X : Finset E3} (hX : HardCore X) {p : Fin 7 → E3}
    (hpmem : ∀ i, p i ∈ X) (hpinj : Function.Injective p)
    {rm : List Nat}
    (hedge : ∀ i j : Fin 7, i ≠ j → rm.contains (pairIdx i.1 j.1) = false →
      dist (p i) (p j) = 1)
    {cert : Nat} (hkill : killcheck rm cert = true) : False := by
  have hdist : ∀ {i j : Nat}, adjB rm i j = true → dist (ppf p i) (ppf p j) = 1 := by
    intro i j h
    obtain ⟨hi, hj, hne, hcon⟩ := adjB_true h
    have hpi : ppf p i = p ⟨i, hi⟩ := by
      simp only [ppf]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt hi)
    have hpj : ppf p j = p ⟨j, hj⟩ := by
      simp only [ppf]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt hj)
    rw [hpi, hpj]
    exact hedge ⟨i, hi⟩ ⟨j, hj⟩ (fun hh => hne (congrArg Fin.val hh)) hcon
  have hppne : ∀ {i j : Nat}, i < 7 → j < 7 → i ≠ j → ppf p i ≠ ppf p j := by
    intro i j hi hj hne heq
    apply hne
    have hv := hpinj heq
    simp only [Fin.mk.injEq] at hv
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
  have hmemN : ∀ {u t : Nat}, adjB rm u t = true → ppf p t ∈ neighbors X (ppf p u) := by
    intro u t h
    exact Finset.mem_filter.mpr ⟨hpmem _, hdist h⟩
  have hcomm2 : ∀ {u v t : Nat}, adjB rm u t = true → adjB rm v t = true →
      ppf p t ∈ neighbors X (ppf p u) ∩ neighbors X (ppf p v) := by
    intro u v t h1 h2
    exact Finset.mem_inter.mpr ⟨hmemN h1, hmemN h2⟩
  have hb : cert % 8 = 0 ∨ cert % 8 = 1 ∨ cert % 8 = 2 ∨ cert % 8 = 3 ∨ cert % 8 = 4 ∨
      cert % 8 = 5 ∨ 6 ≤ cert % 8 := by omega
  rcases hb with hk | hk | hk | hk | hk | hk | hk
  · -- K5
    simp only [killcheck, hk] at hkill
    norm_num at hkill
    simp only [checkK5, Bool.and_eq_true, and_assoc] at hkill
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hkill
    exact five_points_impossible (hdist h1) (hdist h2) (hdist h3) (hdist h4) (hdist h5)
      (hdist h6) (hdist h7) (hdist h8) (hdist h9) (hdist h10)
  · -- ring degree three
    simp only [killcheck, hk] at hkill
    norm_num at hkill
    simp only [checkRingDeg, Bool.and_eq_true, and_assoc] at hkill
    obtain ⟨huv, huc, hvc, hux, hvx, huy, hvy, huz, hvz, hcx, hcy, hcz, hxy, hxz, hyz⟩ := hkill
    obtain ⟨_, hx7, _, _⟩ := adjB_true hux
    obtain ⟨_, hy7, _, _⟩ := adjB_true huy
    obtain ⟨_, hz7, _, _⟩ := adjB_true huz
    exact common_degree_impossible hX (hdist huv) (hcomm2 huc hvc) (hcomm2 hux hvx)
      (hcomm2 huy hvy) (hcomm2 huz hvz)
      (hppne hx7 hy7 (by simpa using hxy)) (hppne hx7 hz7 (by simpa using hxz))
      (hppne hy7 hz7 (by simpa using hyz))
      (hdist hcx) (hdist hcy) (hdist hcz)
  · -- ring triangle
    simp only [killcheck, hk] at hkill
    norm_num at hkill
    simp only [checkRingC3, Bool.and_eq_true, and_assoc] at hkill
    obtain ⟨huv, hux, hvx, huy, hvy, huz, hvz, hxy, hxz, hyz⟩ := hkill
    exact common_triangle_impossible (hdist huv) (hcomm2 hux hvx) (hcomm2 huy hvy)
      (hcomm2 huz hvz) (hdist hxy) (hdist hxz) (hdist hyz)
  · -- ring four-cycle
    simp only [killcheck, hk] at hkill
    norm_num at hkill
    simp only [checkRingC4, Bool.and_eq_true, and_assoc] at hkill
    obtain ⟨huv, huw, hvw, hux, hvx, huy, hvy, huz, hvz, hwx, hxy, hyz, hzw, hwy, hxz⟩ := hkill
    obtain ⟨_, hw7, _, _⟩ := adjB_true huw
    obtain ⟨_, hx7, _, _⟩ := adjB_true hux
    obtain ⟨_, hy7, _, _⟩ := adjB_true huy
    obtain ⟨_, hz7, _, _⟩ := adjB_true huz
    refine common_square_impossible hX (hdist huv) (hcomm2 huw hvw) (hcomm2 huy hvy)
      (hcomm2 hux hvx) (hcomm2 huz hvz)
      (hppne hw7 hy7 (by simpa using hwy)) (hppne hx7 hz7 (by simpa using hxz))
      (hdist hwx) ?_ ?_ (hdist hyz)
    · rw [dist_comm]; exact hdist hzw
    · rw [dist_comm]; exact hdist hxy
  · -- ring five-cycle
    simp only [killcheck, hk] at hkill
    norm_num at hkill
    simp only [checkRingC5, Bool.and_eq_true, and_assoc] at hkill
    obtain ⟨huv, hu1, hv1, hu2, hv2, hu3, hv3, hu4, hv4, hu5, hv5,
      h12, h23, h34, h45, h51, h13, h14⟩ := hkill
    obtain ⟨_, h17, _, _⟩ := adjB_true hu1
    obtain ⟨_, h37, _, _⟩ := adjB_true hu3
    obtain ⟨_, h47, _, _⟩ := adjB_true hu4
    exact common_pentagon_impossible hX (hdist huv) (hcomm2 hu1 hv1) (hcomm2 hu2 hv2)
      (hcomm2 hu3 hv3) (hcomm2 hu4 hv4) (hcomm2 hu5 hv5)
      (hppne h17 h37 (by simpa using h13)) (hppne h17 h47 (by simpa using h14))
      (hdist h12) (hdist h23) (hdist h34) (hdist h45) (hdist h51)
  · -- three particles with three common neighbours
    simp only [killcheck, hk] at hkill
    norm_num at hkill
    simp only [checkTriple, Bool.and_eq_true, and_assoc] at hkill
    obtain ⟨hab, hac, hbc, h12, h13, h23, haw1, hbw1, hcw1, haw2, hbw2, hcw2,
      haw3, hbw3, hcw3⟩ := hkill
    obtain ⟨ha7, hw17, _, _⟩ := adjB_true haw1
    obtain ⟨hb7, _, _, _⟩ := adjB_true hbw1
    obtain ⟨hc7, _, _, _⟩ := adjB_true hcw1
    obtain ⟨_, hw27, _, _⟩ := adjB_true haw2
    obtain ⟨_, hw37, _, _⟩ := adjB_true haw3
    have hsub : ({ppf p (fld cert 3), ppf p (fld cert 4), ppf p (fld cert 5)} : Finset E3)
        ⊆ neighbors X (ppf p (fld cert 0)) ∩
          (neighbors X (ppf p (fld cert 1)) ∩ neighbors X (ppf p (fld cert 2))) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hmemN haw1, Finset.mem_inter.mpr ⟨hmemN hbw1, hmemN hcw1⟩⟩
      · exact Finset.mem_inter.mpr ⟨hmemN haw2, Finset.mem_inter.mpr ⟨hmemN hbw2, hmemN hcw2⟩⟩
      · exact Finset.mem_inter.mpr ⟨hmemN haw3, Finset.mem_inter.mpr ⟨hmemN hbw3, hmemN hcw3⟩⟩
    have hcard3 : ({ppf p (fld cert 3), ppf p (fld cert 4), ppf p (fld cert 5)} :
        Finset E3).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp [hppne hw17 hw27 (by simpa using h12), hppne hw17 hw37 (by simpa using h13)]),
        Finset.card_insert_of_notMem (by
          simp [hppne hw27 hw37 (by simpa using h23)]), Finset.card_singleton]
    have hle2 := common_neighbors_triple_le_two X
      (hppne ha7 hb7 (by simpa using hab)) (hppne ha7 hc7 (by simpa using hac))
      (hppne hb7 hc7 (by simpa using hbc))
    have hle := Finset.card_le_card hsub
    omega
  · -- impossible kind
    have h0 : cert % 8 ≠ 0 := by omega
    have h1 : cert % 8 ≠ 1 := by omega
    have h2 : cert % 8 ≠ 2 := by omega
    have h3 : cert % 8 ≠ 3 := by omega
    have h4 : cert % 8 ≠ 4 := by omega
    have h5 : cert % 8 ≠ 5 := by omega
    simp [killcheck, beq_iff_eq, h0, h1, h2, h3, h4, h5] at hkill

end Emin7

open Emin7 in
open scoped Classical in
/-- **A hard-core seven-particle configuration carries at most 30 ordered contacts**
(15 bonds): its contact graph misses at least five of the 21 pairs, and every five-edge
complement of `K7` is killed by a verified certificate. -/
theorem seven_particle_bound {X : Finset E3} (hX : HardCore X) (h7 : X.card = 7) :
    contactCount X ≤ 30 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hm⟩ := contactCount_even X
  have h32 : 32 ≤ contactCount X := by omega
  -- enumerate the particles
  set e := X.equivFinOfCardEq h7 with he
  set p : Fin 7 → E3 := fun i => ((e.symm i : X) : E3) with hp
  have hpmem : ∀ i, p i ∈ X := fun i => (e.symm i).2
  have hpinj : Function.Injective p := by
    intro i j hij
    have h1 : e.symm i = e.symm j := Subtype.coe_injective hij
    simpa using congrArg e h1
  have hXim : Finset.image p Finset.univ = X := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact hpmem i
    · rw [h7, Finset.card_image_of_injective _ hpinj]
      simp
  -- ordered bonded index pairs
  set A : Finset (Fin 7 × Fin 7) :=
    Finset.univ.filter (fun q => dist (p q.1) (p q.2) = 1) with hA
  have hsum : ∑ z ∈ X, (neighbors X z).card = ∑ i : Fin 7, (neighbors X (p i)).card := by
    refine (Finset.sum_bij (fun i _ => p i) (fun i _ => hpmem i)
      (fun i _ j _ h => hpinj h) ?_ (fun i _ => rfl)).symm
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (by rw [hXim]; exact hz)
    exact ⟨i, Finset.mem_univ i, rfl⟩
  have hAcard : A.card = contactCount X := by
    rw [hA, Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun q _ => Finset.mem_univ _), contactCount, hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hinj2 : Set.InjOn (fun q : Fin 7 × Fin 7 => p q.2)
        ((Finset.univ.filter (fun q : Fin 7 × Fin 7 => dist (p q.1) (p q.2) = 1)).filter
          (fun q => q.1 = i)) := by
      intro q hq q' hq' hpq
      have h1 := (Finset.mem_filter.mp hq).2
      have h2 := (Finset.mem_filter.mp hq').2
      have h3 : q.2 = q'.2 := hpinj hpq
      exact Prod.ext (h1.trans h2.symm) h3
    have hfib : ((Finset.univ.filter
        (fun q : Fin 7 × Fin 7 => dist (p q.1) (p q.2) = 1)).filter
          (fun q => q.1 = i)).image (fun q => p q.2) = neighbors X (p i) := by
      ext w
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, neighbors]
      constructor
      · rintro ⟨q, ⟨hd, hq1⟩, rfl⟩
        exact ⟨hpmem _, by rw [← hq1]; exact hd⟩
      · rintro ⟨hwX, hwd⟩
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hXim ▸ hwX)
        exact ⟨(i, j), ⟨hwd, rfl⟩, rfl⟩
    rw [← hfib, Finset.card_image_of_injOn hinj2]
  -- pair the two orientations
  set U := A.filter (fun q => q.1 < q.2) with hU
  set V := A.filter (fun q => q.2 < q.1) with hV
  have hAne : ∀ q ∈ A, q.1 ≠ q.2 := by
    intro q hq
    have hd := (Finset.mem_filter.mp hq).2
    intro h
    rw [h, dist_self] at hd
    norm_num at hd
  have hsplit : A.card = U.card + V.card := by
    rw [hU, hV, ← Finset.card_filter_add_card_filter_not (s := A) (fun q => q.1 < q.2)]
    congr 1
    congr 1
    apply Finset.filter_congr
    intro q hq
    have hne := hAne q hq
    simp only [not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (fun hh => hne hh.symm), fun h => le_of_lt h⟩
  have hVU : V.card = U.card := by
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
  have hU16 : 16 ≤ U.card := by omega
  -- the non-bonded pairs
  set S0 := (Finset.univ : Finset (Fin 7 × Fin 7)).filter (fun q => q.1 < q.2) with hS0
  have hS0card : S0.card = 21 := by rw [hS0]; decide
  have hUeq : U = S0.filter (fun q => dist (p q.1) (p q.2) = 1) := by
    rw [hU, hA, hS0, Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr
    intro q _
    exact and_comm
  set NB := S0.filter (fun q => ¬ dist (p q.1) (p q.2) = 1) with hNB
  have hNB5 : NB.card ≤ 5 := by
    have hpm := Finset.card_filter_add_card_filter_not (s := S0)
      (fun q => dist (p q.1) (p q.2) = 1)
    rw [← hUeq, ← hNB] at hpm
    omega
  -- pass to edge indices
  set R0 := NB.image (fun q : Fin 7 × Fin 7 => pairIdx q.1.1 q.2.1) with hR0
  have hR0card : R0.card ≤ 5 := le_trans Finset.card_image_le hNB5
  have hR0sub : R0 ⊆ Finset.range 21 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hlt : q.1 < q.2 := (Finset.mem_filter.mp ((Finset.mem_filter.mp hq).1)).2
    exact Finset.mem_range.mpr (pairIdx_lt_of q.1 q.2 hlt)
  obtain ⟨R, hR0R, hRsub, hRcard⟩ := Finset.exists_subsuperset_card_eq hR0sub hR0card
    (by rw [Finset.card_range]; norm_num)
  set rm := R.sort (· ≤ ·) with hrm
  -- the realization is compatible with `rm`
  have hedge : ∀ i j : Fin 7, i ≠ j → rm.contains (pairIdx i.1 j.1) = false →
      dist (p i) (p j) = 1 := by
    intro i j hne hcon
    by_contra hd
    have hkey : ∀ a b : Fin 7, a < b → ¬ dist (p a) (p b) = 1 → pairIdx a.1 b.1 ∈ R := by
      intro a b hab hnd
      apply hR0R
      rw [hR0]
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, hnd⟩, rfl⟩
    have hmem : pairIdx i.1 j.1 ∈ R := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact hkey i j h hd
      · have hji := hkey j i h (fun hh => hd (by rw [dist_comm]; exact hh))
        rwa [pairIdx_comm] at hji
    have hin : pairIdx i.1 j.1 ∈ rm := (Finset.mem_sort _).mpr hmem
    simp at hcon
    exact hcon hin
  -- membership in the case list
  have hcombo : rm ∈ combos := by
    rw [combos, List.mem_sublistsLen]
    constructor
    · apply List.sublist_of_subperm_of_sortedLE
      · apply List.Nodup.subperm (Finset.sort_nodup _ _)
        intro x hx
        exact List.mem_range.mpr (Finset.mem_range.mp (hRsub ((Finset.mem_sort _).mp hx)))
      · exact (Finset.pairwise_sort _ _).sortedLE
      · exact (List.sortedLT_range 21).sortedLE
    · rw [hrm, Finset.length_sort, hRcard]
  obtain ⟨w, hw⟩ := killAll_forall all_killed rm hcombo
  exact killcheck_sound hX hpmem hpinj hedge hw

/-- **`E ≥ −15` for seven particles.** -/
theorem energy_ge_seven_particles {X : Finset E3} (hX : HardCore X) (h7 : X.card = 7) :
    -15 ≤ energy X := by
  have hb := seven_particle_bound hX h7
  rw [energy]
  have hc : (contactCount X : ℝ) ≤ 30 := by exact_mod_cast hb
  linarith

end Kissing3D
