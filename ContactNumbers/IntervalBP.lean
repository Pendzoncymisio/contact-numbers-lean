import ContactNumbers.Emin9Kills

set_option linter.style.header false
set_option maxHeartbeats 3200000

/-!
# Interval branch-and-prune certificates over ℚ

Machinery for kernel-checkable infeasibility of Gram-determinant systems on
rational boxes: polynomials as term lists (`ℚ` coefficient × exponent list),
corner shift (Taylor shift to the box corner), and an exact rational lower
bound. Everything is algebraic — soundness needs no analysis.
-/

namespace Kissing3D

namespace IBP

/-- Polynomial as a list of (coefficient, exponent list). -/
abbrev Poly := List (ℚ × List ℕ)

/-- Monomial evaluation over ℝ; a missing point coordinate acts as factor 1. -/
def evalMono : List ℝ → List ℕ → ℝ
  | _, [] => 1
  | [], _ :: _ => 1
  | x :: xs, e :: es => x ^ e * evalMono xs es

/-- Polynomial evaluation over ℝ. -/
def evalPoly (P : Poly) (s : List ℝ) : ℝ :=
  P.foldr (fun t a => (t.1 : ℝ) * evalMono s t.2 + a) 0

@[simp] lemma evalPoly_nil (s : List ℝ) : evalPoly [] s = 0 := rfl

@[simp] lemma evalPoly_cons (c : ℚ) (es : List ℕ) (P : Poly) (s : List ℝ) :
    evalPoly ((c, es) :: P) s = (c : ℝ) * evalMono s es + evalPoly P s := rfl

lemma evalPoly_append (P Q : Poly) (s : List ℝ) :
    evalPoly (P ++ Q) s = evalPoly P s + evalPoly Q s := by
  induction P with
  | nil => simp
  | cons t P ih =>
    obtain ⟨c, es⟩ := t
    simp [ih]
    ring

lemma evalPoly_flatMap {α : Type} (L : List α) (f : α → Poly) (s : List ℝ) :
    evalPoly (L.flatMap f) s = (L.map (fun a => evalPoly (f a) s)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp [List.flatMap_cons, evalPoly_append, ih]

/-- Expand one term `c · Π sᵢ^{eᵢ}` under `s = lows + t` (binomial expansion). -/
def expandTerm (c : ℚ) : List ℕ → List ℚ → Poly
  | [], _ => [(c, [])]
  | e :: es, [] => (expandTerm c es []).map (fun t => (t.1, e :: t.2))
  | e :: es, l :: lows =>
    (expandTerm c es lows).flatMap (fun t =>
      (List.range (e + 1)).map (fun k =>
        (t.1 * (e.choose k : ℚ) * l ^ (e - k), k :: t.2)))

/-- Shift a polynomial to the corner `lows`. -/
def shiftPoly (P : Poly) (lows : List ℚ) : Poly :=
  P.flatMap (fun t => expandTerm t.1 t.2 lows)

/-- Translate a real point by a rational corner (ragged tails untouched). -/
def addLo : List ℚ → List ℝ → List ℝ
  | [], t => t
  | _ :: _, [] => []
  | l :: lows, x :: t => ((l : ℝ) + x) :: addLo lows t

/-- ℚ-side monomial evaluation. -/
def evalMonoQ : List ℚ → List ℕ → ℚ
  | _, [] => 1
  | [], _ :: _ => 1
  | x :: xs, e :: es => x ^ e * evalMonoQ xs es

private lemma range_map_sum (n : ℕ) (g : ℕ → ℝ) :
    ((List.range n).map g).sum = ∑ k ∈ Finset.range n, g k := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append,
      Finset.sum_range_succ, ih]
    simp

private lemma binom_eval (x : ℝ) (l : ℚ) (e : ℕ) :
    ∑ k ∈ Finset.range (e + 1), (l : ℝ) ^ (e - k) * x ^ k * (e.choose k : ℝ)
      = ((l : ℝ) + x) ^ e := by
  rw [add_comm ((l : ℝ)) x, add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma expandTerm_eval (c : ℚ) (es : List ℕ) (lows : List ℚ) (t : List ℝ)
    (hlo : lows.length = es.length) (ht : t.length = es.length) :
    evalPoly (expandTerm c es lows) t = (c : ℝ) * evalMono (addLo lows t) es := by
  induction es generalizing lows t c with
  | nil =>
    have h1 : lows = [] := List.length_eq_zero_iff.mp hlo
    have h2 : t = [] := List.length_eq_zero_iff.mp ht
    subst h1; subst h2
    simp [expandTerm, evalPoly, evalMono, addLo]
  | cons e es ih =>
    cases lows with
    | nil => simp at hlo
    | cons l lows' =>
      cases t with
      | nil => simp at ht
      | cons x t' =>
        simp only [List.length_cons, Nat.succ_inj] at hlo ht
        simp only [expandTerm, addLo, evalMono]
        rw [evalPoly_flatMap]
        have hterm : ∀ p : ℚ × List ℕ,
            evalPoly ((List.range (e + 1)).map (fun k =>
              (p.1 * (e.choose k : ℚ) * l ^ (e - k), k :: p.2))) (x :: t')
            = (p.1 : ℝ) * evalMono t' p.2 * (((l : ℝ) + x) ^ e) := by
          intro p
          have hmap : evalPoly ((List.range (e + 1)).map (fun k =>
              (p.1 * (e.choose k : ℚ) * l ^ (e - k), k :: p.2))) (x :: t')
              = ((List.range (e + 1)).map (fun k =>
                  ((p.1 : ℝ) * (e.choose k : ℝ) * (l : ℝ) ^ (e - k)) *
                    (x ^ k * evalMono t' p.2))).sum := by
            induction (List.range (e + 1)) with
            | nil => simp
            | cons k ks ihk =>
              simp only [List.map_cons, evalPoly_cons, List.sum_cons, ihk,
                evalMono]
              push_cast
              ring_nf
          rw [hmap, range_map_sum]
          rw [show (∑ k ∈ Finset.range (e + 1),
              ((p.1 : ℝ) * (e.choose k : ℝ) * (l : ℝ) ^ (e - k)) *
                (x ^ k * evalMono t' p.2))
            = (p.1 : ℝ) * evalMono t' p.2 *
              (∑ k ∈ Finset.range (e + 1),
                (l : ℝ) ^ (e - k) * x ^ k * (e.choose k : ℝ)) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring]
          rw [binom_eval]
        calc ((expandTerm c es lows').map (fun p =>
                evalPoly ((List.range (e + 1)).map (fun k =>
                  (p.1 * (e.choose k : ℚ) * l ^ (e - k), k :: p.2))) (x :: t'))).sum
            = ((expandTerm c es lows').map (fun p =>
                ((p.1 : ℝ) * evalMono t' p.2) * (((l : ℝ) + x) ^ e))).sum := by
              congr 1
              apply List.map_congr_left
              intro p _
              rw [hterm p]
          _ = (((expandTerm c es lows').map (fun p =>
                (p.1 : ℝ) * evalMono t' p.2)).sum) * (((l : ℝ) + x) ^ e) := by
              rw [← List.sum_map_mul_right]
          _ = evalPoly (expandTerm c es lows') t' * (((l : ℝ) + x) ^ e) := by
              congr 1
              have hgen : ∀ L : Poly,
                  (L.map (fun p => (p.1 : ℝ) * evalMono t' p.2)).sum
                    = evalPoly L t' := by
                intro L
                induction L with
                | nil => simp
                | cons q qs ihq =>
                  obtain ⟨cc, ees⟩ := q
                  simp [ihq]
              exact hgen _
          _ = (c : ℝ) * (((l : ℝ) + x) ^ e * evalMono (addLo lows' t') es) := by
              rw [ih c lows' t' hlo ht]
              ring

/-- Shift correctness: evaluating the shifted polynomial at `t` is evaluating
the original at `lows + t`. -/
lemma evalPoly_shiftPoly (P : Poly) (lows : List ℚ) (t : List ℝ)
    (hlen : ∀ p ∈ P, (p.2 : List ℕ).length = lows.length)
    (ht : t.length = lows.length) :
    evalPoly (shiftPoly P lows) t = evalPoly P (addLo lows t) := by
  induction P with
  | nil => simp [shiftPoly]
  | cons p ps ih =>
    obtain ⟨c, es⟩ := p
    have hes : es.length = lows.length := hlen (c, es) (by simp)
    simp only [shiftPoly, List.flatMap_cons, evalPoly_append]
    rw [expandTerm_eval c es lows t hes.symm (by rw [ht, hes])]
    have := ih (fun q hq => hlen q (List.mem_cons_of_mem _ hq))
    simp only [shiftPoly] at this
    rw [this]
    rfl

/-- Rational lower bound of a shifted polynomial over `0 ≤ t ≤ w`
(componentwise): constant terms count fully; positive nonconstant terms are
dropped (≥ 0); negative nonconstant terms are taken at width powers. -/
def lowBound (Q : Poly) (w : List ℚ) : ℚ :=
  Q.foldr (fun p a =>
    if p.2.all (fun e => e == 0) then p.1 + a
    else if p.1 < 0 then p.1 * evalMonoQ w p.2 + a
    else a) 0

lemma evalMono_nonneg {t : List ℝ} (h : ∀ x ∈ t, 0 ≤ x) (es : List ℕ) :
    0 ≤ evalMono t es := by
  induction t generalizing es with
  | nil => cases es <;> simp [evalMono]
  | cons x xs ih =>
    cases es with
    | nil => simp [evalMono]
    | cons e es' =>
      simp only [evalMono]
      have hx : (0:ℝ) ≤ x := h x (by simp)
      exact mul_nonneg (pow_nonneg hx e) (ih (fun y hy => h y (by simp [hy])) es')

lemma evalMono_le {t : List ℝ} {w : List ℚ}
    (h0 : ∀ x ∈ t, 0 ≤ x)
    (hw : ∀ i, i < t.length → (t.getD i 0) ≤ (((w.getD i 0) : ℚ) : ℝ))
    (hlen : w.length = t.length) (es : List ℕ) (hes : es.length ≤ t.length) :
    evalMono t es ≤ ((evalMonoQ w es : ℚ) : ℝ) := by
  induction es generalizing t w with
  | nil => simp [evalMono, evalMonoQ]
  | cons e es' ih =>
    cases t with
    | nil => simp at hes
    | cons x xs =>
      cases w with
      | nil => simp at hlen
      | cons wv ws =>
        simp only [evalMono, evalMonoQ]
        push_cast
        have hx0 : (0:ℝ) ≤ x := h0 x (by simp)
        have hxw : x ≤ (wv : ℝ) := by
          have h := hw 0 (by simp)
          simpa [List.getD_cons_zero] using h
        have hxs0 : ∀ y ∈ xs, (0:ℝ) ≤ y := fun y hy => h0 y (by simp [hy])
        have hws : ∀ i, i < xs.length → (xs.getD i 0) ≤ (((ws.getD i 0) : ℚ) : ℝ) := by
          intro i hi
          have h := hw (i + 1) (by simpa using Nat.succ_lt_succ hi)
          simpa [List.getD_cons_succ] using h
        have hlen' : ws.length = xs.length := by simpa using hlen
        have hes' : es'.length ≤ xs.length := by simpa using hes
        have hwv : (0:ℝ) ≤ (wv : ℝ) := le_trans hx0 hxw
        have h1 : x ^ e ≤ (wv : ℝ) ^ e := by gcongr
        have h2 := ih hxs0 hws hlen' hes'
        have h3 : (0:ℝ) ≤ evalMono xs es' := evalMono_nonneg hxs0 es'
        have h4 : (0:ℝ) ≤ x ^ e := pow_nonneg hx0 e
        have h5 : (0:ℝ) ≤ ((evalMonoQ ws es' : ℚ) : ℝ) := le_trans h3 h2
        calc x ^ e * evalMono xs es'
            ≤ (wv : ℝ) ^ e * evalMono xs es' := by
              exact mul_le_mul_of_nonneg_right h1 h3
          _ ≤ (wv : ℝ) ^ e * ((evalMonoQ ws es' : ℚ) : ℝ) := by
              exact mul_le_mul_of_nonneg_left h2 (pow_nonneg hwv e)

lemma evalMono_all_zero (t : List ℝ) (es : List ℕ)
    (h : es.all (fun e => e == 0) = true) : evalMono t es = 1 := by
  induction t generalizing es with
  | nil => cases es <;> simp [evalMono]
  | cons x xs ih =>
    cases es with
    | nil => simp [evalMono]
    | cons e es' =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      simp [evalMono, h.1, ih es' h.2]

/-- **Bound soundness**: on `0 ≤ t ≤ w`, the polynomial is at least `lowBound`. -/
lemma lowBound_le (Q : Poly) (w : List ℚ) (t : List ℝ)
    (h0 : ∀ x ∈ t, 0 ≤ x)
    (hw : ∀ i, i < t.length → (t.getD i 0) ≤ (((w.getD i 0) : ℚ) : ℝ))
    (hlen : w.length = t.length)
    (hes : ∀ p ∈ Q, (p.2 : List ℕ).length ≤ t.length)
    (_hwnn : ∀ x ∈ w, (0:ℚ) ≤ x) :
    ((lowBound Q w : ℚ) : ℝ) ≤ evalPoly Q t := by
  induction Q with
  | nil => simp [lowBound]
  | cons p ps ih =>
    obtain ⟨c, es⟩ := p
    have htail := ih (fun q hq => hes q (List.mem_cons_of_mem _ hq))
    simp only [lowBound, List.foldr_cons, evalPoly_cons]
    by_cases hz : es.all (fun e => e == 0) = true
    · rw [if_pos hz]
      rw [evalMono_all_zero t es hz]
      push_cast
      simp only [lowBound] at htail
      linarith
    · rw [if_neg hz]
      by_cases hc : c < 0
      · rw [if_pos hc]
        have hb := evalMono_le h0 hw hlen es (hes (c, es) (by simp))
        have hcr : (c : ℝ) < 0 := by exact_mod_cast hc
        have h6 : (c : ℝ) * ((evalMonoQ w es : ℚ) : ℝ) ≤ (c : ℝ) * evalMono t es := by
          exact mul_le_mul_of_nonpos_left hb (le_of_lt hcr)
        push_cast
        simp only [lowBound] at htail

        linarith
      · rw [if_neg hc]
        push Not at hc
        have hcr : (0:ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
        have hm := evalMono_nonneg h0 es
        have : (0:ℝ) ≤ (c : ℝ) * evalMono t es := mul_nonneg hcr hm
        simp only [lowBound] at htail
        linarith

end IBP

end Kissing3D

namespace Kissing3D

namespace IBP

/-- Insert a term, merging with an existing equal-exponent term. -/
def insertTerm (t : ℚ × List ℕ) : Poly → Poly
  | [] => [t]
  | u :: rest =>
    if t.2 == u.2 then (t.1 + u.1, u.2) :: rest
    else u :: insertTerm t rest

/-- Combine like terms (quadratic time, canonical result values). -/
def combinePoly : Poly → Poly
  | [] => []
  | t :: rest => insertTerm t (combinePoly rest)

lemma evalPoly_insertTerm (t : ℚ × List ℕ) (P : Poly) (s : List ℝ) :
    evalPoly (insertTerm t P) s = (t.1 : ℝ) * evalMono s t.2 + evalPoly P s := by
  induction P with
  | nil =>
    obtain ⟨c, es⟩ := t
    simp [insertTerm]
  | cons u rest ih =>
    obtain ⟨c, es⟩ := t
    obtain ⟨c', es'⟩ := u
    simp only [insertTerm]
    by_cases h : es == es'
    · rw [if_pos h]
      have heq : es = es' := by simpa using h
      subst heq
      simp only [evalPoly_cons]
      push_cast
      ring
    · rw [if_neg h]
      simp only [evalPoly_cons, ih]

      ring

lemma evalPoly_combinePoly (P : Poly) (s : List ℝ) :
    evalPoly (combinePoly P) s = evalPoly P s := by
  induction P with
  | nil => simp [combinePoly]
  | cons t rest ih =>
    obtain ⟨c, es⟩ := t
    simp only [combinePoly, evalPoly_insertTerm, evalPoly_cons, ih]

/-- Combined-term lengths come from the original terms. -/
lemma insertTerm_length (t : ℚ × List ℕ) (P : Poly) :
    ∀ q ∈ insertTerm t P, (q.2 : List ℕ).length = t.2.length ∨
      ∃ p ∈ P, (q.2 : List ℕ).length = (p.2 : List ℕ).length := by
  induction P with
  | nil =>
    intro q hq
    simp [insertTerm] at hq
    left
    simp [hq]
  | cons u rest ih =>
    intro q hq
    simp only [insertTerm] at hq
    by_cases h : t.2 == u.2
    · rw [if_pos h] at hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · right
        exact ⟨u, by simp, rfl⟩
      · right
        exact ⟨q, List.mem_cons_of_mem _ hq', rfl⟩
    · rw [if_neg h] at hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · right; exact ⟨q, by simp, rfl⟩
      · rcases ih q hq' with h1 | ⟨p, hp, he⟩
        · left; exact h1
        · right; exact ⟨p, List.mem_cons_of_mem _ hp, he⟩

lemma combinePoly_length (P : Poly) :
    ∀ q ∈ combinePoly P, ∃ p ∈ P, (q.2 : List ℕ).length = (p.2 : List ℕ).length := by
  induction P with
  | nil => intro q hq; simp [combinePoly] at hq
  | cons t rest ih =>
    intro q hq
    simp only [combinePoly] at hq
    rcases insertTerm_length t (combinePoly rest) q hq with h1 | ⟨p, hp, he⟩
    · exact ⟨t, by simp, h1⟩
    · obtain ⟨p', hp', he'⟩ := ih p hp
      exact ⟨p', List.mem_cons_of_mem _ hp', he.trans he'⟩

/-! ### The branch-and-prune tree walker

Tree data (preorder, flat `List ℕ`):
* `0 :: k :: rest` — split variable `k` at the box midpoint;
* `1 :: kind :: idx :: rest` — kill leaf: `kind 0` = det `idx` provably
  positive on the box, `kind 1` = det `idx` negative, `kind 2` = minor `idx`
  negative (contradicting PSD).
-/

/-- Negate a polynomial. -/
def negPoly (P : Poly) : Poly := P.map (fun p => (-p.1, p.2))

lemma evalPoly_negPoly (P : Poly) (s : List ℝ) :
    evalPoly (negPoly P) s = -evalPoly P s := by
  induction P with
  | nil => simp [negPoly]
  | cons p ps ih =>
    obtain ⟨c, es⟩ := p
    simp [negPoly, ih] at *

    ring

/-- Walk the branch-and-prune tree, verifying every kill leaf by exact rational
arithmetic. Returns the unconsumed tail on success. -/
def ibpWalk (dets minors : List Poly) : ℕ → List ℕ → List ℚ → List ℚ →
    Option (List ℕ)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, 0 :: k :: rest, lows, w =>
    let w2 := w.set k (w.getD k 0 / 2)
    match ibpWalk dets minors fuel rest lows w2 with
    | none => none
    | some rest2 =>
      ibpWalk dets minors fuel rest2 (lows.set k (lows.getD k 0 + w.getD k 0 / 2)) w2
  | _fuel + 1, 1 :: kind :: idx :: rest, lows, w =>
    if kind == 0 then
      if 0 < lowBound (combinePoly (shiftPoly (dets.getD idx []) lows)) w then some rest else none
    else if kind == 1 then
      if 0 < lowBound (combinePoly (shiftPoly (negPoly (dets.getD idx [])) lows)) w then some rest
      else none
    else if kind == 2 then
      if 0 < lowBound (combinePoly (shiftPoly (negPoly (minors.getD idx [])) lows)) w then some rest
      else none
    else none
  | _ + 1, _ :: _, _, _ => none

end IBP

end Kissing3D

namespace Kissing3D

namespace IBP

/-- Exponent lengths are preserved by term expansion. -/
lemma expandTerm_length (c : ℚ) (es : List ℕ) (lows : List ℚ) :
    ∀ q ∈ expandTerm c es lows, (q.2 : List ℕ).length = es.length := by
  induction es generalizing lows c with
  | nil =>
    intro q hq
    simp [expandTerm] at hq
    simp [hq]
  | cons e es ih =>
    intro q hq
    cases lows with
    | nil =>
      simp only [expandTerm, List.mem_map] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      simp [ih c [] p hp]
    | cons l lows' =>
      simp only [expandTerm, List.mem_flatMap, List.mem_map] at hq
      obtain ⟨p, hp, k, _, rfl⟩ := hq
      simp [ih c lows' p hp]

lemma shiftPoly_length (P : Poly) (lows : List ℚ) :
    ∀ q ∈ shiftPoly P lows, ∃ p ∈ P, (q.2 : List ℕ).length = (p.2 : List ℕ).length := by
  intro q hq
  simp only [shiftPoly, List.mem_flatMap] at hq
  obtain ⟨p, hp, hq2⟩ := hq
  exact ⟨p, hp, expandTerm_length p.1 p.2 lows q hq2⟩

/-- Componentwise difference `s − lows` as a real list. -/
def subLo : List ℚ → List ℝ → List ℝ
  | [], s => s
  | _ :: _, [] => []
  | l :: lows, x :: s => (x - (l : ℝ)) :: subLo lows s

lemma addLo_subLo (lows : List ℚ) (s : List ℝ) (h : s.length = lows.length) :
    addLo lows (subLo lows s) = s := by
  induction lows generalizing s with
  | nil => cases s <;> simp [addLo, subLo]
  | cons l lows' ih =>
    cases s with
    | nil => simp at h
    | cons x s' =>
      simp only [List.length_cons, Nat.succ_inj] at h
      simp [addLo, subLo, ih s' h]

lemma subLo_length (lows : List ℚ) (s : List ℝ) (h : s.length = lows.length) :
    (subLo lows s).length = lows.length := by
  induction lows generalizing s with
  | nil => cases s <;> simp_all [subLo]
  | cons l lows' ih =>
    cases s with
    | nil => simp at h
    | cons x s' =>
      simp only [List.length_cons, Nat.succ_inj] at h
      simp [subLo, ih s' h]


private lemma getD_set_self' : ∀ (l : List ℚ) (i : ℕ) (a : ℚ), i < l.length →
    (l.set i a).getD i 0 = a
  | [], i, a, h => by simp at h
  | x :: xs, 0, a, _ => rfl
  | x :: xs, i + 1, a, h => by
      simpa using getD_set_self' xs i a (by simpa using h)

private lemma getD_set_ne' : ∀ (l : List ℚ) (i j : ℕ), i ≠ j → ∀ (a : ℚ),
    (l.set i a).getD j 0 = l.getD j 0
  | [], _, _, _, _ => by simp
  | x :: xs, 0, 0, h, a => absurd rfl h
  | x :: xs, 0, j + 1, _, a => by simp [List.getD]
  | x :: xs, i + 1, 0, _, a => by simp [List.getD]
  | x :: xs, i + 1, j + 1, h, a => by
      simpa using getD_set_ne' xs i j (fun hh => h (by omega)) a

private lemma getD_mem' : ∀ (l : List ℚ) (i : ℕ), i < l.length → l.getD i 0 ∈ l
  | [], i, h => by simp at h
  | x :: xs, 0, _ => by simp [List.getD]
  | x :: xs, i + 1, h => by
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (getD_mem' xs i (by simpa using h))

private lemma getD_default' : ∀ (l : List ℚ) (i : ℕ), l.length ≤ i →
    l.getD i 0 = 0
  | [], _, _ => by simp
  | x :: xs, 0, h => by simp at h
  | x :: xs, i + 1, h => by
      simpa using getD_default' xs i (by simpa using h)

private lemma subLo_getD : ∀ (lows : List ℚ) (s : List ℝ), s.length = lows.length →
    ∀ i, i < s.length →
    (subLo lows s).getD i 0 = s.getD i 0 - ((lows.getD i 0 : ℚ) : ℝ)
  | [], s, h, i, hi => by
      rw [h] at hi
      simp at hi
  | l :: lows', [], h, i, hi => by simp at hi
  | l :: lows', x :: s', h, 0, hi => by simp [subLo, List.getD]
  | l :: lows', x :: s', h, i + 1, hi => by
      simp only [subLo, List.getD_cons_succ]
      exact subLo_getD lows' s' (by simpa using h) i (by simpa using hi)

/-- **Walker soundness**: a successful walk over a box containing a point where
all `dets` vanish and all `minors` are nonnegative is impossible. -/
theorem ibpWalk_impossible (dets minors : List Poly) (s : List ℝ)
    (hdets : ∀ P ∈ dets, evalPoly P s = 0)
    (hminors : ∀ P ∈ minors, 0 ≤ evalPoly P s)
    (harity : ∀ P ∈ dets ++ minors, ∀ p ∈ P, (p.2 : List ℕ).length = s.length) :
    ∀ (fuel : ℕ) (data : List ℕ) (lows w : List ℚ) (rest : List ℕ),
    ibpWalk dets minors fuel data lows w = some rest →
    lows.length = s.length → w.length = s.length →
    (∀ i, i < s.length →
      ((lows.getD i 0 : ℚ) : ℝ) ≤ s.getD i 0 ∧
        s.getD i 0 ≤ (((lows.getD i 0 + w.getD i 0) : ℚ) : ℝ)) →
    (∀ x ∈ w, (0:ℚ) ≤ x) → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro data lows w rest hwalk
    simp [ibpWalk] at hwalk
  | succ fuel ih =>
    intro data lows w rest hwalk hlo hw hbox hwnn
    match data with
    | [] => simp [ibpWalk] at hwalk
    | 0 :: k :: rest' =>
      rw [show ibpWalk dets minors (fuel + 1) (0 :: k :: rest') lows w
          = (let w2 := w.set k (w.getD k 0 / 2)
             match ibpWalk dets minors fuel rest' lows w2 with
             | none => none
             | some rest2 =>
               ibpWalk dets minors fuel rest2
                 (lows.set k (lows.getD k 0 + w.getD k 0 / 2)) w2) from rfl] at hwalk
      simp only at hwalk
      set w2 := w.set k (w.getD k 0 / 2) with hw2
      cases hleft : ibpWalk dets minors fuel rest' lows w2 with
      | none => rw [hleft] at hwalk; simp at hwalk
      | some rest2 =>
        rw [hleft] at hwalk
        simp only at hwalk
        by_cases hside : s.getD k 0 ≤ (((lows.getD k 0 + w.getD k 0 / 2) : ℚ) : ℝ)
        · -- point is in the left half-box
          refine ih rest' lows w2 rest2 hleft hlo ?_ ?_ ?_
          · rw [hw2]
            simp [List.length_set, hw]
          · intro i hi
            obtain ⟨h1, h2⟩ := hbox i hi
            constructor
            · exact h1
            · by_cases hik : i = k
              · subst hik
                have : w2.getD i 0 = w.getD i 0 / 2 := by
                  rw [hw2]
                  exact getD_set_self' w i _ (by rw [hw]; exact hi)
                rw [this]
                exact hside
              · have : w2.getD i 0 = w.getD i 0 := by
                  rw [hw2]
                  exact getD_set_ne' w k i (fun h => hik h.symm) _
                rw [this]
                exact h2
          · intro x hx
            rw [hw2] at hx
            rcases List.mem_or_eq_of_mem_set hx with h | h
            · exact hwnn x h
            · rw [h]
              have : (0:ℚ) ≤ w.getD k 0 := by
                by_cases hk : k < w.length
                · exact hwnn _ (getD_mem' w k hk)
                · rw [getD_default' w k (by omega)]
              linarith
        · -- point is in the right half-box
          push Not at hside
          refine ih rest2 (lows.set k (lows.getD k 0 + w.getD k 0 / 2)) w2 rest hwalk
            ?_ ?_ ?_ ?_
          · simp [List.length_set, hlo]
          · rw [hw2]; simp [List.length_set, hw]
          · intro i hi
            obtain ⟨h1, h2⟩ := hbox i hi
            by_cases hik : i = k
            · subst hik
              have hlo' : (lows.set i (lows.getD i 0 + w.getD i 0 / 2)).getD i 0
                  = lows.getD i 0 + w.getD i 0 / 2 :=
                getD_set_self' lows i _ (by rw [hlo]; exact hi)
              have hw2' : w2.getD i 0 = w.getD i 0 / 2 := by
                rw [hw2]
                exact getD_set_self' w i _ (by rw [hw]; exact hi)
              rw [hlo', hw2']
              constructor
              · push_cast
                push_cast at hside
                linarith
              · push_cast
                push_cast at h2
                linarith
            · have hlo' : (lows.set k (lows.getD k 0 + w.getD k 0 / 2)).getD i 0
                  = lows.getD i 0 :=
                getD_set_ne' lows k i (fun h => hik h.symm) _
              have hw2' : w2.getD i 0 = w.getD i 0 := by
                rw [hw2]
                exact getD_set_ne' w k i (fun h => hik h.symm) _
              rw [hlo', hw2']
              exact ⟨h1, h2⟩
          · intro x hx
            rw [hw2] at hx
            rcases List.mem_or_eq_of_mem_set hx with h | h
            · exact hwnn x h
            · rw [h]
              have : (0:ℚ) ≤ w.getD k 0 := by
                by_cases hk : k < w.length
                · exact hwnn _ (getD_mem' w k hk)
                · rw [getD_default' w k (by omega)]
              linarith
    | 1 :: kind :: idx :: rest' =>
      rw [show ibpWalk dets minors (fuel + 1) (1 :: kind :: idx :: rest') lows w
          = (if kind == 0 then
              if 0 < lowBound (combinePoly (shiftPoly (dets.getD idx []) lows)) w then some rest'
              else none
            else if kind == 1 then
              if 0 < lowBound (combinePoly (shiftPoly (negPoly (dets.getD idx [])) lows)) w then
                some rest' else none
            else if kind == 2 then
              if 0 < lowBound (combinePoly (shiftPoly (negPoly (minors.getD idx [])) lows)) w then
                some rest' else none
            else none) from rfl] at hwalk
      -- shared facts: the shifted point t = s − lows lies in [0, w]
      set t := subLo lows s with htdef
      have htlen : t.length = lows.length := subLo_length lows s hlo.symm
      have htgetD : ∀ i, i < s.length →
          t.getD i 0 = s.getD i 0 - ((lows.getD i 0 : ℚ) : ℝ) := by
        rw [htdef]
        exact subLo_getD lows s hlo.symm
      have hslen : s.length = t.length := by rw [htlen, hlo]
      have ht0 : ∀ x ∈ t, (0:ℝ) ≤ x := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hi' : i < s.length := by rw [hslen]; exact hi
        have hgd : t.getD i 0 = t[i] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          rfl
        rw [← hgd, htgetD i hi']
        have := (hbox i hi').1
        linarith
      have htw : ∀ i, i < t.length →
          t.getD i 0 ≤ ((w.getD i 0 : ℚ) : ℝ) := by
        intro i hi
        have hi' : i < s.length := by rw [hslen]; exact hi
        rw [htgetD i hi']
        have := (hbox i hi').2
        push_cast at this ⊢
        linarith
      have hwt : w.length = t.length := by rw [htlen, hw, hlo]
      have haddback : addLo lows t = s := by
        rw [htdef]
        exact addLo_subLo lows s hlo.symm
      -- generic leaf discharge
      have hleaf : ∀ (P : Poly), evalPoly P s ≤ 0 →
          (∀ p ∈ P, (p.2 : List ℕ).length = s.length) →
          ¬ (0 < lowBound (combinePoly (shiftPoly P lows)) w) := by
        intro P hPle hPar hpos
        have harshift : ∀ q ∈ combinePoly (shiftPoly P lows),
            (q.2 : List ℕ).length ≤ t.length := by
          intro q hq
          obtain ⟨p1, hp1, hql⟩ := combinePoly_length (shiftPoly P lows) q hq
          obtain ⟨p, hp, hqlen⟩ := shiftPoly_length P lows p1 hp1
          rw [hql, hqlen, hPar p hp, hslen]
        have hb := lowBound_le (combinePoly (shiftPoly P lows)) w t ht0 htw hwt
          harshift hwnn
        have hsh : evalPoly (combinePoly (shiftPoly P lows)) t
            = evalPoly P (addLo lows t) := by
          rw [evalPoly_combinePoly]
          apply evalPoly_shiftPoly
          · intro p hp
            rw [hPar p hp, hlo]
          · rw [htlen]
        rw [hsh, haddback] at hb
        have hle0 : ((lowBound (combinePoly (shiftPoly P lows)) w : ℚ) : ℝ) ≤ 0 :=
          le_trans hb hPle
        have h0 : (0:ℝ) < ((lowBound (combinePoly (shiftPoly P lows)) w : ℚ) : ℝ) := by
          exact_mod_cast hpos
        linarith
      have hgetPoly : ∀ (L : List Poly) (i : ℕ),
          (∀ P ∈ L, evalPoly P s = 0) → evalPoly (L.getD i []) s = 0 := by
        intro L i hall
        by_cases hi : i < L.length
        · apply hall
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          exact List.getElem_mem hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          simp
      have hgetPolyM : ∀ (L : List Poly) (i : ℕ),
          (∀ P ∈ L, 0 ≤ evalPoly P s) → 0 ≤ evalPoly (L.getD i []) s := by
        intro L i hall
        by_cases hi : i < L.length
        · apply hall
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          exact List.getElem_mem hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          simp
      have hgetAr : ∀ (L : List Poly) (i : ℕ),
          (∀ P ∈ L, ∀ p ∈ P, (p.2 : List ℕ).length = s.length) →
          ∀ p ∈ (L.getD i []), (p.2 : List ℕ).length = s.length := by
        intro L i hall p hp
        by_cases hi : i < L.length
        · apply hall (L.getD i []) ?_ p hp
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          exact List.getElem_mem hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hp
          simp at hp
      have hdetAr : ∀ i, ∀ p ∈ (dets.getD i []), (p.2 : List ℕ).length = s.length :=
        fun i => hgetAr dets i (fun P hP => harity P (List.mem_append_left _ hP))
      have hminAr : ∀ i, ∀ p ∈ (minors.getD i []),
          (p.2 : List ℕ).length = s.length :=
        fun i => hgetAr minors i (fun P hP => harity P (List.mem_append_right _ hP))
      have hnegAr : ∀ (L : List Poly) (i : ℕ),
          (∀ p ∈ (L.getD i []), (p.2 : List ℕ).length = s.length) →
          ∀ p ∈ negPoly (L.getD i []), (p.2 : List ℕ).length = s.length := by
        intro L i hall p hp
        simp only [negPoly, List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        exact hall q hq
      by_cases hk0 : kind = 0
      · subst hk0
        simp only [beq_self_eq_true, if_true] at hwalk
        by_cases hcond : 0 < lowBound (combinePoly (shiftPoly (dets.getD idx []) lows)) w
        · exact hleaf (dets.getD idx []) (le_of_eq (hgetPoly dets idx hdets))
            (hdetAr idx) hcond
        · rw [if_neg hcond] at hwalk
          simp at hwalk
      · by_cases hk1 : kind = 1
        · subst hk1
          simp only [beq_iff_eq, if_false, if_true, hk0] at hwalk
          norm_num at hwalk
          rw [← List.getD_eq_getElem?_getD] at hwalk
          refine hleaf (negPoly (dets.getD idx [])) ?_
            (hnegAr dets idx (hdetAr idx)) hwalk.1
          rw [evalPoly_negPoly, hgetPoly dets idx hdets]
          simp
        · by_cases hk2 : kind = 2
          · subst hk2
            simp only [beq_iff_eq, hk0, hk1] at hwalk
            norm_num at hwalk
            rw [← List.getD_eq_getElem?_getD] at hwalk
            refine hleaf (negPoly (minors.getD idx [])) ?_
              (hnegAr minors idx (hminAr idx)) hwalk.1
            rw [evalPoly_negPoly]
            have := hgetPolyM minors idx hminors
            linarith
          · have hb0 : (kind == 0) = false := by simp [hk0]
            have hb1 : (kind == 1) = false := by simp [hk1]
            have hb2 : (kind == 2) = false := by simp [hk2]
            rw [hb0, hb1, hb2] at hwalk
            simp at hwalk
    | 1 :: kind :: [] => simp [ibpWalk] at hwalk
    | 1 :: [] => simp [ibpWalk] at hwalk
    | (n + 2) :: rest' => simp [ibpWalk] at hwalk

end IBP

end Kissing3D

namespace Kissing3D

namespace IBP



end IBP

end Kissing3D

namespace Kissing3D

namespace IBP

/-- Composition: a sub-walk returning remainder `r` extends over an appended
tail. -/
lemma ibpWalk_append (dets minors : List Poly) {fuel : ℕ}
    {l1 l2 r : List ℕ} {lows w : List ℚ}
    (h : ibpWalk dets minors fuel l1 lows w = some r) :
    ibpWalk dets minors fuel (l1 ++ l2) lows w = some (r ++ l2) := by
  induction fuel generalizing l1 r lows w with
  | zero => simp [ibpWalk] at h
  | succ fuel ih =>
    match l1 with
    | [] => simp [ibpWalk] at h
    | 0 :: k :: rest =>
      rw [show ibpWalk dets minors (fuel + 1) (0 :: k :: rest) lows w
          = (let w2 := w.set k (w.getD k 0 / 2)
             match ibpWalk dets minors fuel rest lows w2 with
             | none => none
             | some rest2 =>
               ibpWalk dets minors fuel rest2
                 (lows.set k (lows.getD k 0 + w.getD k 0 / 2)) w2) from rfl] at h
      rw [show (0 :: k :: rest) ++ l2 = 0 :: k :: (rest ++ l2) from rfl,
        show ibpWalk dets minors (fuel + 1) (0 :: k :: (rest ++ l2)) lows w
          = (let w2 := w.set k (w.getD k 0 / 2)
             match ibpWalk dets minors fuel (rest ++ l2) lows w2 with
             | none => none
             | some rest2 =>
               ibpWalk dets minors fuel rest2
                 (lows.set k (lows.getD k 0 + w.getD k 0 / 2)) w2) from rfl]
      simp only at h ⊢
      cases hw : ibpWalk dets minors fuel rest lows (w.set k (w.getD k 0 / 2)) with
      | none => rw [hw] at h; simp at h
      | some rest2 =>
        rw [hw] at h
        simp only at h
        rw [ih hw]
        simp only
        exact ih h
    | 1 :: kind :: idx :: rest =>
      rw [show ibpWalk dets minors (fuel + 1) (1 :: kind :: idx :: rest) lows w
          = (if kind == 0 then
              if 0 < lowBound (combinePoly (shiftPoly (dets.getD idx []) lows)) w then some rest
              else none
            else if kind == 1 then
              if 0 < lowBound (combinePoly (shiftPoly (negPoly (dets.getD idx [])) lows)) w then
                some rest else none
            else if kind == 2 then
              if 0 < lowBound (combinePoly (shiftPoly (negPoly (minors.getD idx [])) lows)) w then
                some rest else none
            else none) from rfl] at h
      rw [show (1 :: kind :: idx :: rest) ++ l2 = 1 :: kind :: idx :: (rest ++ l2)
          from rfl,
        show ibpWalk dets minors (fuel + 1) (1 :: kind :: idx :: (rest ++ l2)) lows w
          = (if kind == 0 then
              if 0 < lowBound (combinePoly (shiftPoly (dets.getD idx []) lows)) w then
                some (rest ++ l2) else none
            else if kind == 1 then
              if 0 < lowBound (combinePoly (shiftPoly (negPoly (dets.getD idx [])) lows)) w then
                some (rest ++ l2) else none
            else if kind == 2 then
              if 0 < lowBound (combinePoly (shiftPoly (negPoly (minors.getD idx [])) lows)) w then
                some (rest ++ l2) else none
            else none) from rfl]
      split_ifs at h ⊢ <;> simp_all
    | 1 :: kind :: [] => simp [ibpWalk] at h
    | 1 :: [] => simp [ibpWalk] at h
    | (n + 2) :: rest => simp [ibpWalk] at h

/-- Fuel monotonicity. -/
lemma ibpWalk_fuel_mono (dets minors : List Poly) {f f' : ℕ} (hf : f ≤ f') :
    ∀ {d : List ℕ} {lows w : List ℚ} {r : List ℕ},
    ibpWalk dets minors f d lows w = some r →
    ibpWalk dets minors f' d lows w = some r := by
  induction f' generalizing f with
  | zero =>
    intro d lows w r h
    interval_cases f
    simp [ibpWalk] at h
  | succ f' ih =>
    intro d lows w r h
    match f, h with
    | 0, h => simp [ibpWalk] at h
    | f + 1, h =>
      have hff : f ≤ f' := by omega
      match d with
      | [] => simp [ibpWalk] at h
      | 0 :: k :: rest =>
        rw [show ibpWalk dets minors (f + 1) (0 :: k :: rest) lows w
            = (let w2 := w.set k (w.getD k 0 / 2)
               match ibpWalk dets minors f rest lows w2 with
               | none => none
               | some rest2 =>
                 ibpWalk dets minors f rest2
                   (lows.set k (lows.getD k 0 + w.getD k 0 / 2)) w2) from rfl] at h
        rw [show ibpWalk dets minors (f' + 1) (0 :: k :: rest) lows w
            = (let w2 := w.set k (w.getD k 0 / 2)
               match ibpWalk dets minors f' rest lows w2 with
               | none => none
               | some rest2 =>
                 ibpWalk dets minors f' rest2
                   (lows.set k (lows.getD k 0 + w.getD k 0 / 2)) w2) from rfl]
        simp only at h ⊢
        cases hw : ibpWalk dets minors f rest lows (w.set k (w.getD k 0 / 2)) with
        | none => rw [hw] at h; simp at h
        | some rest2 =>
          rw [hw] at h
          simp only at h
          rw [ih hff hw]
          simp only
          exact ih hff h
      | 1 :: kind :: idx :: rest =>
        rw [show ibpWalk dets minors (f + 1) (1 :: kind :: idx :: rest) lows w
            = (if kind == 0 then
                if 0 < lowBound (combinePoly (shiftPoly (dets.getD idx []) lows)) w then some rest
                else none
              else if kind == 1 then
                if 0 < lowBound (combinePoly (shiftPoly (negPoly (dets.getD idx [])) lows)) w then
                  some rest else none
              else if kind == 2 then
                if 0 < lowBound (combinePoly (shiftPoly (negPoly (minors.getD idx [])) lows)) w then
                  some rest else none
              else none) from rfl] at h
        rw [show ibpWalk dets minors (f' + 1) (1 :: kind :: idx :: rest) lows w
            = (if kind == 0 then
                if 0 < lowBound (combinePoly (shiftPoly (dets.getD idx []) lows)) w then some rest
                else none
              else if kind == 1 then
                if 0 < lowBound (combinePoly (shiftPoly (negPoly (dets.getD idx [])) lows)) w then
                  some rest else none
              else if kind == 2 then
                if 0 < lowBound (combinePoly (shiftPoly (negPoly (minors.getD idx [])) lows)) w then
                  some rest else none
              else none) from rfl]
        exact h
      | 1 :: kind :: [] => simp [ibpWalk] at h
      | 1 :: [] => simp [ibpWalk] at h
      | (n + 2) :: rest => simp [ibpWalk] at h

/-- Symbolic branch composition for chunked kernel checks. -/
lemma ibpWalk_branch (dets minors : List Poly) {fuel : ℕ}
    {dL dR : List ℕ} {k : ℕ} {lows w : List ℚ}
    (hL : ibpWalk dets minors fuel dL lows (w.set k (w.getD k 0 / 2)) = some [])
    (hR : ibpWalk dets minors fuel dR
      (lows.set k (lows.getD k 0 + w.getD k 0 / 2)) (w.set k (w.getD k 0 / 2))
      = some []) :
    ibpWalk dets minors (fuel + 1) ((0 : ℕ) :: k :: (dL ++ dR)) lows w
      = some [] := by
  have hcomp := ibpWalk_append dets minors (l2 := dR) hL
  rw [List.nil_append] at hcomp
  rw [show ibpWalk dets minors (fuel + 1) (0 :: k :: (dL ++ dR)) lows w
      = (let w2 := w.set k (w.getD k 0 / 2)
         match ibpWalk dets minors fuel (dL ++ dR) lows w2 with
         | none => none
         | some rest2 =>
           ibpWalk dets minors fuel rest2
             (lows.set k (lows.getD k 0 + w.getD k 0 / 2)) w2) from rfl]
  simp only
  rw [hcomp]
  simp only
  exact hR

end IBP

end Kissing3D

namespace Kissing3D

namespace IBP

/-- Branch composition with explicit child boxes (the equations are decidable
ℚ-list computations, dischargeable by `decide`). -/
lemma ibpWalk_branch' (dets minors : List Poly) {fuel : ℕ}
    {dL dR : List ℕ} {k : ℕ} {lows w lows' w' : List ℚ}
    (hL : ibpWalk dets minors fuel dL lows w' = some [])
    (hR : ibpWalk dets minors fuel dR lows' w' = some [])
    (hw' : w' = w.set k (w.getD k 0 / 2))
    (hlo' : lows' = lows.set k (lows.getD k 0 + w.getD k 0 / 2)) :
    ibpWalk dets minors (fuel + 1) ((0 : ℕ) :: k :: (dL ++ dR)) lows w
      = some [] := by
  subst hw'
  subst hlo'
  exact ibpWalk_branch dets minors hL hR

end IBP

end Kissing3D
