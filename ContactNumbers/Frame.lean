/-
  Orthonormal-frame utilities: the cross product in `ℝ³` and the Parseval identity
  for the frame `(p, e, p × e)`.  Extracted verbatim from the parent development
  (`Physics/CapCount.lean`), which is not otherwise needed here.
-/
import ContactNumbers.Basic

namespace Kissing3D

def cross3 (p e : Fin 3 → ℝ) : Fin 3 → ℝ := fun i =>
  if i = 0 then p 1 * e 2 - p 2 * e 1
  else if i = 1 then p 2 * e 0 - p 0 * e 2
  else p 0 * e 1 - p 1 * e 0

@[simp] theorem cross3_zero (p e : Fin 3 → ℝ) : cross3 p e 0 = p 1 * e 2 - p 2 * e 1 := rfl

@[simp] theorem cross3_one (p e : Fin 3 → ℝ) : cross3 p e 1 = p 2 * e 0 - p 0 * e 2 := rfl

@[simp] theorem cross3_two (p e : Fin 3 → ℝ) : cross3 p e 2 = p 0 * e 1 - p 1 * e 0 := rfl

/-- **Parseval in the frame `{p, e, p × e}`.** For `p` and `e` orthonormal in `ℝ³` the three
vectors form an orthonormal basis, so every inner product splits into three coordinates. The
proof is ideal membership: the certificate below was computed once and is checked by `ring`. -/
theorem parseval3 (p e u v : Fin 3 → ℝ) (hp : dot3 p p = 1) (he : dot3 e e = 1)
    (hpe : dot3 p e = 0) :
    dot3 u v = dot3 p u * dot3 p v + dot3 e u * dot3 e v
             + dot3 (cross3 p e) u * dot3 (cross3 p e) v := by
  simp only [dot3, cross3_zero, cross3_one, cross3_two] at *
  linear_combination
    (-e 0 ^ 2 * u 1 * v 1 + e 0 * e 1 * u 0 * v 1 + e 0 * e 1 * u 1 * v 0
      + e 0 * e 2 * u 0 * v 2 + e 0 * e 2 * u 2 * v 0 - e 1 ^ 2 * u 0 * v 0
      + e 1 * e 2 * u 1 * v 2 + e 1 * e 2 * u 2 * v 1 - e 2 ^ 2 * u 0 * v 0
      - e 2 ^ 2 * u 1 * v 1 + e 2 ^ 2 * u 2 * v 2 - u 2 * v 2) * hp
    + (p 0 ^ 2 * u 0 * v 0 - p 0 ^ 2 * u 2 * v 2 + p 0 * p 1 * u 0 * v 1
      + p 0 * p 1 * u 1 * v 0 + p 0 * p 2 * u 0 * v 2 + p 0 * p 2 * u 2 * v 0
      + p 1 ^ 2 * u 1 * v 1 - p 1 ^ 2 * u 2 * v 2 + p 1 * p 2 * u 1 * v 2
      + p 1 * p 2 * u 2 * v 1 - u 0 * v 0 - u 1 * v 1) * he
    + (-e 0 * p 0 * u 0 * v 0 + e 0 * p 0 * u 1 * v 1 + e 0 * p 0 * u 2 * v 2
      - e 0 * p 1 * u 0 * v 1 - e 0 * p 1 * u 1 * v 0 - e 0 * p 2 * u 0 * v 2
      - e 0 * p 2 * u 2 * v 0 - e 1 * p 0 * u 0 * v 1 - e 1 * p 0 * u 1 * v 0
      + e 1 * p 1 * u 0 * v 0 - e 1 * p 1 * u 1 * v 1 + e 1 * p 1 * u 2 * v 2
      - e 1 * p 2 * u 1 * v 2 - e 1 * p 2 * u 2 * v 1 - e 2 * p 0 * u 0 * v 2
      - e 2 * p 0 * u 2 * v 0 - e 2 * p 1 * u 1 * v 2 - e 2 * p 1 * u 2 * v 1
      + e 2 * p 2 * u 0 * v 0 + e 2 * p 2 * u 1 * v 1 - e 2 * p 2 * u 2 * v 2) * hpe


end Kissing3D
