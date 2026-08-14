#!/usr/bin/env python3
"""Generate Physics/Bipyramid7.lean: the unit-edge pentagonal bipyramid,
its 15 bonds, hard-core property, and E_min(7) = -15.

Radicals: s5 = sqrt 5, t = sqrt(10 - 2*sqrt 5).  Coordinates:
  base_k = (R cos(72k), R sin(72k), 0), apexes (0,0,+-h), which simplify to
  polynomials in s5, t over Q (R sin 72 = (1+s5)/4, R sin 144 = 1/2, h = s5*t/10).
"""
import sympy as sp

s5, t = sp.symbols("s5 t", positive=True)
REL = [s5**2 - 5, t**2 - (10 - 2 * s5)]

# symbolic coordinates and their Lean strings
S5 = "Real.sqrt 5"
T = "Real.sqrt (10 - 2 * Real.sqrt 5)"

pts_sym = [
    ((5 + s5) * t / 20, sp.Integer(0), sp.Integer(0)),
    (s5 * t / 20, (1 + s5) / sp.Integer(4), sp.Integer(0)),
    (-(5 + 3 * s5) * t / 40, sp.Rational(1, 2), sp.Integer(0)),
    (-(5 + 3 * s5) * t / 40, sp.Rational(-1, 2), sp.Integer(0)),
    (s5 * t / 20, -(1 + s5) / sp.Integer(4), sp.Integer(0)),
    (sp.Integer(0), sp.Integer(0), s5 * t / 10),
    (sp.Integer(0), sp.Integer(0), -s5 * t / 10),
]
pts_str = [
    (f"(5 + {S5}) * {T} / 20", "0", "0"),
    (f"{S5} * {T} / 20", f"(1 + {S5}) / 4", "0"),
    (f"-((5 + 3 * {S5}) * {T} / 40)", "1 / 2", "0"),
    (f"-((5 + 3 * {S5}) * {T} / 40)", "-(1 / 2)", "0"),
    (f"{S5} * {T} / 20", f"-((1 + {S5}) / 4)", "0"),
    ("0", "0", f"{S5} * {T} / 10"),
    ("0", "0", f"-({S5} * {T} / 10)"),
]

BONDS = [(0,1),(1,2),(2,3),(3,4),(0,4),
         (0,5),(1,5),(2,5),(3,5),(4,5),
         (0,6),(1,6),(2,6),(3,6),(4,6)]
NONBONDS = [(0,2),(0,3),(1,3),(1,4),(2,4),(5,6)]

def leanify(e):
    s = sp.sstr(sp.nsimplify(e), full_prec=False)
    s = s.replace("**", "^").replace("s5", "@A@").replace("t", "@B@")
    s = s.replace("@A@", f"({S5})").replace("@B@", f"({T})")
    return s

def dist2(i, j):
    (xi, yi, zi), (xj, yj, zj) = pts_sym[i], pts_sym[j]
    return sp.expand((xi - xj) ** 2 + (yi - yj) ** 2 + (zi - zj) ** 2)

def reduce_coeffs(expr):
    qs, r = sp.reduced(sp.expand(expr), [REL[1], REL[0]], t, s5, order='lex')
    while len(qs) < 2:
        qs.append(sp.Integer(0))
    qs = [qs[1], qs[0]]
    assert sp.simplify(r) == 0, f"nonzero remainder {r}"
    return qs

def show_expr(i, j):
    (xi, yi, zi), (xj, yj, zj) = pts_str[i], pts_str[j]
    return (f"(({xi} : ℝ) - ({xj}))^2 + (({yi} : ℝ) - ({yj}))^2 "
            f"+ (({zi} : ℝ) - ({zj}))^2")

def lc(qs):
    terms = []
    for q, name in zip(qs, ["hs5sq", "ht5sq"]):
        if q == 0:
            continue
        terms.append(f"({leanify(q)}) * {name}")
    return " + ".join(terms) if terms else "(0 : ℝ) * hs5sq"

L = []
L.append("import Physics.Emin7")
L.append("")
L.append("set_option linter.style.header false")
L.append("set_option maxHeartbeats 1000000")
L.append("")
L.append("/-!")
L.append("# `E_min(7) = −15`: the pentagonal bipyramid")
L.append("")
L.append("The unit-edge pentagonal bipyramid: a regular pentagon of side one (circumradius")
L.append("`R = 2/√(10−2√5) < 1`) with two apexes at height `√(1−R²)` above and below its")
L.append("centre. All 15 edges (5 ring + 10 apex) have length one; the five base diagonals")
L.append("are the golden ratio `(1+√5)/2` and the apex pair sits at `√5·√(10−2√5)/5 ≈ 1.051`,")
L.append("so the configuration is hard-core. With `energy_ge_seven_particles` this pins the")
L.append("seven-particle ground-state energy at exactly `−15`. This file is machine-generated")
L.append("by `scratch-h4/bipyr7_gen.py`.")
L.append("-/")
L.append("")
L.append("namespace Kissing3D")
L.append("")
for k in range(7):
    x, y, z = pts_str[k]
    L.append(f"/-- Pentagonal bipyramid vertex {k}. -/")
    L.append(f"noncomputable def pb{k} : E3 := WithLp.toLp 2 ![{x}, {y}, {z}]")
L.append("")
L.append("/-- The unit-edge pentagonal bipyramid. -/")
L.append("noncomputable def bipyr7 : Finset E3 := {pb0, pb1, pb2, pb3, pb4, pb5, pb6}")
L.append("")
L.append("section Bipyr7Distances")
L.append("")
L.append("private lemma hs5sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)")
L.append("")
L.append("private lemma hs5le : Real.sqrt 5 ≤ 5 / 2 := by")
L.append("  nlinarith [hs5sq, Real.sqrt_nonneg 5]")
L.append("")
L.append("private lemma ht5sq : Real.sqrt (10 - 2 * Real.sqrt 5) ^ 2 = 10 - 2 * Real.sqrt 5 :=")
L.append("  Real.sq_sqrt (by linarith [hs5le])")
L.append("")
L.append("private lemma ne_of_dist_one' {a b : E3} (h : dist a b = 1) : a ≠ b := by")
L.append("  rintro rfl")
L.append("  rw [dist_self] at h")
L.append("  norm_num at h")
L.append("")
L.append("private lemma ne_of_dist_ge_one {a b : E3} (h : 1 ≤ dist a b) : a ≠ b := by")
L.append("  rintro rfl")
L.append("  rw [dist_self] at h")
L.append("  linarith")
L.append("")

for (i, j) in BONDS:
    e = dist2(i, j)
    qs = reduce_coeffs(e - 1)
    se = show_expr(i, j)
    L.append(f"private lemma pd{i}{j} : dist pb{i} pb{j} = 1 := by")
    L.append("  rw [dist_coords]")
    L.append(f"  show Real.sqrt ({se}) = 1")
    L.append(f"  rw [show {se} = 1 by linear_combination {lc(qs)}]")
    L.append("  exact Real.sqrt_one")
    L.append("")

for (i, j) in NONBONDS:
    e = dist2(i, j)
    if (i, j) == (5, 6):
        target = "2 - 2 / 5 * Real.sqrt 5"
        tgt_sym = 2 - sp.Rational(2, 5) * s5
        bound = "  nlinarith [hs5le, Real.sqrt_nonneg 5]"
    else:
        target = "(3 + Real.sqrt 5) / 2"
        tgt_sym = (3 + s5) / 2
        bound = "  linarith [Real.sqrt_nonneg 5]"
    qs = reduce_coeffs(e - tgt_sym)
    se = show_expr(i, j)
    L.append(f"private lemma pge{i}{j} : 1 ≤ dist pb{i} pb{j} := by")
    L.append("  rw [dist_coords]")
    L.append(f"  show 1 ≤ Real.sqrt ({se})")
    L.append(f"  rw [show {se} = {target} by linear_combination {lc(qs)}]")
    L.append("  rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]")
    L.append("  apply Real.sqrt_le_sqrt")
    L.append(bound)
    L.append("")

# ne lemmas
ne_of = {}
for (i, j) in BONDS:
    ne_of[(i, j)] = f"ne_of_dist_one' pd{i}{j}"
for (i, j) in NONBONDS:
    ne_of[(i, j)] = f"ne_of_dist_ge_one pge{i}{j}"
for (i, j) in sorted(ne_of):
    L.append(f"private lemma pne{i}{j} : pb{i} ≠ pb{j} := {ne_of[(i,j)]}")
L.append("")
L.append("end Bipyr7Distances")
L.append("")
L.append("section Bipyr7Config")
L.append("")

def nes_from(i, rest):
    return ", ".join(f"pne{min(i,j)}{max(i,j)}" for j in rest)

# hard core
L.append("private lemma bipyr7_dist : ∀ u ∈ bipyr7, ∀ v ∈ bipyr7, u ≠ v → 1 ≤ dist u v := by")
L.append("  have key : ∀ a b : E3, dist a b = 1 → 1 ≤ dist a b ∧ 1 ≤ dist b a := by")
L.append("    intro a b h")
L.append("    exact ⟨by rw [h], by rw [dist_comm, h]⟩")
L.append("  have key2 : ∀ a b : E3, 1 ≤ dist a b → 1 ≤ dist a b ∧ 1 ≤ dist b a := by")
L.append("    intro a b h")
L.append("    exact ⟨h, by rw [dist_comm]; exact h⟩")
L.append("  intro u hu v hv huv")
L.append("  simp only [bipyr7, Finset.mem_insert, Finset.mem_singleton] at hu hv")
L.append("  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>")
L.append("    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>")
L.append("    first")
L.append("      | exact absurd rfl huv")
for (i, j) in BONDS:
    L.append(f"      | exact (key _ _ pd{i}{j}).1 | exact (key _ _ pd{i}{j}).2")
for (i, j) in NONBONDS:
    L.append(f"      | exact (key2 _ _ pge{i}{j}).1 | exact (key2 _ _ pge{i}{j}).2")
L.append("")
L.append("theorem hardCore_bipyr7 : HardCore bipyr7 := bipyr7_dist")
L.append("")
L.append("theorem card_bipyr7 : bipyr7.card = 7 := by")
L.append("  rw [bipyr7]")
for k in range(6):
    rest = range(k + 1, 7)
    L.append(f"  rw [Finset.card_insert_of_notMem (by simp [{nes_from(k, rest)}])]")
L.append("  rw [Finset.card_singleton]")
L.append("")

# neighbour lower bounds
NBRS = {0: [1, 4, 5, 6], 1: [0, 2, 5, 6], 2: [1, 3, 5, 6], 3: [2, 4, 5, 6],
        4: [0, 3, 5, 6], 5: [0, 1, 2, 3, 4], 6: [0, 1, 2, 3, 4]}
for k in range(7):
    nb = NBRS[k]
    deg = len(nb)
    setstr = ", ".join(f"pb{j}" for j in nb)
    L.append(f"private lemma pdeg{k} : {deg} ≤ (neighbors bipyr7 pb{k}).card := by")
    L.append(f"  have hsub : ({{{setstr}}} : Finset E3) ⊆ neighbors bipyr7 pb{k} := by")
    L.append("    intro u hu")
    L.append("    simp only [Finset.mem_insert, Finset.mem_singleton] at hu")
    L.append("    rcases hu with " + " | ".join(["rfl"] * deg))
    for j in nb:
        if (min(k, j), max(k, j)) in dict.fromkeys(BONDS):
            name = f"pd{min(k,j)}{max(k,j)}"
        else:
            raise AssertionError((k, j))
        if k < j:
            L.append(f"    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], {name}⟩")
        else:
            L.append(f"    · exact Finset.mem_filter.mpr ⟨by simp [bipyr7], by rw [dist_comm]; exact {name}⟩")
    L.append(f"  have hcard : ({{{setstr}}} : Finset E3).card = {deg} := by")
    chain = []
    for a in range(deg - 1):
        rest = nb[a + 1:]
        chain.append(f"    rw [Finset.card_insert_of_notMem (by simp [{nes_from(nb[a], rest)}])]")
    L.extend(chain)
    L.append("    rw [Finset.card_singleton]")
    L.append("  calc " + str(deg) + f" = ({{{setstr}}} : Finset E3).card := hcard.symm")
    L.append("    _ ≤ _ := Finset.card_le_card hsub")
    L.append("")

L.append("theorem energy_bipyr7 : energy bipyr7 = -15 := by")
L.append("  have hle : energy bipyr7 ≤ -15 := by")
L.append("    have hcc : 30 ≤ contactCount bipyr7 := by")
L.append("      rw [contactCount, bipyr7]")
for k in range(6):
    rest = range(k + 1, 7)
    L.append(f"      rw [Finset.sum_insert (by simp [{nes_from(k, rest)}])]")
L.append("      rw [Finset.sum_singleton]")
L.append("      simp only [show ({pb0, pb1, pb2, pb3, pb4, pb5, pb6} : Finset E3) = bipyr7 from rfl]")
L.append("      have h0 := pdeg0; have h1 := pdeg1; have h2 := pdeg2; have h3 := pdeg3")
L.append("      have h4 := pdeg4; have h5 := pdeg5; have h6 := pdeg6")
L.append("      omega")
L.append("    rw [energy]")
L.append("    have : (30 : ℝ) ≤ (contactCount bipyr7 : ℝ) := by exact_mod_cast hcc")
L.append("    linarith")
L.append("  have hge := energy_ge_seven_particles hardCore_bipyr7 card_bipyr7")
L.append("  linarith")
L.append("")
L.append("/-- **`E_min(7) = −15`**: the pentagonal bipyramid is the seven-particle ground")
L.append("state. The lower bound is the certificate-checked graph fact; the upper bound is")
L.append("this configuration. -/")
L.append("theorem groundState_seven :")
L.append("    (∀ X : Finset E3, HardCore X → X.card = 7 → -15 ≤ energy X) ∧")
L.append("    HardCore bipyr7 ∧ bipyr7.card = 7 ∧ energy bipyr7 = -15 :=")
L.append("  ⟨fun _ hX h => energy_ge_seven_particles hX h, hardCore_bipyr7, card_bipyr7,")
L.append("    energy_bipyr7⟩")
L.append("")
L.append("end Bipyr7Config")
L.append("")
L.append("end Kissing3D")

open("/home/marek/Documents/Lean/physics/Physics/Bipyramid7.lean", "w").write("\n".join(L) + "\n")

# numeric sanity
import math
vals = {s5: math.sqrt(5), t: math.sqrt(10 - 2 * math.sqrt(5))}
for (i, j) in BONDS:
    d = float(dist2(i, j).subs(vals))
    assert abs(d - 1) < 1e-12, (i, j, d)
for (i, j) in NONBONDS:
    d = float(dist2(i, j).subs(vals))
    assert d >= 1.0, (i, j, d)
print("wrote Physics/Bipyramid7.lean; numeric checks pass")
