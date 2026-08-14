#!/usr/bin/env python3
"""Emit the E_min(9) walk-tree modules Physics/Emin9TreeC{0..M-1}.lean plus the
composition skeleton Physics/Emin9Final.lean.

The serialized tree (scratch-h4/emin9_tree_final.dat) is cut into subtrees of at
most CHUNK leaves; each becomes `def sg{i}` + `lemma ck{i} : walk FUEL sg{i} k es
ns = some [] := by decide +kernel`.  The cuts are re-composed with walk_branch /
walk_fuel_mono, exactly as Emin8Final does.
Usage: emit_emin9_tree.py [chunk_leaves] [n_modules]"""
import sys

CHUNK = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
NMOD = int(sys.argv[2]) if len(sys.argv) > 2 else 6
FUEL = 8001

data = list(map(int, open('scratch-h4/emin9_tree_final.dat').read().split()))
pos = 0
def build():
    global pos
    c = data[pos]; pos += 1
    if c == 0:
        left = build()
        right = build()
        return ('S', left, right)
    return ('L', c)
tree = build()
assert pos == len(data), f'{pos} != {len(data)}'

def leaves_of(t):
    return 1 if t[0] == 'L' else leaves_of(t[1]) + leaves_of(t[2])

def ser(t):
    if t[0] == 'L':
        return [t[1]]
    return [0] + ser(t[1]) + ser(t[2])

chunks = []   # (data, k, es, ns, nleaves)
def chunkify(t, k, es, ns):
    if t[0] == 'L' or leaves_of(t) <= CHUNK:
        idx = len(chunks)
        chunks.append((ser(t), k, list(es), list(ns), leaves_of(t)))
        return ('C', idx)
    left = chunkify(t[1], k + 1, [k] + es, ns)
    right = chunkify(t[2], k + 1, es, [k] + ns)
    return ('S', k, left, right)

skel = chunkify(tree, 0, [], [])
print(f'nodes {len(data)}, leaves {leaves_of(tree)}, chunks {len(chunks)}')

def natlist(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"

# ---------------- chunk modules ----------------
per = (len(chunks) + NMOD - 1) // NMOD
mod_of = {}
for mi in range(NMOD):
    lo, hi = mi * per, min((mi + 1) * per, len(chunks))
    if lo >= hi:
        continue
    L = ['import Physics.Emin9', '',
         'set_option linter.style.header false',
         'set_option maxRecDepth 100000', '',
         f'/-! # E_min(9) kill-tree chunks {lo}..{hi - 1} -/', '',
         'namespace Kissing3D', 'namespace Emin9T', '']
    for ci in range(lo, hi):
        d, k, es, ns, nl = chunks[ci]
        mod_of[ci] = mi
        L.append(f'def sg{ci} : List Nat := ' + natlist(d))
        L.append('')
        L.append(f'lemma ck{ci} : walk {FUEL} sg{ci} {k} {natlist(es)} '
                 f'{natlist(ns)} = some [] := by')
        L.append('  decide +kernel')
        L.append('')
    L += ['end Emin9T', '', 'end Kissing3D']
    open(f'/home/marek/Documents/Lean/physics/Physics/Emin9TreeC{mi}.lean',
         'w').write('\n'.join(L) + '\n')
    print(f'  Emin9TreeC{mi}.lean: chunks {lo}..{hi - 1} '
          f'({sum(chunks[c][4] for c in range(lo, hi))} leaves)')
NMOD_USED = len(set(mod_of.values()))

# ---------------- composition ----------------
have_lines = []
ctr = 0
def emit(t):
    global ctr
    if t[0] == 'C':
        ci = t[1]
        return (f'ck{ci}', f'sg{ci}', FUEL)
    k = t[1]
    lterm, ldata, lf = emit(t[2])
    rterm, rdata, rf = emit(t[3])
    mf = max(lf, rf)
    if lf < mf:
        lterm = f'(walk_fuel_mono (by norm_num : {lf} ≤ {mf}) {lterm})'
    if rf < mf:
        rterm = f'(walk_fuel_mono (by norm_num : {rf} ≤ {mf}) {rterm})'
    nm = f'n{ctr}'; ctr += 1
    have_lines.append(f'  have {nm} := walk_branch (by norm_num : {k} < 36) '
                      f'{lterm} {rterm}')
    return (nm, f'((0 : ℕ) :: ({ldata} ++ {rdata}))', mf + 1)

root_term, root_data, root_fuel = emit(skel)

F = ['import Physics.Emin9', 'import Physics.Cap9']
for mi in range(NMOD_USED):
    F.append(f'import Physics.Emin9TreeC{mi}')
F += ['', 'set_option linter.style.header false',
      'set_option maxRecDepth 1000000', '',
      '/-! # E_min(9): the assembled kill tree and the ground-state bound',
      '',
      'The 131325-node canonical-enumeration tree is checked in chunks by the',
      'kernel and recomposed here with `walk_branch` / `walk_fuel_mono`.  Every',
      'leaf carries a certificate discharged by one of the 23 kill kinds, so no',
      'hard-core nine-point configuration reaches 43 ordered contacts. -/', '',
      'namespace Kissing3D', 'namespace Emin9T', '',
      f'lemma nine_tree : walk {root_fuel} ({root_data}) 0 [] [] = some [] := by']
F.extend(have_lines)
F.append(f'  exact {root_term}')
F += ['', 'end Emin9T', '',
      'open scoped Classical in',
      '/-- **Nine hard-core particles carry at most 42 ordered contacts** '
      '(21 bonds). -/',
      'theorem nine_particle_bound {X : Finset E3} (hX : HardCore X)',
      '    (h9 : X.card = 9) : contactCount X ≤ 42 :=',
      '  Emin9T.nine_particle_bound_of_tree Emin9T.nine_tree hX h9', '',
      '/-- **`E ≥ −21` for nine particles.** -/',
      'theorem energy_ge_nine_particles {X : Finset E3} (hX : HardCore X)',
      '    (h9 : X.card = 9) : -21 ≤ energy X := by',
      '  have hb := nine_particle_bound hX h9',
      '  rw [energy]',
      '  have hc : (contactCount X : ℝ) ≤ 42 := by exact_mod_cast hb',
      '  linarith', '',
      '/-- The doubly-capped pentagonal bipyramid is exactly optimal. -/',
      'theorem energy_capBipyr9 : energy capBipyr9 = -21 := by',
      '  have h1 := energy_capBipyr9_le',
      '  have h2 := energy_ge_nine_particles hardCore_capBipyr9 card_capBipyr9',
      '  linarith', '',
      '/-- **`E_min(9) = −21`**: the nine-particle ground-state energy, realised',
      'by the doubly-capped pentagonal bipyramid.  Resolves the case `n = 9` of',
      'the contact-number conjecture `c(n,3) = 3n − 6` (Bezdek–Khan, Conj. 5.2). -/',
      'theorem groundState_nine :',
      '    (∀ X : Finset E3, HardCore X → X.card = 9 → -21 ≤ energy X) ∧',
      '    HardCore capBipyr9 ∧ capBipyr9.card = 9 ∧ energy capBipyr9 = -21 :=',
      '  ⟨fun _ hX h => energy_ge_nine_particles hX h, hardCore_capBipyr9,',
      '    card_capBipyr9, energy_capBipyr9⟩', '',
      '#print axioms nine_particle_bound',
      '#print axioms energy_ge_nine_particles',
      '#print axioms energy_capBipyr9',
      '#print axioms groundState_nine', '',
      'end Kissing3D']
open('/home/marek/Documents/Lean/physics/Physics/Emin9Final.lean',
     'w').write('\n'.join(F) + '\n')
print(f'wrote Emin9Final.lean: root fuel {root_fuel}, {len(have_lines)} joins')
