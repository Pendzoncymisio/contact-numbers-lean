#!/usr/bin/env python3
"""Emit Physics/Emin9Q{k}.lean from an IBP tree (scratch-h4/ibp_p8_{k}.pkl):
static det/minor Poly data, chunked kernel checks of ibpWalk, a composed tree
lemma, and the geometric wrapper feeding ibpWalk_impossible.
Usage: emit_ibp_pattern.py <k> [chunk_leaves]"""
import sys, pickle, itertools
from fractions import Fraction as F
import sympy as sp

K = int(sys.argv[1])
CHUNK = int(sys.argv[2]) if len(sys.argv) > 2 else 150
d = pickle.load(open(f'scratch-h4/ibp_p8_{K}.pkl', 'rb'))
pats = pickle.load(open('scratch-h4/emin9_pat8.pkl', 'rb'))
E_, resid, ks = pats[K]
Eset = set(tuple(e) for e in E_)
size = 8
base = d['base']
others = [v for v in range(size) if v != base]
def adj(a, b): return (min(a, b), max(a, b)) in Eset
vars_ = [sp.Symbol(v, real=True) for v in d['vars']]
loc = {str(v): v for v in vars_}
n = len(vars_)
dets = [sp.Poly(sp.sympify(s, locals=loc), *vars_) for s in d['dets']]
minors = [sp.Poly(sp.sympify(s, locals=loc), *vars_) for s in d['minors']]
det_subs = list(itertools.combinations(others, 4))
m2subs = list(itertools.combinations(others, 2))
m3subs = list(itertools.combinations(others, 3))

# ---------------- serialize the tree with chunk splitting ----------------
# rebuild the tree structure from the preorder leaves list
entries = d['leaves']
pos = 0
def build():
    global pos
    e = entries[pos]; pos += 1
    if e[0] == 'split':
        k = e[1]
        left = build()
        right = build()
        return ('S', k, left, right)
    kind = {'pos': 0, 'neg': 1, 'mneg': 2}[e[0]]
    return ('L', kind, e[1])
tree = build()
assert pos == len(entries)

def count(t):
    if t[0] == 'L':
        return 1
    return 1 + count(t[2]) + count(t[3])

def ser(t):
    if t[0] == 'L':
        return [1, t[1], t[2]]
    return [0, t[1]] + ser(t[2]) + ser(t[3])

# chunk: cut subtrees with <= CHUNK leaves; box tracked during descent
chunks = []   # (data list, lo list, w list, nleaves)
def leaves_of(t):
    if t[0] == 'L':
        return 1
    return leaves_of(t[2]) + leaves_of(t[3])

def chunkify(t, lo, w):
    nl = leaves_of(t)
    if nl <= CHUNK or t[0] == 'L':
        idx = len(chunks)
        chunks.append((ser(t), list(lo), list(w), nl))
        return ('C', idx)
    k = t[1]
    w2 = list(w); w2[k] = w[k]/2
    loB = list(lo); loB[k] = lo[k] + w[k]/2
    left = chunkify(t[2], lo, w2)
    right = chunkify(t[3], loB, w2)
    return ('S', k, left, right)

lo0 = [F(1)]*n
w0 = [F(3)]*n
skel = chunkify(tree, lo0, w0)
maxdepth_sk = 0
def skdepth(t, dep=0):
    global maxdepth_sk
    maxdepth_sk = max(maxdepth_sk, dep)
    if t[0] == 'S':
        skdepth(t[2], dep+1)
        skdepth(t[3], dep+1)
skdepth(skel)
FUEL = 200   # covers max tree depth (<= 60 splits + leaf codes)
print(f'tree nodes {count(tree)}, chunks {len(chunks)}, skel depth {maxdepth_sk}')

def ratl(q):
    q = sp.Rational(q)
    return f"({q.p} : ℚ)" if q.q == 1 else f"(({q.p} : ℚ) / {q.q})"

def poly_data(P):
    terms = [(sp.Rational(c), list(e)) for e, c in P.terms()]
    return "[" + ", ".join(f"({ratl(c)}, {e})" for c, e in terms) + "]"

SLICES = int(sys.argv[3]) if len(sys.argv) > 3 else 1

HDR = ['set_option linter.style.header false',
       # the 35-determinant data definition alone exceeds 4e6 heartbeats once the
       # pattern has 11 variables (Q28), so give elaboration real headroom
       'set_option maxHeartbeats 200000000',
       'set_option maxRecDepth 1000000', '']

def chunk_lemma(ci, private=True):
    data, lo, w, nl = chunks[ci]
    lol = "[" + ", ".join(ratl(x) for x in lo) + "]"
    wl = "[" + ", ".join(ratl(x) for x in w) + "]"
    p = 'private ' if private else ''
    return [f'{p}def q{K}sg{ci} : List ℕ := {data}',
            '',
            f'{p}lemma q{K}ck{ci} : ibpWalk q{K}D q{K}M {FUEL} q{K}sg{ci} '
            f'{lol} {wl} = some [] := by',
            '  decide +kernel', '']

if SLICES > 1:
    # A single Lean process retaining every chunk proof term runs out of memory
    # (Q28: 898 chunks, >22 GiB and climbing).  Split the chunks across slice
    # modules; the composition module then imports oleans instead of elaborating.
    D = ['import Physics.IntervalBP', ''] + HDR + [
        f'/-! # IBP pattern q{K}: determinant and minor data -/', '',
        'namespace Kissing3D', '', 'open IBP', '',
        f'def q{K}D : List IBP.Poly := [',
        ',\n'.join('  ' + poly_data(P) for P in dets), ']', '',
        f'def q{K}M : List IBP.Poly := [',
        ',\n'.join('  ' + poly_data(P) for P in minors), ']', '',
        'end Kissing3D']
    open(f'/home/marek/Documents/Lean/physics/Physics/Emin9Q{K}Data.lean',
         'w').write('\n'.join(D) + '\n')
    per = (len(chunks) + SLICES - 1) // SLICES
    slice_mods = []
    for si in range(SLICES):
        lo_i, hi_i = si * per, min((si + 1) * per, len(chunks))
        if lo_i >= hi_i:
            continue
        slice_mods.append(si)
        S = [f'import Physics.Emin9Q{K}Data', ''] + HDR + [
            f'/-! # IBP pattern q{K}: kernel-checked chunks {lo_i}..{hi_i - 1} -/',
            '', 'namespace Kissing3D', '', 'open IBP', '']
        for ci in range(lo_i, hi_i):
            S += chunk_lemma(ci, private=False)
        S.append('end Kissing3D')
        open(f'/home/marek/Documents/Lean/physics/Physics/Emin9Q{K}TreeS{si}.lean',
             'w').write('\n'.join(S) + '\n')
    L = [f'import Physics.Emin9Q{K}TreeS{si}' for si in slice_mods]
    L.append('')
    L += HDR
    L.append(f'/-! # IBP pattern q{K}: the composed branch-and-prune tree -/')
    L.append('')
    L.append('namespace Kissing3D')
    L.append('')
    L.append('open IBP')
    L.append('')
    print(f'sliced layout: Data + {len(slice_mods)} slices '
          f'(<= {per} chunks each) + Tree')
else:
    L = ['import Physics.IntervalBP', ''] + HDR
    L.append(f'/-! # IBP kill lemma: 8-point pattern q{K} '
             f'(kills classes {sorted(ks)}) -/')
    L.append('')
    L.append('namespace Kissing3D')
    L.append('')
    L.append('open IBP')
    L.append('')
    L.append(f'def q{K}D : List IBP.Poly := [')
    L.append(',\n'.join('  ' + poly_data(P) for P in dets))
    L.append(']')
    L.append('')
    L.append(f'def q{K}M : List IBP.Poly := [')
    L.append(',\n'.join('  ' + poly_data(P) for P in minors))
    L.append(']')
    L.append('')
    for ci in range(len(chunks)):
        L += chunk_lemma(ci, private=True)

# composed tree lemma: type-free haves (types inferred), explicit root only
have_lines = []
ctr = 0

def emit3(t, lo, w):
    global ctr
    if t[0] == 'C':
        ci = t[1]
        return (f'q{K}ck{ci}', f'q{K}sg{ci}', FUEL)
    k = t[1]
    w2 = list(w); w2[k] = w[k]/2
    loB = list(lo); loB[k] = lo[k] + w[k]/2
    lterm, ldata, lf = emit3(t[2], lo, w2)
    rterm, rdata, rf = emit3(t[3], loB, w2)
    mf = max(lf, rf)
    if lf < mf:
        lterm = (f'(ibpWalk_fuel_mono q{K}D q{K}M (by omega : {lf} ≤ {mf}) '
                 f'{lterm})')
    if rf < mf:
        rterm = (f'(ibpWalk_fuel_mono q{K}D q{K}M (by omega : {rf} ≤ {mf}) '
                 f'{rterm})')
    nm = f'hnd{ctr}'; ctr += 1
    lol = "[" + ", ".join(ratl(x) for x in lo) + "]"
    wl = "[" + ", ".join(ratl(x) for x in w) + "]"
    have_lines.append(
        f"  have {nm} := ibpWalk_branch' q{K}D q{K}M (k := {k}) "
        f"(lo := {lol}) (w := {wl}) {lterm} {rterm} "
        f"(by decide +kernel) (by decide +kernel)")
    return (nm, f'((0 : ℕ) :: {k} :: ({ldata} ++ {rdata}))', mf + 1)

def ratlist(xs):
    return "[" + ", ".join(ratl(x) for x in xs) + "]"

root_term, root_data, root_fuel = emit3(skel, lo0, w0)
L.append(f'lemma q{K}tree : ibpWalk q{K}D q{K}M {root_fuel} '
         f'({root_data}) {ratlist(lo0)} {ratlist(w0)} = some [] := by')
L.extend(have_lines)
L.append(f'  exact {root_term}')
L.append('')
L.append('end Kissing3D')
open(f'/home/marek/Documents/Lean/physics/Physics/Emin9Q{K}Tree.lean', 'w').write(
    '\n'.join(L) + '\n')
print(f'wrote Physics/Emin9Q{K}Tree.lean (data+tree), {len(chunks)} chunks; '
      f'root fuel {root_fuel}')
# record the root data expression for the wrapper emitter
pickle.dump({'K': K, 'root_data': root_data, 'root_fuel': root_fuel,
             'n': n, 'base': base, 'vars': [str(v) for v in vars_],
             'det_subs': det_subs, 'm2subs': m2subs, 'm3subs': m3subs},
            open(f'scratch-h4/ibp_wrap_{K}.pkl', 'wb'))
