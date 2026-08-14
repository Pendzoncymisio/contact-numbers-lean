#!/usr/bin/env python3
"""Independent replay of Physics/Emin9.lean's `walk` over emin9_tree_final.dat.

Mirrors the Lean semantics exactly:
  pairIdx9 i j = max*(max-1)/2 + min
  fld cert k   = cert / (64 * 16^k) % 16
  walk: 0 = branch on pair k (edge branch first, then non-edge),
        odd c = kill leaf with cert (c-1)/2, kind = cert % 64
and re-derives every pattern's edge list from the pickles rather than
trusting the tree generator's copy.  Fails loudly on the first bad leaf.
"""
import pickle, itertools, sys

sys.setrecursionlimit(300000)
V = list(range(9))

def pairIdx9(i, j):
    a, b = min(i, j), max(i, j)
    return b * (b - 1) // 2 + a

PAIRS = [None] * 36
for i, j in itertools.combinations(V, 2):
    PAIRS[pairIdx9(i, j)] = (i, j)
assert all(p is not None for p in PAIRS)
def pairFst(k): return PAIRS[k][0]
def pairSnd(k): return PAIRS[k][1]

def fld(cert, k):
    return cert // (64 * 16 ** k) % 16

# ---------------- pattern table (must match emin9_gen.py) ----------------
P6E = [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,5),(2,3),(2,5),(3,5),(4,5)]
P1L = [(0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(2,3),(2,4),(3,4),
       (0,6),(1,6),(2,6),(3,6),(4,6),(5,6)]
P4L = [(0,1),(0,4),(0,5),(1,2),(1,3),(2,3),(2,5),(3,4),(4,5),
       (0,6),(1,6),(2,6),(3,6),(4,6),(5,6)]
P5L = [(0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(2,3),(2,5),(3,4),
       (1,6),(2,6),(3,6),(4,6),(5,6)]
d = pickle.load(open('scratch-h4/emin9_subpat.pkl', 'rb'))
nc = pickle.load(open('scratch-h4/emin9_newclasses.pkl', 'rb'))
pats8 = pickle.load(open('scratch-h4/emin9_pat8.pkl', 'rb'))
OBS_IDXS = [7, 3, 0]
CLASS_IDXS = sorted(set(pickle.load(open('scratch-h4/emin9_proven_classes.pkl', 'rb')))
                    | {23})
P8_PROVEN = pickle.load(open('scratch-h4/emin9_proven_p8.pkl', 'rb'))

PAT = {6: (7, P1L), 7: (7, P4L), 8: (7, P5L), 10: (6, sorted(P6E))}
kind = 11
for k in OBS_IDXS:
    PAT[kind] = (7, sorted(tuple(e) for e in d['obstructions'][k][0])); kind += 1
for c in CLASS_IDXS:
    ns = set(nc[c][2])
    PAT[kind] = (9, sorted(p for p in itertools.combinations(V, 2) if p not in ns))
    kind += 1
for pk in P8_PROVEN:
    PAT[kind] = (8, sorted(tuple(e) for e in pats8[pk][0])); kind += 1
NKINDS = kind
PATNAME = ({6: 'P1', 7: 'P4', 8: 'P5', 10: 'P6'} |
           {11 + i: f'obs{k}' for i, k in enumerate(OBS_IDXS)} |
           {11 + len(OBS_IDXS) + i: f'class{c}' for i, c in enumerate(CLASS_IDXS)} |
           {11 + len(OBS_IDXS) + len(CLASS_IDXS) + i: f'q{p}'
            for i, p in enumerate(P8_PROVEN)})

# ---------------- certificate checking ----------------
def eMem(es, i, j):
    return i < 9 and j < 9 and i != j and pairIdx9(i, j) in es

def embeds(cert, es, nl, edges):
    """the labelled map m must be injective into 0..8 and carry every pattern
    edge to a decided bond"""
    m = [fld(cert, t) for t in range(nl)]
    if any(x >= 9 for x in m) or len(set(m)) != nl:
        return False
    return all(eMem(es, m[a], m[b]) for a, b in edges)

def check(cert, es, ns):
    kind = cert % 64
    if kind == 0:
        v = fld(cert, 0)
        return v < 9 and sum(1 for k in ns if pairFst(k) == v or pairSnd(k) == v) >= 5
    if kind == 1:
        return len(ns) >= 15
    if kind == 2:
        m = [fld(cert, t) for t in range(5)]
        return all(eMem(es, a, b) for a, b in itertools.combinations(m, 2))
    if kind == 3:
        u, v, c, x, y, z = (fld(cert, t) for t in range(6))
        return (eMem(es, u, v) and eMem(es, u, c) and eMem(es, v, c) and
                all(eMem(es, u, t) and eMem(es, v, t) for t in (x, y, z)) and
                all(eMem(es, c, t) for t in (x, y, z)) and
                len({x, y, z}) == 3)
    if kind == 4:
        u, v = fld(cert, 0), fld(cert, 1)
        w = [fld(cert, 2 + t) for t in range(6)]
        return (eMem(es, u, v) and
                all(eMem(es, u, t) and eMem(es, v, t) for t in w) and
                len(set(w)) == 6)
    if kind == 5:
        a, b, c = (fld(cert, t) for t in range(3))
        w = [fld(cert, 3 + t) for t in range(3)]
        return (len({a, b, c}) == 3 and len(set(w)) == 3 and
                all(eMem(es, x, t) for x in (a, b, c) for t in w))
    if kind == 9:
        m = [fld(cert, t) for t in range(9)]
        i = fld(cert, 9) + 16 * fld(cert, 10)
        if any(x >= 9 for x in m) or len(set(m)) != 9 or i >= 36:
            return False
        for j in range(i):
            img = pairIdx9(m[pairFst(j)], m[pairSnd(j)])
            if not ((j in es and img in es) or (j in ns and img in ns)):
                return False
        return i in ns and pairIdx9(m[pairFst(i)], m[pairSnd(i)]) in es
    if kind in PAT:
        nl, edges = PAT[kind]
        return embeds(cert, es, nl, edges)
    return False

# ---------------- replay ----------------
data = list(map(int, open('scratch-h4/emin9_tree_final.dat').read().split()))
pos = 0
leaves = 0
kindct = {}
maxdepth = 0

def walk(k, es, ns, depth):
    global pos, leaves, maxdepth
    maxdepth = max(maxdepth, depth)
    c = data[pos]; pos += 1
    if c == 0:
        if k >= 36:
            raise AssertionError(f'branch past pair 36 at pos {pos-1}')
        walk(k + 1, es | {k}, ns, depth + 1)
        walk(k + 1, es, ns | {k}, depth + 1)
        return
    cert = (c - 1) // 2
    if (c - 1) % 2 != 0:
        raise AssertionError(f'leaf token {c} is not 2*cert+1 at pos {pos-1}')
    if not check(cert, es, ns):
        raise AssertionError(
            f'BAD CERT at pos {pos-1}: cert={cert} kind={cert % 64} '
            f'es={sorted(es)} ns={sorted(ns)}')
    leaves += 1
    kindct[cert % 64] = kindct.get(cert % 64, 0) + 1

walk(0, frozenset(), frozenset(), 0)
assert pos == len(data), f'trailing data: consumed {pos} of {len(data)}'
named = {f'{k}:{PATNAME.get(k, "cheap")}': v for k, v in sorted(kindct.items())}
print(f'OK  nodes={len(data)}  leaves={leaves}  max depth={maxdepth}')
print(f'kinds used: {named}')
print(f'NKINDS={NKINDS}; every leaf certificate verified independently.')
