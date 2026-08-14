#!/usr/bin/env python3
"""Automated Gram det-chain finder for a full N=9 survivor class.

Tries each base vertex (max degree first). Two step types:
  * univariate: a 4-subset det with exactly one unpinned unknown; pin its
    admissible root(s) in [1,4];
  * pair: two dets whose union of unknowns is {s,t}; the resultant in t is
    univariate in s -> pin s (Lean side: linear_combination with cofactors).
Succeeds when a fully-pinned det is nonzero or a det/resultant has no
admissible root. Usage: chain_finder.py <class_idx> [base]"""
import pickle, itertools, sys
import sympy as sp

ARG = sys.argv[1] if len(sys.argv) > 1 else '23'
BASE_ARG = int(sys.argv[2]) if len(sys.argv) > 2 else None
if ARG.startswith('p8_'):
    pats = pickle.load(open('scratch-h4/emin9_pat8.pkl', 'rb'))
    E_, resid, ks = pats[int(ARG[3:])]
    Eset = set(tuple(e) for e in E_)
    size = 8
    def adj(a, b): return (min(a, b), max(a, b)) in Eset
else:
    nc = pickle.load(open('scratch-h4/emin9_newclasses.pkl', 'rb'))
    degs, members, non = nc[int(ARG)]
    ns = set(non)
    size = 9
    def adj(a, b): return (min(a, b), max(a, b)) not in ns
degmap = {v: sum(1 for a in range(size) if a != v and adj(a, v))
          for v in range(size)}
BASES = ([BASE_ARG] if BASE_ARG is not None
         else sorted(range(size), key=lambda v: -degmap[v]))

syms = {}
for a, b in itertools.combinations(range(size), 2):
    if not adj(a, b):
        syms[(a, b)] = sp.Symbol(f's{a}{b}', real=True)

def boxroots(expr, s):
    roots = sp.solve(sp.Eq(expr, 0), s)
    box = []
    for r in roots:
        try:
            rn = complex(sp.N(r))
        except Exception:
            continue
        if abs(rn.imag) < 1e-9 and 1 - 1e-9 <= rn.real <= 4 + 1e-9:
            box.append(sp.simplify(r))
    return list(dict.fromkeys(box))

ALLSTEPS = []
for w in range(size):
    for sub in itertools.combinations([v for v in range(size) if v != w], 4):
        ALLSTEPS.append((w, sub))

def sq_g(a, b, pins):
    if a == b:
        return sp.Integer(0)
    key = (min(a, b), max(a, b))
    if adj(a, b):
        return sp.Integer(1)
    if key in pins:
        return pins[key]
    return syms[key]

def ip_g(w, a, b, pins):
    if a == b:
        return sq_g(w, a, pins)
    return sp.Rational(1, 2)*(sq_g(w, a, pins) + sq_g(w, b, pins)
                              - sq_g(a, b, pins))

def detexpr_g(w, sub, pins):
    return sp.expand(sp.Matrix(4, 4,
                     lambda i, j: ip_g(w, sub[i], sub[j], pins)).det())

def run_base(base):
    subs4 = ALLSTEPS

    def detexpr(step, pins):
        w, sub = step
        return detexpr_g(w, sub, pins)

    def try_chain(pins, depth, log):
        for sub in subs4:
            d = detexpr(sub, pins)
            if not d.free_symbols and d != 0:
                log.append(f'CONTRADICTION det{sub} = {d}')
                return True
        if depth > 14:
            log.append('depth limit')
            return False
        best = None
        for sub in subs4:
            d = detexpr(sub, pins)
            fv = list(d.free_symbols)
            if len(fv) == 1:
                s = fv[0]
                box = boxroots(d, s)
                if best is None or len(box) < best[2]:
                    best = (sub, s, len(box), box)
                if best[2] == 0:
                    break
        if best is not None:
            sub, s, nroots, roots = best
            key = (int(str(s)[1]), int(str(s)[2]))
            if nroots == 0:
                log.append(f'det{sub}: {s} NO admissible root -> dead')
                return True
            ok = True
            for r in roots:
                log.append(f'depth {depth}: det{sub} pins {s} = {r}')
                pins2 = dict(pins)
                pins2[key] = r
                if not try_chain(pins2, depth + 1, log):
                    ok = False
                    break
            return ok
        # pair-step
        twos = []
        for sub in subs4:
            d = detexpr(sub, pins)
            fv = d.free_symbols
            if 1 <= len(fv) <= 2:
                twos.append((sub, d, fv))
        pair_found = None
        for a in range(len(twos)):
            for b in range(a + 1, len(twos)):
                fv = twos[a][2] | twos[b][2]
                if len(fv) != 2:
                    continue
                s, t = sorted(fv, key=str)
                R = sp.expand(sp.resultant(twos[a][1], twos[b][1], t))
                if R == 0 or s not in R.free_symbols:
                    continue
                box = boxroots(R, s)
                if pair_found is None or len(box) < pair_found[4]:
                    pair_found = (twos[a][0], twos[b][0], s, t, len(box), box)
                if pair_found[4] <= 1:
                    break
            if pair_found and pair_found[4] <= 1:
                break
        if pair_found is None:
            log.append(f'no univariate det or usable pair at depth {depth}')
            return False
        sub1, sub2, s, t, nroots, roots = pair_found
        key = (int(str(s)[1]), int(str(s)[2]))
        if nroots == 0:
            log.append(f'pair det{sub1},det{sub2} elim {t}: {s} NO root -> dead')
            return True
        ok = True
        for r in roots:
            log.append(f'depth {depth}: PAIR det{sub1},det{sub2} elim {t} '
                       f'pins {s} = {r}')
            pins2 = dict(pins)
            pins2[key] = r
            if not try_chain(pins2, depth + 1, log):
                ok = False
                break
        return ok

    log = []
    result = try_chain({}, 0, log)
    return result, log

result, log = run_base(0)
for line in log[-50:]:
    print(line, flush=True)
print('CHAIN COMPLETE' if result else 'CHAIN INCOMPLETE', flush=True)
