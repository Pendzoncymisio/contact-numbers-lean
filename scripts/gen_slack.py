#!/usr/bin/env python3
"""Slack-absorbed SOS kill-lemma generator (the production path).

Per target (obs{k} or class{c}):
 1. numeric SDP with PSD margin eps (all blocks, box [1,4]^n, principal minors),
 2. round lambda/Q to 2^-k rationals; exact residual E := 1 + sum lam~ e + sigma~,
 3. bound B := sum_{c>0} c 4^deg + sum_{c<0} c ; require B < 1/2,
 4. exact PSD (LDL) of rounded blocks,
 5. emit Physics/Emin9P{k}s.lean / Emin9C{c}.lean:
    scalar lemma:  key : sigma~ = -1 + E   (linear_combination of det hyps)
                   monomial bounds via mono_step chains, E <= B, positivity, done
    wrapper: identical geometry layer as emit_obs_lean.
Usage: gen_slack.py obs15 | class23 | class12 ...
"""
import sys, pickle, itertools
from fractions import Fraction
import numpy as np
import sympy as sp
sys.path.insert(0, 'scratch-h4')
from sos_lib import GramSystem, monomials

target = sys.argv[1]
BITS = int(sys.argv[2]) if len(sys.argv) > 2 else 16

# ---------------- build system ----------------
if target.startswith('obs'):
    idx = int(target[3:])
    d = pickle.load(open('scratch-h4/emin9_subpat.pkl', 'rb'))
    E_, size, kills, resid = d['obstructions'][idx]
    Eset = set(E_)
    lean_name = f'pattern_obs{idx}_impossible'
    scalar_name = f'obs{idx}s_scalar'
    out_path = f'/home/marek/Documents/Lean/physics/Physics/Emin9P{idx}.lean'
    title = f'obstruction `obs{idx}`'
elif target.startswith('p8_'):
    pidx = int(target[3:])
    pats = pickle.load(open('scratch-h4/emin9_pat8.pkl', 'rb'))
    E_, resid, ks = pats[pidx]
    Eset = set(tuple(e) for e in E_)
    size = 8
    lean_name = f'pattern_q{pidx}_impossible'
    scalar_name = f'q{pidx}_scalar'
    out_path = f'/home/marek/Documents/Lean/physics/Physics/Emin9Q{pidx}.lean'
    title = f'8-point pattern q{pidx} (kills classes {sorted(ks)})'
else:
    cidx = int(target[5:])
    nc = pickle.load(open('scratch-h4/emin9_newclasses.pkl', 'rb'))
    degs, members, non = nc[cidx]
    ns_ = set(non)
    size = 9
    Eset = set(p for p in itertools.combinations(range(size), 2) if p not in ns_)
    lean_name = f'pattern_class{cidx}_impossible'
    scalar_name = f'class{cidx}_scalar'
    out_path = f'/home/marek/Documents/Lean/physics/Physics/Emin9C{cidx}.lean'
    title = f'survivor class {cidx}'

deg = {v: sum(1 for e in Eset if v in e) for v in range(size)}
base = max(range(size), key=lambda v: deg[v])
others = [v for v in range(size) if v != base]

def adj(a, b):
    return (min(a, b), max(a, b)) in Eset

sq = {}
vars_ = []
for a, b in itertools.combinations(range(size), 2):
    if adj(a, b):
        sq[(a, b)] = sp.Integer(1)
    else:
        s = sp.Symbol(f's{a}{b}', real=True)
        sq[(a, b)] = s
        vars_.append(s)
    sq[(b, a)] = sq[(a, b)]
def ip(a, b):
    if a == b:
        return sq[(base, a)]
    return sp.Rational(1, 2)*(sq[(base, a)] + sq[(base, b)] - sq[(a, b)])

dets = []
det_subs = list(itertools.combinations(others, 4))
for sub in det_subs:
    M = sp.Matrix(4, 4, lambda i, j: ip(sub[i], sub[j]))
    dets.append(sp.expand(M.det()))
m2subs = list(itertools.combinations(others, 2))
m3subs = list(itertools.combinations(others, 3))
ineqs = []
for sub in m2subs:
    M = sp.Matrix(2, 2, lambda i, j: ip(sub[i], sub[j]))
    ineqs.append(sp.expand(M.det()))
for sub in m3subs:
    M = sp.Matrix(3, 3, lambda i, j: ip(sub[i], sub[j]))
    ineqs.append(sp.expand(M.det()))
LAMDEG = 1 if target.startswith('class') else 2
IS_CLASSLIKE = target.startswith('class')
n = len(vars_)
print(f'{target}: {n} vars, {len(dets)} dets, base {base}', flush=True)
lo = [sp.Integer(1)]*n
hi = [sp.Integer(4)]*n

m2all, m3all = list(m2subs), list(m3subs)
m2ineqs = ineqs[:len(m2all)]
m3ineqs = ineqs[len(m2all):]
if IS_CLASSLIKE:
    configs = [([], [], []), (m2ineqs, m2all, []),
               (m2ineqs + m3ineqs, m2all, m3all)]
else:
    configs = [(m2ineqs + m3ineqs, m2all, m3all)]
num = None
for cfg_ineqs, cfg_m2, cfg_m3 in configs:
    gs = GramSystem(vars_, dets, lamdeg=LAMDEG, sosdeg=1, ineqs=cfg_ineqs)
    eps_ladder = (0.0,) if IS_CLASSLIKE else (1e-3, 1e-4, 0.0)
    for eps_ in eps_ladder:
        num = gs.solve_box(lo, hi, eps=eps_) if eps_ > 0 else gs.solve_box(lo, hi)
        if num is not None:
            break
    if num is not None:
        ineqs, m2subs, m3subs = cfg_ineqs, cfg_m2, cfg_m3
        print(f'SDP stage 1: {num["status"]} '
              f'(m2={len(cfg_m2)}, m3={len(cfg_m3)})', flush=True)
        break
assert num is not None, 'SDP infeasible in all configs'
# stage 2: accuracy-restoring masked re-solve (small system, CLARABEL-friendly)
norms1 = [float(np.linalg.norm(np.array(Q))) for Q in num['Q']]
_done2 = False
for mth in (1e-1, 3e-2, 1e-2, 1e-3):
    mask = [t for t, nm in enumerate(norms1) if nm > mth]
    for eps2 in (1e-3, 3e-4, 1e-4):
        num2 = gs.solve_box(lo, hi, mask=mask, eps=eps2)
        if num2 is not None and num2['status'] == 'optimal':
            num = num2
            print(f'SDP stage 2: optimal on {len(mask)} blocks '
                  f'(thresh {mth}, eps {eps2})', flush=True)
            _done2 = True
            break
    if _done2:
        break
if not _done2:
    print('SDP stage 2: keeping stage-1 solution', flush=True)

# ---------------- round + residual ----------------
mults = gs.mult_list(lo, hi)
def attempt(bits):
    D = 2**bits
    def rnd(x):
        return sp.Rational(int(round(float(x)*D)), D)
    lamr = [[rnd(num['lam'][i*len(gs.lam_basis)+t])
             for t in range(len(gs.lam_basis))] for i in range(len(dets))]
    forms = {}   # block t -> list of (d_k rational > 0, coeff vector rational)
    for t in range(len(mults)):
        Q = num['Q'][t]
        if np.linalg.norm(Q) < 1e-6:
            continue
        Qs = (Q + Q.T) / 2
        w, Vv = np.linalg.eigh(Qs)
        fl = []
        wmax = float(np.max(w)) if len(w) else 0.0
        for k in range(len(w)):
            if w[k] < 1e-6:
                continue
            dk = rnd(w[k])
            vec = [rnd(Vv[a, k]) for a in range(gs.nb)]
            if dk > 0 and any(x != 0 for x in vec):
                fl.append((dk, vec))
        if fl:
            forms[t] = fl
    Eres = sp.Integer(1)
    for i, det in enumerate(gs.dets):
        lp = sum(c*b for c, b in zip(lamr[i], gs.lam_basis))
        Eres += sp.expand(lp*det)
    for t, fl in forms.items():
        quad = sp.Integer(0)
        for dk, vec in fl:
            lin = sum(c*b for c, b in zip(vec, gs.sos_basis))
            quad += dk * lin**2
        Eres += sp.expand(mults[t]*sp.expand(quad))
    Eres = sp.expand(Eres)
    P = sp.Poly(Eres, *vars_)
    B = sp.Integer(0)
    for exp, c in P.terms():
        B += c * 4**sum(exp) if c > 0 else c
    return lamr, forms, Eres, P, B

for bits in (BITS, BITS+4, BITS+8):
    lamr, forms, Eres, P, B = attempt(bits)
    print(f'bits={bits}: E support {len(P.terms())}, B = {float(B):.4f}', flush=True)
    if B < sp.Rational(1, 2):
        break
assert B < 1, f'residual bound too large: {float(B)}'

ldls = forms
print(f'{len(ldls)} form blocks', flush=True)

# ---------------- Lean printing helpers ----------------
sys.set_int_max_str_digits(2000000)
def rat_lean(q):
    q = sp.Rational(q)
    if q.q == 1:
        return f'({q.p} : ℝ)'
    return f'(({q.p} : ℝ) / {q.q})'

def poly_lean(expr):
    expr = sp.expand(expr)
    Pp = sp.Poly(expr, *vars_)
    terms = []
    for exp, c in Pp.terms():
        c = sp.Rational(c)
        parts = []
        for v, e in zip(vars_, exp):
            if e == 1:
                parts.append(str(v))
            elif e >= 2:
                parts.append(f'{v} ^ {e}')
        if not parts:
            terms.append(rat_lean(c))
        elif c == 1:
            terms.append(' * '.join(parts))
        elif c == -1:
            terms.append('-' + ' * '.join(parts))
        else:
            terms.append(rat_lean(c) + ' * ' + ' * '.join(parts))
    if not terms:
        return '(0 : ℝ)'
    s = terms[0]
    for t in terms[1:]:
        s += (' + ' + t) if not t.startswith('-') else (' - ' + t[1:])
    return s

def mono_lean(exp):
    parts = []
    for v, e in zip(vars_, exp):
        if e == 1:
            parts.append(str(v))
        elif e >= 2:
            parts.append(f'{v} ^ {e}')
    return ' * '.join(parts)

# metas aligned with mults
metas = [('one', sp.Integer(1), 'one', None)]
for v in vars_:
    metas.append((f'hlo_{v}', v - 1, 'lo', v))
    metas.append((f'hhi_{v}', 4 - v, 'hi', v))
for si, sub in enumerate(m2subs):
    metas.append((f'hm2_{si}', ineqs[si], 'm2', sub))
for si, sub in enumerate(m3subs):
    metas.append((f'hm3_{si}', ineqs[len(m2subs)+si], 'm3', sub))
used_mults = sorted(ldls.keys())
used_dets = [i for i in range(len(dets)) if any(c != 0 for c in lamr[i])]

# ---------------- scalar lemma (split declarations) ----------------
S = []
args = ' '.join(str(v) for v in vars_)
det_hyps = [f'(hd{i} : {poly_lean(dets[i])} = 0)' for i in used_dets]
bound_hyps = []
for t in used_mults:
    if t == 0:
        continue
    name, expr, kind, info = metas[t]
    bound_hyps.append((t, f'({name} : 0 ≤ {poly_lean(expr)})'))
box_hyps = [h for (t, h) in bound_hyps if metas[t][2] in ('lo', 'hi')]
box_names = [metas[t][0] for (t, h) in bound_hyps if metas[t][2] in ('lo', 'hi')]
# need ALL box bounds for Eb regardless of block usage
all_box_hyps = []
all_box_names = []
for v in vars_:
    all_box_hyps.append(f'(hlo_{v} : 0 ≤ {poly_lean(v - 1)})')
    all_box_names.append(f'hlo_{v}')
    all_box_hyps.append(f'(hhi_{v} : 0 ≤ {poly_lean(4 - v)})')
    all_box_names.append(f'hhi_{v}')

# sigma expression pieces
sos_parts = []
block_info = []
for t in used_mults:
    forms = ldls[t]
    inner = ' + '.join(
        f'{rat_lean(dd)} * ({poly_lean(sum(cc*b for cc, b in zip(col, gs.sos_basis)))}) ^ 2'
        for dd, col in forms)
    if t == 0:
        sos_parts.append(f'({inner})')
        block_info.append((t, None, inner))
    else:
        mexpr = poly_lean(metas[t][1])
        sos_parts.append(f'({mexpr}) * ({inner})')
        block_info.append((t, mexpr, inner))
sos_expr = ' + '.join(sos_parts)

# 1. key
S.append(f'private lemma {scalar_name}_key ({args} : ℝ)')
for h in det_hyps:
    S.append(f'    {h}')
S.append(f'    : {sos_expr} = -1 + ({poly_lean(Eres)}) := by')
lam_parts = []
for i in used_dets:
    lp = sp.expand(-sum(c*b for c, b in zip(lamr[i], gs.lam_basis)))
    lam_parts.append(f'({poly_lean(lp)}) * hd{i}')
S.append(f'  linear_combination {" + ".join(lam_parts)}')
S.append('')

# 2. pos
S.append(f'private lemma {scalar_name}_pos ({args} : ℝ)')
for (t, h) in bound_hyps:
    S.append(f'    {h}')
S.append(f'    : (0:ℝ) ≤ {sos_expr} := by')
pidx = 0
for (t, mexpr, inner) in block_info:
    if mexpr is None:
        S.append(f'  have t{pidx} : (0:ℝ) ≤ ({inner}) := by positivity')
    else:
        S.append(f'  have u{pidx} : (0:ℝ) ≤ ({inner}) := by positivity')
        S.append(f'  have t{pidx} : (0:ℝ) ≤ ({mexpr}) * ({inner}) := '
                 f'mul_nonneg {metas[t][0]} u{pidx}')
    pidx += 1
S.append('  linarith only [' + ', '.join(f't{i}' for i in range(pidx)) + ']')
S.append('')

# 3. Eb
S.append(f'private lemma {scalar_name}_Eb ({args} : ℝ)')
for h in all_box_hyps:
    S.append(f'    {h}')
S.append(f'    : ({poly_lean(Eres)}) ≤ {rat_lean(B)} := by')
for v in vars_:
    S.append(f'  have hv1_{v} : (1:ℝ) ≤ {v} := by linarith [hlo_{v}]')
    S.append(f'  have hv4_{v} : {v} ≤ (4:ℝ) := by linarith [hhi_{v}]')
bound_names = []
for j, (exp, c) in enumerate(P.terms()):
    dtot = sum(exp)
    if dtot == 0:
        bound_names.append((None, c))
        continue
    factors = []
    for v, e in zip(vars_, exp):
        factors.extend([v]*e)
    ml = mono_lean(exp)
    if dtot == 1:
        f0 = factors[0]
        if c > 0:
            S.append(f'  have hb{j} : ({ml}:ℝ) ≤ 4 := hv4_{f0}')
        else:
            S.append(f'  have hb{j} : (1:ℝ) ≤ {ml} := hv1_{f0}')
        bound_names.append((f'hb{j}', c))
        continue
    S.append(f'  have hc{j}_0 : (1:ℝ) ≤ {factors[0]} ∧ ({factors[0]}:ℝ) ≤ 4 := '
             f'⟨hv1_{factors[0]}, hv4_{factors[0]}⟩')
    prev = f'hc{j}_0'
    chain = f'{factors[0]}'
    bnd = '(4:ℝ)'
    for st, f in enumerate(factors[1:], start=1):
        S.append(f'  have hc{j}_{st} := mono_step hv1_{f} hv4_{f} '
                 f'{prev}.1 {prev}.2')
        prev = f'hc{j}_{st}'
        chain = f'{f} * ({chain})'
        bnd = f'4 * ({bnd})'
    if c > 0:
        S.append(f'  have hb{j} : ({ml}:ℝ) ≤ {4**dtot} := by')
        S.append(f'    calc ({ml}:ℝ) = {chain} := by ring')
        S.append(f'      _ ≤ {bnd} := {prev}.2')
        S.append(f'      _ = {4**dtot} := by norm_num')
    else:
        S.append(f'  have hb{j} : (1:ℝ) ≤ {ml} := by')
        S.append(f'    calc (1:ℝ) ≤ {chain} := {prev}.1')
        S.append(f'      _ = {ml} := by ring')
    bound_names.append((f'hb{j}', c))
S.append('  linarith only [' + ', '.join(nm for nm, c in bound_names if nm) + ']')
S.append('')

# 4. glue
S.append(f'private lemma {scalar_name} ({args} : ℝ)')
for h in det_hyps:
    S.append(f'    {h}')
for v in vars_:
    S.append(f'    (hlo_{v} : 0 ≤ {poly_lean(v - 1)})')
    S.append(f'    (hhi_{v} : 0 ≤ {poly_lean(4 - v)})')
for (t, h) in bound_hyps:
    if metas[t][2] in ('m2', 'm3'):
        S.append(f'    {h}')
S.append('    : False := by')
S.append(f'  have key := {scalar_name}_key {args} '
         + ' '.join(f'hd{i}' for i in used_dets))
pos_args = []
for t in used_mults:
    if t == 0:
        continue
    pos_args.append(metas[t][0])
S.append(f'  have pos := {scalar_name}_pos {args} ' + ' '.join(pos_args))
S.append(f'  have hEb := {scalar_name}_Eb {args} ' + ' '.join(all_box_names))
S.append('  linarith only [key, pos, hEb]')
S.append('')

# ---------------- wrapper (same geometry layer as emit_obs_lean) ----------------
def two_path(a, c):
    for w in range(size):
        if w != a and w != c and adj(a, w) and adj(w, c):
            return w
    raise AssertionError(f'no 2-path for {(a, c)}')

def bond_lemma(a, b):
    x, y = min(a, b), max(a, b)
    if (a, b) == (x, y):
        return f'h{x}{y}'
    return f'(by rw [dist_comm]; exact h{x}{y})'

W = []
W.append(f'/-- {title} of the `E_min(9)` programme is impossible in a hard-core')
W.append('configuration. Machine-generated wrapper over a slack-absorbed rational')
W.append('SOS certificate (`scratch-h4/gen_slack.py`). -/')
W.append(f'theorem {lean_name} {{X : Finset E3}} (hX : HardCore X)')
W.append(f'    {{q : Fin {size} → E3}} (hq : ∀ i, q i ∈ X) '
         f'(hinj : Function.Injective q)')
for (a, b) in sorted(Eset):
    W.append(f'    (h{a}{b} : dist (q {a}) (q {b}) = 1)')
W.append('    : False := by')
W.append(f'  set y : Fin {size} → E3 := fun i => q i - q {base} with hy')
W.append('  have hsep : ∀ i j, i ≠ j → (1:ℝ) ≤ dist (q i) (q j) ^ 2 := by')
W.append('    intro i j hne')
W.append('    have hd := hX (q i) (hq i) (q j) (hq j) (fun h => hne (hinj h))')
W.append('    nlinarith [dist_nonneg (x := q i) (y := q j)]')
W.append('  have hipgen : ∀ i j, (inner ℝ (y i) (y j) : ℝ)')
W.append('      = (‖y i‖ ^ 2 + ‖y j‖ ^ 2 - dist (q i) (q j) ^ 2) / 2 := by')
W.append('    intro i j')
W.append('    have hkey := norm_sub_sq_real (y i) (y j)')
W.append('    rw [show y i - y j = q i - q j by simp only [hy]; abel, '
         '← dist_eq_norm] at hkey')
W.append('    linarith')
W.append(f'  have hnrm : ∀ i, ‖y i‖ = dist (q i) (q {base}) := by')
W.append('    intro i')
W.append('    simp only [hy]')
W.append('    rw [← dist_eq_norm]')
for v in others:
    if adj(base, v):
        W.append(f'  have hn{v} : ‖y {v}‖ = 1 := by')
        W.append('    rw [hnrm]')
        if v < base:
            W.append(f'    exact h{v}{base}')
        else:
            W.append(f'    rw [dist_comm]; exact h{base}{v}')
for v in vars_:
    s = str(v)
    a, b = int(s[1]), int(s[2])
    W.append(f'  set {s} : ℝ := dist (q {a}) (q {b}) ^ 2 with h{s}def')
for v in vars_:
    s = str(v)
    a, b = int(s[1]), int(s[2])
    W.append(f'  have hlo_{s} : 0 ≤ {poly_lean(v - 1)} := by')
    W.append(f'    have hs := hsep {a} {b} (by decide)')
    W.append(f'    rw [h{s}def]')
    W.append('    linarith')
    w = two_path(a, b)
    W.append(f'  have hhi_{s} : 0 ≤ {poly_lean(4 - v)} := by')
    W.append(f'    have htri := dist_triangle (q {a}) (q {w}) (q {b})')
    W.append(f'    have hb1 : dist (q {a}) (q {w}) = 1 := {bond_lemma(a, w)}')
    W.append(f'    have hb2 : dist (q {w}) (q {b}) = 1 := {bond_lemma(w, b)}')
    W.append(f'    rw [h{s}def]')
    W.append(f'    nlinarith [dist_nonneg (x := q {a}) (y := q {b})]')
for v in others:
    if adj(base, v):
        W.append(f'  have hs{v} : (inner ℝ (y {v}) (y {v}) : ℝ) = 1 := by')
        W.append(f'    rw [real_inner_self_eq_norm_sq, hn{v}]; norm_num')
    else:
        a, b = min(base, v), max(base, v)
        W.append(f'  have hs{v} : (inner ℝ (y {v}) (y {v}) : ℝ) = s{a}{b} := by')
        if v > base:
            W.append(f'    rw [real_inner_self_eq_norm_sq, hnrm, '
                     f'dist_comm (q {v}) (q {base}), hs{a}{b}def]')
        else:
            W.append(f'    rw [real_inner_self_eq_norm_sq, hnrm, hs{a}{b}def]')
for i, j in itertools.combinations(others, 2):
    val = sp.expand(ip(i, j))
    vs = poly_lean(val)
    W.append(f'  have e{i}{j} : (inner ℝ (y {i}) (y {j}) : ℝ) = {vs} := by')
    steps = ['hipgen']
    for t_ in (i, j):
        if adj(base, t_):
            steps.append(f'hn{t_}')
        else:
            steps.append(f'hnrm {t_}')
            if t_ > base:
                steps.append(f'dist_comm (q {t_}) (q {base})')
    if adj(i, j):
        steps.append(f'h{i}{j}')
    W.append(f'    rw [{", ".join(steps)}]')
    defs = sorted({str(x) for x in val.free_symbols})
    if not adj(i, j):
        defs = sorted(set(defs) | {f's{i}{j}'})
    if defs:
        W.append(f'    rw [{", ".join(f"h{s_}def" for s_ in defs)}]')
    W.append('    ring')
    W.append(f'  have e{j}{i} : (inner ℝ (y {j}) (y {i}) : ℝ) = {vs} := by')
    W.append(f'    rw [real_inner_comm]; exact e{i}{j}')
ipd = {}
for i_ in others:
    ipd[(i_, i_)] = f'hs{i_}'
for i_, j_ in itertools.permutations(others, 2):
    ipd[(i_, j_)] = f'e{i_}{j_}'
for di in used_dets:
    sub = det_subs[di]
    vecs = ', '.join(f'y {v}' for v in sub)
    rewrites = list(dict.fromkeys(ipd[(a, b)] for a in sub for b in sub))
    W.append(f'  have hd{di} : {poly_lean(dets[di])} = 0 := by')
    W.append(f'    have hd := gram_det_zero ![{vecs}]')
    W.append('    rw [det_fin_four] at hd')
    W.append('    simp only [Matrix.of_apply, Matrix.cons_val_zero, '
             'Matrix.cons_val_one,')
    W.append('      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, '
             'Matrix.cons_val_three] at hd')
    W.append(f'    rw [{", ".join(rewrites)}] at hd')
    W.append('    linear_combination hd')
for t in used_mults:
    name, expr, kind, info = metas[t]
    if kind == 'm2':
        i_, j_ = info
        W.append(f'  have {name} : 0 ≤ {poly_lean(expr)} := by')
        W.append(f'    have hcs := gram2_det_nonneg (y {i_}) (y {j_})')
        W.append(f'    rw [{ipd[(i_,i_)]}, {ipd[(j_,j_)]}, {ipd[(i_,j_)]}, '
                 f'{ipd[(j_,i_)]}] at hcs')
        W.append('    convert hcs using 1')
        W.append('    ring')
    elif kind == 'm3':
        vecs = ', '.join(f'y {v}' for v in info)
        rewrites = list(dict.fromkeys(ipd[(a, b)] for a in info for b in info))
        W.append(f'  have {name} : 0 ≤ {poly_lean(expr)} := by')
        W.append(f'    have hg := gram3_det_nonneg ![{vecs}]')
        W.append('    rw [Matrix.det_fin_three] at hg')
        W.append('    simp only [Matrix.of_apply, Matrix.cons_val_zero, '
                 'Matrix.cons_val_one,')
        W.append('      Matrix.head_cons, Matrix.cons_val_two, '
                 'Matrix.tail_cons] at hg')
        W.append(f'    rw [{", ".join(rewrites)}] at hg')
        W.append('    convert hg using 1')
        W.append('    ring')
call_args = [str(v) for v in vars_]
hyps = [f'hd{i}' for i in used_dets]
for v in vars_:
    hyps.append(f'hlo_{v}')
    hyps.append(f'hhi_{v}')
for t in used_mults:
    if t != 0 and metas[t][2] in ('m2', 'm3'):
        hyps.append(metas[t][0])
W.append(f'  exact {scalar_name} {" ".join(call_args)} {" ".join(hyps)}')

out = []
out.append('import Physics.Emin9Kills')
out.append('')
out.append('set_option linter.style.header false')
out.append('set_option linter.unusedSimpArgs false')
out.append('set_option maxHeartbeats 16000000')
out.append('set_option maxRecDepth 100000')
out.append('')
out.append(f'/-! # Slack-absorbed SOS kill lemma: {title} -/')
out.append('')
out.append('namespace Kissing3D')
out.append('')
out.extend(S)
out.append('')
out.extend(W)
out.append('')
out.append('end Kissing3D')
open(out_path, 'w').write('\n'.join(out) + '\n')
print('wrote', out_path, f'({len(out)} lines, {len(used_dets)} dets, '
      f'{len(used_mults)} blocks, B={float(B):.4f})', flush=True)
