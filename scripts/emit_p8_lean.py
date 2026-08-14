#!/usr/bin/env python3
"""Emit Physics/Emin9Q{k}.lean from a slack certificate produced by
p8_direct.py (scratch-h4/p8cert_p8_{k}.pkl). Split-declaration template.
Usage: emit_p8_lean.py <k>"""
import sys, pickle, itertools
sys.set_int_max_str_digits(2000000)
import sympy as sp
sys.path.insert(0, 'scratch-h4')
from sos_lib import monomials

k = int(sys.argv[1])
cert = pickle.load(open(f'scratch-h4/p8cert_p8_{k}.pkl', 'rb'))
pats = pickle.load(open('scratch-h4/emin9_pat8.pkl', 'rb'))
E_, resid, ks = pats[k]
Eset = set(tuple(e) for e in E_)
size = 8
base = cert['base']
others = [v for v in range(size) if v != base]
def adj(a, b): return (min(a, b), max(a, b)) in Eset

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
assert [str(v) for v in vars_] == cert['vars']

dets = []
det_subs = list(itertools.combinations(others, 4))
for sub in det_subs:
    dets.append(sp.expand(sp.Matrix(4, 4, lambda i, j: ip(sub[i], sub[j])).det()))
m2subs = list(itertools.combinations(others, 2))
m3subs = list(itertools.combinations(others, 3))
m2 = [sp.expand(sp.Matrix(2, 2, lambda i, j: ip(sub[i], sub[j])).det())
      for sub in m2subs]
m3 = [sp.expand(sp.Matrix(3, 3, lambda i, j: ip(sub[i], sub[j])).det())
      for sub in m3subs]
use_m3 = (cert['ineqs'] == 'm2m3')
ineqs = m2 + (m3 if use_m3 else [])
lamr = cert['lamr']
forms = cert['forms']
Eres = cert['E']
B = cert['B']
lam_basis = monomials(vars_, 2)
sos_basis = monomials(vars_, len(next(iter(forms.values()))[0][1]) and 1)
# sos basis length check
nb = len(next(iter(forms.values()))[0][1])
for dcand in (1, 2):
    if len(monomials(vars_, dcand)) == nb:
        sos_basis = monomials(vars_, dcand)
        break

def rat_lean(q):
    q = sp.Rational(q)
    if q.q == 1:
        return f'({q.p} : ℝ)'
    return f'(({q.p} : ℝ) / {q.q})'

def poly_lean(expr):
    expr = sp.expand(expr)
    P = sp.Poly(expr, *vars_)
    terms = []
    for exp, c in P.terms():
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

metas = [('one', sp.Integer(1), 'one', None)]
for v in vars_:
    metas.append((f'hlo_{v}', v - 1, 'lo', v))
    metas.append((f'hhi_{v}', 4 - v, 'hi', v))
for si, sub in enumerate(m2subs):
    metas.append((f'hm2_{si}', m2[si], 'm2', sub))
if use_m3:
    for si, sub in enumerate(m3subs):
        metas.append((f'hm3_{si}', m3[si], 'm3', sub))

used_dets = [i for i in range(len(dets)) if any(sp.Rational(c) != 0 for c in lamr[i])]
used_mults = sorted(forms.keys())
scalar_name = f'q{k}_scalar'
lean_name = f'pattern_q{k}_impossible'

P = sp.Poly(Eres, *vars_)
S = []
args = ' '.join(str(v) for v in vars_)
det_hyps = [f'(hd{i} : {poly_lean(dets[i])} = 0)' for i in used_dets]
bound_hyps = []
for t in used_mults:
    if t == 0:
        continue
    name, expr, kind_, info = metas[t]
    bound_hyps.append((t, f'({name} : 0 ≤ {poly_lean(expr)})'))
all_box_hyps = []
all_box_names = []
for v in vars_:
    all_box_hyps.append(f'(hlo_{v} : 0 ≤ {poly_lean(v - 1)})')
    all_box_names.append(f'hlo_{v}')
    all_box_hyps.append(f'(hhi_{v} : 0 ≤ {poly_lean(4 - v)})')
    all_box_names.append(f'hhi_{v}')

sos_parts = []
block_info = []
for t in used_mults:
    fl = forms[t]
    inner = ' + '.join(
        f'{rat_lean(dd)} * ({poly_lean(sum(sp.Rational(c)*b for c, b in zip(vec, sos_basis)))}) ^ 2'
        for dd, vec in fl)
    if t == 0:
        sos_parts.append(f'({inner})')
        block_info.append((t, None, inner))
    else:
        mexpr = poly_lean(metas[t][1])
        sos_parts.append(f'({mexpr}) * ({inner})')
        block_info.append((t, mexpr, inner))
sos_expr = ' + '.join(sos_parts)

S.append(f'private lemma {scalar_name}_key ({args} : ℝ)')
for h in det_hyps:
    S.append(f'    {h}')
S.append(f'    : {sos_expr} = -1 + ({poly_lean(Eres)}) := by')
lam_parts = []
for i in used_dets:
    lp = sp.expand(-sum(sp.Rational(c)*b for c, b in zip(lamr[i], lam_basis)))
    lam_parts.append(f'({poly_lean(lp)}) * hd{i}')
S.append(f'  linear_combination {" + ".join(lam_parts)}')
S.append('')
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
S.append(f'private lemma {scalar_name} ({args} : ℝ)')
for h in det_hyps:
    S.append(f'    {h}')
for h in all_box_hyps:
    S.append(f'    {h}')
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
W.append(f'/-- 8-point pattern `q{k}` (kills classes {sorted(ks)}) is impossible in a')
W.append('hard-core configuration. Machine-generated slack-SOS wrapper')
W.append('(`scratch-h4/emit_p8_lean.py`). -/')
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
    W.append(f'  have hlo_{s} : 0 ≤ {poly_lean(sp.Symbol(s, real=True) - 1)} := by')
    W.append(f'    have hs := hsep {a} {b} (by decide)')
    W.append(f'    rw [h{s}def]')
    W.append('    linarith')
    w = two_path(a, b)
    W.append(f'  have hhi_{s} : 0 ≤ {poly_lean(4 - sp.Symbol(s, real=True))} := by')
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
    if t == 0:
        continue
    name, expr, kind_, info = metas[t]
    if kind_ == 'm2':
        i_, j_ = info
        W.append(f'  have {name} : 0 ≤ {poly_lean(expr)} := by')
        W.append(f'    have hcs := gram2_det_nonneg (y {i_}) (y {j_})')
        W.append(f'    rw [{ipd[(i_,i_)]}, {ipd[(j_,j_)]}, {ipd[(i_,j_)]}, '
                 f'{ipd[(j_,i_)]}] at hcs')
        W.append('    convert hcs using 1')
        W.append('    ring')
    elif kind_ == 'm3':
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
out.append(f'/-! # Slack-SOS kill lemma: 8-point pattern q{k} -/')
out.append('')
out.append('namespace Kissing3D')
out.append('')
out.extend(S)
out.append('')
out.extend(W)
out.append('')
out.append('end Kissing3D')
path = f'/home/marek/Documents/Lean/physics/Physics/Emin9Q{k}.lean'
open(path, 'w').write('\n'.join(out) + '\n')
print('wrote', path, f'({len(out)} lines, {len(used_dets)} dets, '
      f'{len(used_mults)} blocks, B={float(B):.4f})')
