#!/usr/bin/env python3
"""Generate Physics/Emin9P{k}.lean for an obstruction with an exact SOS
certificate (scratch-h4/sosr_obs{k}.pkl). Single-leaf certificates only.
Usage: emit_obs_lean.py <obs_idx>"""
import sys, pickle, itertools
sys.set_int_max_str_digits(2000000)
import sympy as sp
sys.path.insert(0, 'scratch-h4')
from sos_lib import obs_system, monomials

idx = int(sys.argv[1])
cert = pickle.load(open(f'scratch-h4/sosr_obs{idx}.pkl', 'rb'))
d = pickle.load(open('scratch-h4/emin9_subpat.pkl', 'rb'))
E, size, kills, resid = d['obstructions'][idx]
Eset = set(E)
deg = {v: sum(1 for e in E if v in e) for v in range(size)}
base = max(range(size), key=lambda v: deg[v])
others = [v for v in range(size) if v != base]
vars_, dets, gs = obs_system(idx, base=None, lamdeg=2, sosdeg=1)
assert [str(v) for v in vars_] == cert['vars']

def adj(a, b):
    return (min(a, b), max(a, b)) in Eset

sq = {}
for a, b in itertools.combinations(range(size), 2):
    sq[(a, b)] = sp.Integer(1) if adj(a, b) else sp.Symbol(f's{a}{b}', real=True)
    sq[(b, a)] = sq[(a, b)]
def ip(a, b):
    if a == b:
        return sq[(base, a)]
    return sp.Rational(1, 2)*(sq[(base, a)] + sq[(base, b)] - sq[(a, b)])

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

def ldl_psd(M):
    M = sp.Matrix(M)
    nb = M.rows
    out = []
    used = [False]*nb
    for _ in range(nb):
        best, bi = 0, -1
        for i in range(nb):
            if not used[i] and M[i, i] > best:
                best, bi = M[i, i], i
        if bi < 0:
            break
        dd = M[bi, bi]
        col = [M[j, bi]/dd for j in range(nb)]
        for a in range(nb):
            for b in range(nb):
                M[a, b] -= dd*col[a]*col[b]
        used[bi] = True
        out.append((dd, col))
    assert all(x == 0 for x in M), 'not PSD in LDL'
    return out

m2subs = list(itertools.combinations(others, 2))
m3subs = list(itertools.combinations(others, 3))
det_subs = list(itertools.combinations(others, 4))
lam_basis = monomials(vars_, 2)

def mult_meta(lo, hi):
    metas = [('one', sp.Integer(1), 'one', None)]
    for kk, v in enumerate(vars_):
        metas.append((f'hlo_{v}', v - lo[kk], 'lo', v))
        metas.append((f'hhi_{v}', hi[kk] - v, 'hi', v))
    for si, sub in enumerate(m2subs):
        M = sp.Matrix(2, 2, lambda i, j: ip(sub[i], sub[j]))
        metas.append((f'hm2_{si}', sp.expand(M.det()), 'm2', sub))
    for si, sub in enumerate(m3subs):
        M = sp.Matrix(3, 3, lambda i, j: ip(sub[i], sub[j]))
        metas.append((f'hm3_{si}', sp.expand(M.det()), 'm3', sub))
    return metas

leaf = cert['leaves'][0]
assert len(cert['leaves']) == 1, 'single-leaf only'
lo, hi = leaf['lo'], leaf['hi']
assert all(sp.Rational(str(x)) == 1 for x in lo), 'expected root box'
assert all(sp.Rational(str(x)) == 4 for x in hi), 'expected root box'
metas = mult_meta([sp.Integer(1)]*len(vars_), [sp.Integer(4)]*len(vars_))
mats = [sp.Matrix(m) for m in leaf['mats']]
lam = [[sp.Rational(str(x)) for x in l] for l in leaf['lam']]
used_dets = [i for i in range(len(dets)) if any(c != 0 for c in lam[i])]
used_mults = [t for t in range(len(metas))
              if t < len(mats) and any(x != 0 for x in mats[t])]

# ---------------- scalar lemma ----------------
S = []
args = ' '.join(str(v) for v in vars_)
S.append(f'private lemma obs{idx}_scalar ({args} : ℝ)')
for i in used_dets:
    S.append(f'    (hd{i} : {poly_lean(dets[i])} = 0)')
for t in used_mults:
    if t == 0:
        continue
    name, expr, kind, info = metas[t]
    S.append(f'    ({name} : 0 ≤ {poly_lean(expr)})')
S.append('    : False := by')
sos_parts = []
pos_lines = []
pidx = 0
for t in used_mults:
    forms = ldl_psd(mats[t])
    inner = ' + '.join(
        f'{rat_lean(dd)} * ({poly_lean(sum(c*b for c, b in zip(col, gs.sos_basis)))}) ^ 2'
        for dd, col in forms)
    if t == 0:
        sos_parts.append(f'({inner})')
        pos_lines.append(f'    have t{pidx} : (0:ℝ) ≤ ({inner}) := by positivity')
    else:
        mexpr = poly_lean(metas[t][1])
        sos_parts.append(f'({mexpr}) * ({inner})')
        pos_lines.append(f'    have s{pidx} : (0:ℝ) ≤ ({inner}) := by positivity')
        pos_lines.append(f'    have t{pidx} : (0:ℝ) ≤ ({mexpr}) * ({inner}) := '
                         f'mul_nonneg {metas[t][0]} s{pidx}')
    pidx += 1
sos_expr = ' + '.join(sos_parts)
lam_parts = []
for i in used_dets:
    lp = sp.expand(-sum(c*b for c, b in zip(lam[i], lam_basis)))
    lam_parts.append(f'({poly_lean(lp)}) * hd{i}')
S.append(f'  have key : {sos_expr} = -1 := by')
S.append(f'    linear_combination {" + ".join(lam_parts)}')
S.append(f'  have pos : (0:ℝ) ≤ {sos_expr} := by')
S.extend(pos_lines)
S.append('    linarith [' + ', '.join(f't{i}' for i in range(pidx)) + ']')
S.append('  linarith')

# ---------------- wrapper ----------------
def two_path(a, c):
    for w in range(size):
        if w != a and w != c and adj(a, w) and adj(w, c):
            return w
    raise AssertionError(f'no 2-path for {(a, c)}')

def bond_lemma(a, b):
    """Lean term of type dist (q a) (q b) = 1 for an edge (a,b)."""
    x, y = min(a, b), max(a, b)
    if (a, b) == (x, y):
        return f'h{x}{y}'
    return f'(by rw [dist_comm]; exact h{x}{y})'

W = []
W.append(f'/-- Obstruction `obs{idx}` of the `E_min(9)` sub-pattern analysis is')
W.append('impossible in a hard-core configuration. Machine-generated wrapper over an')
W.append('exact rational Positivstellensatz certificate (`scratch-h4/emit_obs_lean.py`);')
W.append('the SOS identity lives in `obs' + str(idx) + '_scalar`. -/')
W.append(f'theorem pattern_obs{idx}_impossible {{X : Finset E3}} (hX : HardCore X)')
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
        W.append(f'    rw [hnrm]; exact {bond_lemma(v, base)[1:-1] if v > base else bond_lemma(v, base)}'
                 if False else
                 f'    rw [hnrm]')
        if v < base:
            W.append(f'    exact h{v}{base}')
        else:
            W.append(f'    rw [dist_comm]; exact h{base}{v}')
# set unknowns
for v in vars_:
    s = str(v)
    a, b = int(s[1]), int(s[2])
    W.append(f'  set {s} : ℝ := dist (q {a}) (q {b}) ^ 2 with h{s}def')
# self inner products
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
# cross inner products
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
# bounds
for t in used_mults:
    name, expr, kind, info = metas[t]
    if kind == 'lo':
        s = str(info)
        a, b = int(s[1]), int(s[2])
        W.append(f'  have {name} : 0 ≤ {poly_lean(expr)} := by')
        W.append(f'    have hs := hsep {a} {b} (by decide)')
        W.append(f'    rw [h{s}def]')
        W.append('    linarith')
    elif kind == 'hi':
        s = str(info)
        a, b = int(s[1]), int(s[2])
        w = two_path(a, b)
        W.append(f'  have {name} : 0 ≤ {poly_lean(expr)} := by')
        W.append(f'    have htri := dist_triangle (q {a}) (q {w}) (q {b})')
        W.append(f'    have hb1 : dist (q {a}) (q {w}) = 1 := {bond_lemma(a, w)}')
        W.append(f'    have hb2 : dist (q {w}) (q {b}) = 1 := {bond_lemma(w, b)}')
        W.append(f'    rw [h{s}def]')
        W.append(f'    nlinarith [dist_nonneg (x := q {a}) (y := q {b})]')
# entry rewrite dictionary
ipd = {}
for i_ in others:
    ipd[(i_, i_)] = f'hs{i_}'
for i_, j_ in itertools.permutations(others, 2):
    ipd[(i_, j_)] = f'e{i_}{j_}'
# det hypotheses
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
# minor hypotheses
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
# final application
call_args = [str(v) for v in vars_]
hyps = [f'hd{i}' for i in used_dets]
for t in used_mults:
    if t != 0:
        hyps.append(metas[t][0])
W.append(f'  exact obs{idx}_scalar {" ".join(call_args)} {" ".join(hyps)}')

out = []
out.append('import Physics.Emin9Kills')
out.append('')
out.append('set_option linter.style.header false')
out.append('set_option linter.unusedSimpArgs false')
out.append('set_option maxHeartbeats 3200000')
out.append('')
out.append(f'/-! # Kill lemma for obstruction `obs{idx}` '
           '(machine-generated SOS certificate) -/')
out.append('')
out.append('namespace Kissing3D')
out.append('')
out.extend(S)
out.append('')
out.extend(W)
out.append('')
out.append('end Kissing3D')
path = f'/home/marek/Documents/Lean/physics/Physics/Emin9P{idx}.lean'
open(path, 'w').write('\n'.join(out) + '\n')
print('wrote', path, f'({len(out)} lines, {len(used_dets)} dets, '
      f'{len(used_mults)} mult blocks)')
