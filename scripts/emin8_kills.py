#!/usr/bin/env python3
"""E_min(8) kill lemmas: exact algebra for the three 7-point obstruction patterns.

Monotone semantics throughout: pattern edges are exact bonds (inner 1/2 after
recentring on the cone vertex), all other pairs have inner <= 1/2 (hard core).
Rank <= 3 (vectors in R^3) => every 4x4 Gram determinant vanishes.

P1 (kills survivor classes 0,1,2): cone vertex + 6-point shell, shell edges
  {(0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(2,3),(2,4),(3,4)}.
  Chain (verified below):
    det G[0,2,3,4](x02) = -(x02-1)(3x02+1)/4  = 0, x02<=1/2  => x02 = -1/3
    det G[1,2,3,4](x13) = -(x13-1)(3x13+1)/4  = 0, x13<=1/2  => x13 = -1/3
    det G[0,1,2,3](x01) = -(18x01+7)(54x01+53)/1296 = 0
    det G[0,1,2,4](x01) = -(2x01-1)(18x01+7)/48     = 0
        intersection => x01 = -7/18   (-53/54 fails the second det)
    det G[0,1,4,5](x45) = -25(x45-1)(11x45-7)/324 = 0
        roots {1, 7/11} both > 1/2  => CONTRADICTION.

P4 (kills class 3): cone vertex + prism shell
  {(0,1),(0,4),(0,5),(1,2),(1,3),(2,3),(2,5),(3,4),(4,5)}.
  The full rank system (15 quartic dets) has exactly 14 solutions, every one
  containing a value 1 or > 1/2: contradiction. A short resultant chain for
  Lean is still to be extracted (two-unknown dets, e.g. G[0,1,2,5](x02,x15)).

P5 (kills class 4): no cone vertex (degrees [3,4,4,4,4,4,5]); needs the
  difference-vector version from a degree-5 base vertex. TODO.
"""
import sympy as sp, itertools as it

def gram(E, known, xs):
    def g(i, j):
        if i == j:
            return sp.Integer(1)
        p = (min(i, j), max(i, j))
        if p in E:
            return sp.Rational(1, 2)
        return known.get(p, xs[p])
    return g

def verify_p1():
    E = {(0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(2,3),(2,4),(3,4)}
    free = [(i,j) for i,j in it.combinations(range(6),2) if (i,j) not in E]
    xs = {p: sp.Symbol(f"x{p[0]}{p[1]}") for p in free}
    known = {}
    g = gram(E, known, xs)
    def det(sub):
        return sp.factor(sp.Matrix(4,4, lambda a,b: g(sub[a],sub[b])).det())
    assert sp.simplify(det((0,2,3,4)) - (-(xs[(0,2)]-1)*(3*xs[(0,2)]+1)/4)) == 0
    known[(0,2)] = sp.Rational(-1,3)
    assert sp.simplify(det((1,2,3,4)) - (-(xs[(1,3)]-1)*(3*xs[(1,3)]+1)/4)) == 0
    known[(1,3)] = sp.Rational(-1,3)
    d1, d2 = det((0,1,2,3)), det((0,1,2,4))
    x = xs[(0,1)]
    assert sp.simplify(d1 - (-(18*x+7)*(54*x+53)/1296)) == 0
    assert sp.simplify(d2 - (-(2*x-1)*(18*x+7)/48)) == 0
    known[(0,1)] = sp.Rational(-7,18)
    d3 = det((0,1,4,5))
    y = xs[(4,5)]
    assert sp.simplify(d3 - (-25*(y-1)*(11*y-7)/324)) == 0
    print("P1 chain verified: contradiction at G[0,1,4,5], roots {1, 7/11} > 1/2")

if __name__ == "__main__":
    verify_p1()
