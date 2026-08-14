# Exact contact numbers for packings of six to nine congruent balls

[![build](https://github.com/Pendzoncymisio/contact-numbers-lean/actions/workflows/build.yml/badge.svg)](https://github.com/Pendzoncymisio/contact-numbers-lean/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21935524.svg)](https://doi.org/10.5281/zenodo.21935524)

A Lean 4 formalization of

> **c(6,3) = 12, c(7,3) = 15, c(8,3) = 18, c(9,3) = 21,**

where `c(n,3)` is the maximum number of touching pairs in a packing of `n` congruent
balls in Euclidean 3-space, together with the fact that every packing attaining these
values is *minimally rigid*.

Bezdek and Khan ([*Contact numbers for sphere packings*][bk], Bolyai Soc. Math. Studies
**27**, Springer 2018, 25–48) state that "the contact number c(n, 3) is still unknown
for n ≥ 6", record `c(n,3) = 3n − 6` for `n = 6,…,9` as their Conjecture 5.2, and prove
it as their Proposition 5.1 only *conditionally* on the completeness of a numerical
enumeration. That hypothesis is removed here. Since Conjecture 5.2 asserts a value only
for `n = 6,…,9`, its numerical half is settled completely, and its structural half at
every `n` for which it makes a numerical claim.

[bk]: https://arxiv.org/abs/1601.00145

## The statements

```lean
theorem contactNumber_nine : IsGreatest (realised 9) 21

theorem conjecture52_nine :
    IsGreatest (realised 9) 21 ∧
    ∀ X : Finset E3, HardCore X → X.card = 9 → contacts X = 21 → MinimallyRigid X
```

where

```lean
abbrev E3 := EuclideanSpace ℝ (Fin 3)

def HardCore (X : Finset E3) : Prop :=          -- balls of radius 1/2, disjoint interiors
  ∀ z ∈ X, ∀ w ∈ X, z ≠ w → 1 ≤ dist z w

noncomputable def neighbors (X : Finset E3) (z : E3) : Finset E3 :=
  X.filter (fun w => dist z w = 1)              -- the balls touching z

noncomputable def contacts (X : Finset E3) : ℕ  -- the number of touching pairs

def realised (n : ℕ) : Set ℕ :=                 -- contact numbers achieved by n balls
  {k | ∃ X : Finset E3, HardCore X ∧ X.card = n ∧ contacts X = k}

def MinimallyRigid (X : Finset E3) : Prop :=    -- Bezdek–Khan, Definition 1
  (∀ v ∈ X, 3 ≤ (neighbors X v).card) ∧ 3 * X.card - 6 ≤ contacts X
```

`IsGreatest (realised n) c` is `mathlib`'s "`c` is the maximum of that set", i.e.
exactly `c(n,3) = c`. The quantification is over *all* finite subsets of ℝ³ with
pairwise distances at least one: no genericity, boundedness, or rigidity is assumed.

## Where things are

| Result | Declaration | File |
|---|---|---|
| `c(6,3) = 12` | `ContactNumbers.contactNumber_six` | `Interface.lean:55` |
| `c(7,3) = 15` | `ContactNumbers.contactNumber_seven` | `Interface.lean:60` |
| `c(8,3) = 18` | `ContactNumbers.contactNumber_eight` | `Interface.lean:65` |
| `c(9,3) = 21` | `ContactNumbers.contactNumber_nine` | `Interface.lean:70` |
| Conjecture 5.2 at `n = 6…9` | `ContactNumbers.conjecture52_six` … `_nine` | `Interface.lean:85–106` |
| upper bound, `n = 7` | `Kissing3D.seven_particle_bound` | `Emin7.lean:400` |
| upper bound, `n = 8` | `Kissing3D.eight_particle_bound` | `Emin8Final.lean:560` |
| upper bound, `n = 9` | `Kissing3D.nine_particle_bound` | `Emin9Final.lean:209` |
| minimum degree three | `Kissing3D.minDegree_six` … `_nine` | `MinDegree.lean` |
| local geometry | `ring_no_triangle`, `ring_no_square`, `ring_degree_le_two`, … | `Contact3.lean` |
| shell obstructions | `pattern_p1_impossible`, `_p4_`, `_p5_` | `Emin8Kills.lean` |
| interval branch-and-prune | `IBP.ibpWalk`, `ibpWalk_impossible` | `IntervalBP.lean` |

## Building

Requires [`elan`](https://github.com/leanprover/elan); the toolchain
(`leanprover/lean4:v4.32.0`) is pinned in `lean-toolchain` and the dependency
revisions in `lake-manifest.json`. The only dependency is `mathlib`
(rev `81a5d257c8e410db227a6665ed08f64fea08e997`).

```sh
lake exe cache get     # prebuilt mathlib oleans
lake build
```

On four cores of an AMD Ryzen 7 5700G a full build takes about five hours, dominated by
the serialized search trees and the Positivstellensatz witnesses; `Emin9Q10.lean` alone
takes roughly ninety minutes. This is longer than the six-hour ceiling on a single
GitHub-hosted job once that machine's slower cores are accounted for, so CI builds in
three chained stages that pass `.lake/build` along through the cache, with the trust-base
check at the end of the last one.

## Checking what is assumed

```sh
lake env lean Axioms.lean
```

Every theorem must report

```
[propext, Classical.choice, Quot.sound]
```

— Lean's three standard axioms and nothing else. In particular there is no `sorry`, no
user-declared axiom, and no `native_decide`, which would delegate evaluation to compiled
code and show up here as `Lean.ofReduceBool`. Every finite check is performed by the
Lean kernel itself (`decide +kernel`). `Axioms.lean` also prints the full statements and
the definitions they are built from.

## Machine-generated content

Of 60 modules and 50,810 lines, **44 modules and 41,463 lines (12.7 MB) are
machine-emitted** — the certificates for `n = 7` (`Emin7Cert.lean`), the serialized
search trees for `n = 8` and `n = 9` (`Emin8Tree*`, `Emin9TreeC*`, `Emin9Q*Tree*`), the
Positivstellensatz witnesses (`Emin9P*`, `Emin9Q*`), and the tree recompositions
(`Emin8Final`, `Emin9Final`). These are data and mechanically produced terms, not
hand-written proofs.

The generators that produced them are in `scripts/`, and are **not part of the trust
base** — see `scripts/README.md`. A bug in a generator can only produce a certificate
that the kernel rejects; it cannot produce a false theorem.

The hand-written mathematics is the other 16 modules, 9,347 lines: `Basic`, `Frame`,
`Contact3` (the local geometry), `GroundStates3`, `Emin7`, `Emin8`, `Emin9` (the
reductions and their soundness proofs), `Emin8Kills`, `Emin9Kills`, `Emin9Canon`,
`Bipyramid7`, `Cap8`, `Cap9` (the constructions), `IntervalBP`, `MinDegree` and
`Interface`. There are 4,445 kernel evaluation sites (`decide +kernel`).

## Provenance and naming

This development grew out of a study of the energy minimisation of hard spheres, and
some names still carry that origin: the namespace is `Kissing3D`, the modules for each
case are `Emin7`, `Emin8`, `Emin9` (for *energy minimum*), and the underlying quantity
is

```lean
noncomputable def energy (X : Finset E3) : ℝ := -(contactCount X : ℝ) / 2
```

with `contactCount` counting *ordered* touching pairs. So `energy X = −contacts X`, and
a ground state of `n` particles is a maximum-contact packing of `n` balls.
`Interface.lean` restates everything in contact-number language, and it is those
statements that the paper and `Axioms.lean` refer to.

The core files keep their original names rather than being renamed, so that they stay
close to the development they were extracted from. The only edits applied during
extraction are mechanical: deprecated tactics and lemmas updated for the pinned mathlib
(`push_neg` to `push Not`, `Fin.coe_cast` to `Fin.val_cast`, `mul_le_mul_right'` to
`mul_le_mul_left`), unused `simp` arguments dropped, unused binders underscored, and one
local variable renamed off a deprecated global. None of these touches a statement, and
the build is warning-free.

## What is not proved

- **Uniqueness of the maximisers.** The maximum is attained by the configurations given
  here; they are not shown to be the only ones.
- **Minimal rigidity for general `n`.** Conjecture 5.2 asserts it for every `n ≥ 6`.
  It is proved here at `n = 6,…,9`. No finite computation can reach the general case,
  because `c(n,3)` is unknown for every `n ≥ 10`.
- **Rigidity.** "Minimally rigid" is a counting condition; Bezdek and Khan note it is
  neither sufficient nor necessary for rigidity.
- **`n ≥ 10`.** In particular `c(10,3)`, where the pattern `3n − 6` is believed to break
  with `c(10,3) = 25`, is untouched.

## Paper

`paper/` contains the accompanying preprint (`build.sh`, pdflatex).

## Citing

Archived at [doi:10.5281/zenodo.21935524](https://doi.org/10.5281/zenodo.21935524)
(concept DOI — always resolves to the current version). See `CITATION.cff`.

## Licence

Apache-2.0, matching `mathlib`.
