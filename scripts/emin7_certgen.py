#!/usr/bin/env python3
"""Generate kill certificates for all 20349 five-edge complements of K7,
in Lean's (List.range 21).sublistsLen 5 order, packed as base-8 Nats.

Certificate kinds (field order little-endian after the kind digit):
  0 K5      : a,b,c,d,e            -- five pairwise-adjacent vertices
  1 ringdeg : u,v,c,x,y,z          -- edge uv; c,x,y,z common nbrs; c adj x,y,z; x,y,z distinct
  2 ringC3  : u,v,x,y,z            -- edge uv; x,y,z common nbrs pairwise adjacent
  3 ringC4  : u,v,w,x,y,z          -- edge uv; cycle w-x-y-z among common nbrs; w!=y, x!=z
  4 ringC5  : u,v,z1,z2,z3,z4,z5   -- edge uv; 5-cycle among common nbrs; z1!=z3, z1!=z4
  5 triple  : a,b,c,w1,w2,w3       -- a,b,c distinct; w1,w2,w3 distinct common nbrs of all three
"""
from itertools import combinations, permutations

PAIRS = list(combinations(range(7), 2))
IDX = {p: k for k, p in enumerate(PAIRS)}

def pair_idx(i, j):
    return IDX[(i, j) if i < j else (j, i)]

def mk_adj(removed):
    rs = set(removed)
    def adj(i, j):
        return i != j and i < 7 and j < 7 and pair_idx(i, j) not in rs
    return adj

def pack(kind, fields):
    n = 0
    for f in reversed(fields):
        n = n * 8 + f
    return n * 8 + kind

# --- checkers (must mirror Lean killcheck exactly) ---
def check(removed, cert):
    adj = mk_adj(removed)
    kind, rest = cert % 8, cert // 8
    f = []
    while rest:
        f.append(rest % 8); rest //= 8
    def g(k):
        return f[k] if k < len(f) else 0
    if kind == 0:
        vs = [g(i) for i in range(5)]
        return all(adj(vs[i], vs[j]) for i in range(5) for j in range(i + 1, 5))
    if kind == 1:
        u, v, c, x, y, z = (g(i) for i in range(6))
        return (adj(u, v)
                and all(adj(u, t) and adj(v, t) for t in (c, x, y, z))
                and adj(c, x) and adj(c, y) and adj(c, z)
                and x != y and x != z and y != z)
    if kind == 2:
        u, v, x, y, z = (g(i) for i in range(5))
        return (adj(u, v)
                and all(adj(u, t) and adj(v, t) for t in (x, y, z))
                and adj(x, y) and adj(x, z) and adj(y, z))
    if kind == 3:
        u, v, w, x, y, z = (g(i) for i in range(6))
        return (adj(u, v)
                and all(adj(u, t) and adj(v, t) for t in (w, x, y, z))
                and adj(w, x) and adj(x, y) and adj(y, z) and adj(z, w)
                and w != y and x != z)
    if kind == 4:
        u, v, z1, z2, z3, z4, z5 = (g(i) for i in range(7))
        return (adj(u, v)
                and all(adj(u, t) and adj(v, t) for t in (z1, z2, z3, z4, z5))
                and adj(z1, z2) and adj(z2, z3) and adj(z3, z4) and adj(z4, z5)
                and adj(z5, z1) and z1 != z3 and z1 != z4)
    if kind == 5:
        a, b, c, w1, w2, w3 = (g(i) for i in range(6))
        return (a != b and a != c and b != c
                and w1 != w2 and w1 != w3 and w2 != w3
                and all(adj(t, w) for t in (a, b, c) for w in (w1, w2, w3)))
    return False

# --- searchers ---
def find_cert(removed):
    adj = mk_adj(removed)
    # K5
    for c5 in combinations(range(7), 5):
        if all(adj(a, b) for a, b in combinations(c5, 2)):
            return pack(0, list(c5))
    # ring degree
    for (u, v) in PAIRS:
        if not adj(u, v):
            continue
        common = [w for w in range(7) if adj(u, w) and adj(v, w)]
        for c in common:
            nb = [t for t in common if adj(c, t)]
            if len(nb) >= 3:
                return pack(1, [u, v, c, nb[0], nb[1], nb[2]])
    # ring C3
    for (u, v) in PAIRS:
        if not adj(u, v):
            continue
        common = [w for w in range(7) if adj(u, w) and adj(v, w)]
        for x, y, z in combinations(common, 3):
            if adj(x, y) and adj(x, z) and adj(y, z):
                return pack(2, [u, v, x, y, z])
    # ring C4
    for (u, v) in PAIRS:
        if not adj(u, v):
            continue
        common = [t for t in range(7) if adj(u, t) and adj(v, t)]
        for quad in combinations(common, 4):
            for perm in permutations(quad):
                w, x, y, z = perm
                if adj(w, x) and adj(x, y) and adj(y, z) and adj(z, w):
                    return pack(3, [u, v, w, x, y, z])
    # ring C5
    for (u, v) in PAIRS:
        if not adj(u, v):
            continue
        common = [t for t in range(7) if adj(u, t) and adj(v, t)]
        if len(common) == 5:
            for perm in permutations(common):
                z1, z2, z3, z4, z5 = perm
                if (adj(z1, z2) and adj(z2, z3) and adj(z3, z4) and adj(z4, z5)
                        and adj(z5, z1)):
                    return pack(4, [u, v, z1, z2, z3, z4, z5])
    # triple
    for a, b, c in combinations(range(7), 3):
        common = [w for w in range(7) if adj(a, w) and adj(b, w) and adj(c, w)]
        if len(common) >= 3:
            return pack(5, [a, b, c, common[0], common[1], common[2]])
    return None

def main():
    scratch = "/tmp/claude-1000/-home-marek-Documents-Lean/2fb3f9c4-f11c-4629-ae2e-03bf909fa416/scratchpad"
    combos = []
    with open(f"{scratch}/combos.txt") as fh:
        for line in fh:
            combos.append([int(t) for t in line.split()])
    assert len(combos) == 20349
    certs = []
    stats = {}
    for removed in combos:
        cert = find_cert(removed)
        assert cert is not None, f"no certificate for {removed}"
        assert check(removed, cert), f"self-check failed for {removed} cert {cert}"
        stats[cert % 8] = stats.get(cert % 8, 0) + 1
        certs.append(cert)
    print("kind counts:", dict(sorted(stats.items())))
    print("max cert:", max(certs))
    # emit Lean file
    lines = ["/-! Machine-generated: kill certificates for the 20349 five-edge",
             "complements of `K7`, aligned with `(List.range 21).sublistsLen 5`.",
             "Generated by scratch-h4/emin7_certgen.py -- do not edit. -/",
             "",
             "namespace Kissing3D",
             "",
             "/-- Packed base-8 kill certificates, one per five-edge complement. -/",
             "def emin7Certs : List Nat := ["]
    row = []
    for k, cert in enumerate(certs):
        row.append(str(cert))
        if len(row) == 12:
            sep = "," if k < len(certs) - 1 else ""
            lines.append("  " + ", ".join(row) + sep)
            row = []
    if row:
        lines.append("  " + ", ".join(row))
    lines.append("]")
    lines.append("")
    lines.append("end Kissing3D")
    with open("/home/marek/Documents/Lean/physics/Physics/Emin7Cert.lean", "w") as fh:
        fh.write("\n".join(lines) + "\n")
    print("wrote Physics/Emin7Cert.lean")

if __name__ == "__main__":
    main()
