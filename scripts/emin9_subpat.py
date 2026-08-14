#!/usr/bin/env python3
"""Sub-pattern analysis of the 52 NEW N=9 survivor classes.

For each class (full decision on 9 vertices: edges = exact unit distance,
nonedges = dist >= 1), scan induced sub-patterns on subsets of size 5..8 for
numerical infeasibility (LSQ). Cache feasibility by iso class of the induced
graph so shared sub-patterns across classes are tested once. Finally, dedupe
the minimal infeasible sub-patterns up to isomorphism and greedily cover all
52 classes with as few obstruction classes as possible.
"""
import pickle, itertools, numpy as np, networkx as nx
from scipy.optimize import least_squares

newclasses = pickle.load(open("scratch-h4/emin9_newclasses.pkl", "rb"))
print("new classes:", len(newclasses), flush=True)

def feasible_resid(edges, nons, n, tries=25, seed=1):
    rng = np.random.default_rng(seed)
    best = np.inf
    for _ in range(tries):
        x0 = rng.normal(size=3 * n)
        def res(x):
            P = x.reshape(n, 3)
            r = [np.dot(P[i] - P[j], P[i] - P[j]) - 1.0 for i, j in edges]
            for i, j in nons:
                d2 = np.dot(P[i] - P[j], P[i] - P[j])
                r.append(min(0.0, d2 - 1.0) * 3.0)
            return np.array(r)
        s = least_squares(res, x0, method="trf", max_nfev=4000)
        best = min(best, float(np.sum(s.fun ** 2)))
        if best < 1e-18:
            break
    return best

# cache of feasibility by iso class of the induced (edge) graph
# key: (n, wl_hash) -> list of (Graph, residual)
cache = {}
cache_hits = 0

def induced_feasible(E, n):
    global cache_hits
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
    key = (n, nx.weisfeiler_lehman_graph_hash(G, iterations=3))
    for (H, r) in cache.setdefault(key, []):
        if nx.is_isomorphic(G, H):
            cache_hits += 1
            return r, G
    N = [p for p in itertools.combinations(range(n), 2) if p not in set(E)
         and (p[1], p[0]) not in set(E)]
    r = feasible_resid(E, N, n)
    cache[key].append((G, r))
    return r, G

# per class: find minimal infeasible induced sub-patterns
class_kills = []   # per class: (size, [rep Graph, ...]) at the first killing size
for ci, (degs, members, nonedges) in enumerate(newclasses):
    ns = set(nonedges) | set((b, a) for a, b in nonedges)
    alledges = [p for p in itertools.combinations(range(9), 2) if p not in ns]
    killed = None
    for size in (5, 6, 7, 8):
        found = []
        for sub in itertools.combinations(range(9), size):
            idx = {v: k for k, v in enumerate(sub)}
            E = [(idx[i], idx[j]) for i, j in alledges if i in idx and j in idx]
            r, G = induced_feasible(E, size)
            if r > 1e-6:
                found.append((sub, r, G))
        if found:
            killed = (size, found)
            break
    if killed is None:
        print(f"class {ci}: degs={degs} members={members} -- NO infeasible "
              f"sub-pattern up to size 8 (full 9-pattern only)", flush=True)
        class_kills.append((ci, None, []))
    else:
        size, found = killed
        print(f"class {ci}: degs={degs} members={members} -- killed at size "
              f"{size}, {len(found)} subsets", flush=True)
        class_kills.append((ci, size, found))

print("cache hits:", cache_hits, "distinct tested:",
      sum(len(v) for v in cache.values()), flush=True)

# dedupe infeasible sub-patterns across classes up to isomorphism
obstructions = []   # list of (Graph, size, set of class indices it kills, resid)
for ci, size, found in class_kills:
    for sub, r, G in found:
        for k, (H, hs, kills, hr) in enumerate(obstructions):
            if hs == size and nx.is_isomorphic(G, H):
                kills.add(ci)
                break
        else:
            obstructions.append((G, size, {ci}, r))
print(f"distinct infeasible sub-pattern classes: {len(obstructions)}", flush=True)

# greedy cover of all killed classes
killed_classes = set(ci for ci, size, f in class_kills if size is not None)
cover = []
remaining = set(killed_classes)
obs_sorted = sorted(range(len(obstructions)),
                    key=lambda k: -len(obstructions[k][2]))
while remaining:
    best = max(range(len(obstructions)),
               key=lambda k: len(obstructions[k][2] & remaining))
    gain = obstructions[best][2] & remaining
    if not gain:
        break
    cover.append(best)
    remaining -= gain
print(f"greedy cover: {len(cover)} obstructions cover "
      f"{len(killed_classes) - len(remaining)}/{len(killed_classes)} classes",
      flush=True)
for k in cover:
    G, size, kills, r = obstructions[k]
    degs = sorted(d for _, d in G.degree())
    print(f"  obstruction size={size} degseq={degs} kills {len(kills)} classes "
          f"resid={r:.2e}", flush=True)
    print(f"    edges: {sorted(G.edges())}", flush=True)

pickle.dump(
    {"class_kills": [(ci, size, [(sub, r, sorted(G.edges())) for sub, r, G in f])
                     for ci, size, f in class_kills],
     "obstructions": [(sorted(G.edges()), size, sorted(kills), r)
                      for G, size, kills, r in obstructions],
     "cover": cover},
    open("scratch-h4/emin9_subpat.pkl", "wb"))
print("done", flush=True)
