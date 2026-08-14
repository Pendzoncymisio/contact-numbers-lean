#!/usr/bin/env python3
"""Build the E_min(8) kill decision tree.

Pairs of Fin 8 in a fixed order (vertex-major). DFS: at each node the next pair is
decided edge / non-edge. A subtree dies as soon as a monotone kill applies to the
partial assignment:
  - mindeg : some vertex has >= 4 decided non-edges  (kill: seven_particle_bound)
  - nonedge10 : >= 10 decided non-edges              (kill: bonds >= 19 impossible)
  - K5 / ring-deg / ring-cycle(C3,C4,C5) / common6 / triple / P1 / P4 / P5 on the
    decided edges (monotone: only needs edges)
Certificates are found at kill time and stored at leaves. Measures tree size first.
"""
from itertools import combinations
import sys
sys.setrecursionlimit(100000)

V = list(range(8))
PAIRS = [(i, j) for i in V for j in V if i < j]
# vertex-major order: (0,1),(0,2),...,(0,7),(1,2),...
NP = len(PAIRS)

import networkx as nx
P1E = [(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),
       (0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(2,3),(2,4),(3,4)]
P4E = [(6,0),(6,1),(6,2),(6,3),(6,4),(6,5),
       (0,1),(0,4),(0,5),(1,2),(1,3),(2,3),(2,5),(3,4),(4,5)]
P5E = [(6,1),(6,2),(6,3),(6,4),(6,5),
       (0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(2,3),(2,5),(3,4)]
PGRAPHS = [(nx.Graph(P1E), "P1"), (nx.Graph(P4E), "P4"), (nx.Graph(P5E), "P5")]

nodes = 0
leaves = 0
kills = {}

def find_kill(edges, nonedges, adj, nedeg):
    # mindeg
    for v in V:
        if nedeg[v] >= 4:
            return ("mindeg", v)
    if len(nonedges) >= 10:
        return ("ne10",)
    # K5
    for c5 in combinations(V, 5):
        if all(adj[a][b] for a, b in combinations(c5, 2)):
            return ("K5", c5)
    # rings
    for (u, v) in edges:
        common = [w for w in V if w != u and w != v and adj[u][w] and adj[v][w]]
        if len(common) >= 6:
            return ("common6", u, v)
        deg = {w: 0 for w in common}
        es = []
        for a, b in combinations(common, 2):
            if adj[a][b]:
                deg[a] += 1; deg[b] += 1; es.append((a, b))
        for w in common:
            if deg[w] > 2:
                return ("ringdeg", u, v, w)
        parent = {w: w for w in common}
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]; x = parent[x]
            return x
        for a, b in es:
            ra, rb = find(a), find(b)
            if ra == rb:
                return ("ringcyc", u, v)
            parent[ra] = rb
    # triple
    for a, b, c in combinations(V, 3):
        cnt = [w for w in V if w not in (a, b, c) and adj[a][w] and adj[b][w] and adj[c][w]]
        if len(cnt) > 2:
            return ("triple", a, b, c)
    # P patterns (only worth checking when enough edges)
    if len(edges) >= 14:
        G = nx.Graph(); G.add_nodes_from(V); G.add_edges_from(edges)
        for P, name in PGRAPHS:
            gm = nx.algorithms.isomorphism.GraphMatcher(G, P)
            if gm.subgraph_is_monomorphic():
                return (name,)
    return None

def dfs(k, edges, nonedges, adj, nedeg, depth):
    global nodes, leaves
    nodes += 1
    kill = find_kill(edges, nonedges, adj, nedeg)
    if kill is not None:
        leaves += 1
        kills[kill[0]] = kills.get(kill[0], 0) + 1
        return
    if k == NP:
        raise AssertionError(f"undead full pattern! edges={edges}")
    (a, b) = PAIRS[k]
    # edge branch
    adj[a][b] = adj[b][a] = True
    edges.append((a, b))
    dfs(k + 1, edges, nonedges, adj, nedeg, depth + 1)
    edges.pop()
    adj[a][b] = adj[b][a] = False
    # non-edge branch
    nonedges.append((a, b))
    nedeg[a] += 1; nedeg[b] += 1
    dfs(k + 1, edges, nonedges, adj, nedeg, depth + 1)
    nedeg[a] -= 1; nedeg[b] -= 1
    nonedges.pop()

def main():
    adj = [[False] * 8 for _ in range(8)]
    nedeg = [0] * 8
    dfs(0, [], [], adj, nedeg, 0)
    print("nodes:", nodes, "leaves:", leaves)
    print("kill distribution:", kills)

if __name__ == "__main__":
    main()
