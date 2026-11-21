from collections import deque
from math import ceil, log2

# ==============================================================================
# DISCRETE MATHEMATICS (UBA04) - ASSIGNMENT 3 (CO3)
# Graph Models, Matrix Representations, Isomorphism, Connectivity & Distances
# ==============================================================================


def bfs_distances(adj, start):
    dist = {start: 0}
    q = deque([start])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist


def is_bipartite(adj):
    color = {}
    for s in adj:
        if s not in color:
            color[s] = 0
            q = deque([s])
            while q:
                u = q.popleft()
                for v in adj[u]:
                    if v not in color:
                        color[v] = 1 - color[u]
                        q.append(v)
                    elif color[v] == color[u]:
                        return False
    return True


def is_connected(adj, excluded=None):
    excluded = excluded or set()
    verts = [v for v in adj if v not in excluded]
    if not verts:
        return True
    seen = {verts[0]}
    q = deque([verts[0]])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in excluded and v not in seen:
                seen.add(v)
                q.append(v)
    return len(seen) == len(verts)


# ------------------------------------------------------------------------------
# TASK 1: Graph Terminology and Special Graphs (Data-Centre Topology Selection)
# ------------------------------------------------------------------------------
def task1_data_centre_topologies():
    print("=== ASSIGNMENT 3 - TASK 1 ===")
    topologies = {}

    # C8
    c8 = {i: {(i - 1) % 8, (i + 1) % 8} for i in range(8)}
    topologies["C8"] = c8

    # K1,7
    k17 = {i: set() for i in range(8)}
    for i in range(1, 8):
        k17[0].add(i)
        k17[i].add(0)
    topologies["K1,7"] = k17

    # W8 (hub 0 connected to 7-cycle 1..7)
    w8 = {i: set() for i in range(8)}
    for idx in range(7):
        u, v = idx + 1, ((idx + 1) % 7) + 1
        w8[u].add(v)
        w8[v].add(u)
        w8[0].add(u)
        w8[u].add(0)
    topologies["W8"] = w8

    # K8
    k8 = {i: set(range(8)) - {i} for i in range(8)}
    topologies["K8"] = k8

    # Q3
    q3 = {i: {i ^ (1 << b) for b in range(3)} for i in range(8)}
    topologies["Q3"] = q3

    for name, adj in topologies.items():
        edges = sum(len(nbrs) for nbrs in adj.values()) // 2
        deg_seq = sorted((len(nbrs) for nbrs in adj.values()), reverse=True)
        handshaking_ok = sum(deg_seq) == 2 * edges
        diam = max(max(bfs_distances(adj, v).values()) for v in adj)
        bip = is_bipartite(adj)
        two_connected = all(is_connected(adj, {v}) for v in adj)
        qualifies = (edges <= 12) and (diam <= 3) and two_connected
        print(
            f"{name:5s} | |E|={edges:2d} | deg={deg_seq} | Handshake={handshaking_ok} | "
            f"diam={diam} | Bipartite={str(bip):5s} | 2-conn={str(two_connected):5s} | "
            f"Qualifies={qualifies}"
        )
    print()


# ------------------------------------------------------------------------------
# TASK 2: Representing Graphs (Adjacency & Incidence Matrices of Sensor Mesh)
# ------------------------------------------------------------------------------
def task2_matrices_and_walks():
    print("=== ASSIGNMENT 3 - TASK 2 ===")
    n = 6
    edges = [
        (0, 1), (0, 2), (1, 2), (1, 3),
        (2, 3), (3, 4), (3, 5), (4, 5),
    ]
    m = len(edges)

    A = [[0] * n for _ in range(n)]
    B = [[0] * m for _ in range(n)]
    for e_idx, (u, v) in enumerate(edges):
        A[u][v] = A[v][u] = 1
        B[u][e_idx] = B[v][e_idx] = 1

    D = [[sum(A[i]) if i == j else 0 for j in range(n)] for i in range(n)]
    BBT = [
        [sum(B[i][k] * B[j][k] for k in range(m)) for j in range(n)]
        for i in range(n)
    ]
    A_plus_D = [[A[i][j] + D[i][j] for j in range(n)] for i in range(n)]

    print(f"(a) Column sums of B all equal 2: {all(sum(B[i][k] for i in range(n)) == 2 for k in range(m))}")
    print(f"(a) B @ B^T == A + D: {BBT == A_plus_D}")

    def matmul(X, Y):
        return [
            [sum(X[i][k] * Y[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)
        ]

    A2 = matmul(A, A)
    A3 = matmul(A2, A)
    triangles = sum(A3[i][i] for i in range(n)) // 6
    print(f"(b) 2-hop routes v1->v4 (A^2[0][3]): {A2[0][3]}")
    print(f"(b) 3-hop routes v1->v4 (A^3[0][3]): {A3[0][3]}")
    print(f"(b) Triangles tr(A^3)/6: {triangles}")

    # (c) Smart-city storage comparison
    N_nodes, avg_deg = 10_000, 6
    matrix_bits = N_nodes ** 2
    list_bits = N_nodes * avg_deg * ceil(log2(N_nodes))
    print(
        f"(c) Storage for n={N_nodes}, deg={avg_deg}: "
        f"Adjacency Matrix = {matrix_bits:,} bits ({matrix_bits / 8e6:.2f} MB), "
        f"Adjacency List = {list_bits:,} bits ({list_bits / 8e3:.2f} KB)\n"
    )


# ------------------------------------------------------------------------------
# TASK 3: Graph Isomorphism (Verifying and Refuting Topology Equivalence)
# ------------------------------------------------------------------------------
def task3_graph_isomorphism():
    print("=== ASSIGNMENT 3 - TASK 3 ===")
    # (a) Topology X (Q3) vs Topology Y (Mobius ladder M8)
    X = {i: {i ^ (1 << b) for b in range(3)} for i in range(8)}
    Y = {i: {(i - 1) % 8, (i + 1) % 8, (i + 4) % 8} for i in range(8)}
    same_fp = (
        len(X) == len(Y)
        and sum(len(v) for v in X.values()) == sum(len(v) for v in Y.values())
        and sorted(len(v) for v in X.values()) == sorted(len(v) for v in Y.values())
    )
    print(f"(a) X and Y share fingerprint: {same_fp}")
    print(f"    X bipartite: {is_bipartite(X)}, Y bipartite: {is_bipartite(Y)} -> X ~= Y: False")

    # (b) Isomorphism phi: G1 -> G2 (K3,3)
    verts_1 = ["a", "b", "c", "d", "e", "f"]
    edges_1 = [
        ("a", "b"), ("b", "c"), ("c", "d"), ("d", "e"), ("e", "f"), ("f", "a"),
        ("a", "d"), ("b", "e"), ("c", "f"),
    ]
    verts_2 = [1, 2, 3, 4, 5, 6]
    edges_2 = {(u, v) for u in [1, 2, 3] for v in [4, 5, 6]} | {
        (v, u) for u in [1, 2, 3] for v in [4, 5, 6]
    }

    phi = {"a": 1, "c": 2, "e": 3, "b": 4, "d": 5, "f": 6}
    edge_preserved = all((phi[u], phi[v]) in edges_2 for u, v in edges_1)

    A1 = [[int((u, v) in edges_1 or (v, u) in edges_1) for v in verts_1] for u in verts_1]
    A2 = [[int((u, v) in edges_2) for v in verts_2] for u in verts_2]
    inv_phi = {v: k for k, v in phi.items()}
    idx1 = {v: i for i, v in enumerate(verts_1)}
    A1_permuted = [
        [A1[idx1[inv_phi[u]]][idx1[inv_phi[v]]] for v in verts_2]
        for u in verts_2
    ]
    print(f"(b) Edge-by-edge isomorphism phi verified: {edge_preserved}")
    print(f"    Rearranged A1 == A2: {A1_permuted == A2}")

    # (c) Self-complementary C5
    C5_edges = {(i, (i + 1) % 5) for i in range(5)} | {((i + 1) % 5, i) for i in range(5)}
    C5_comp_edges = {
        (u, v) for u in range(5) for v in range(5) if u != v and (u, v) not in C5_edges
    }
    psi = {i: (2 * i) % 5 for i in range(5)}
    c5_self_comp = all((psi[u], psi[v]) in C5_comp_edges for u, v in C5_edges)
    print(f"(c) C5 self-complementary via i -> 2i mod 5: {c5_self_comp}")
    print(f"    n=6 required edges = 6*5/4 = {6 * 5 / 4} (not integer -> impossible)\n")


# ------------------------------------------------------------------------------
# TASK 4: Connectivity (Cut Vertices, Bridges and One-Way Road Networks)
# ------------------------------------------------------------------------------
def task4_connectivity():
    print("=== ASSIGNMENT 3 - TASK 4 ===")
    # (a) Campus network N
    edges_N = [
        (1, 2), (2, 3), (3, 1),
        (3, 4),
        (4, 5), (5, 6), (6, 7), (7, 4),
        (6, 8),
        (8, 9), (9, 10), (10, 8),
    ]
    adj_N = {i: set() for i in range(1, 11)}
    for u, v in edges_N:
        adj_N[u].add(v)
        adj_N[v].add(u)

    def count_components(adj, excl_v=None, excl_e=None):
        excl_v = excl_v or set()
        excl_e = excl_e or set()
        seen = set()
        comps = 0
        for v in adj:
            if v not in excl_v and v not in seen:
                comps += 1
                q = deque([v])
                seen.add(v)
                while q:
                    curr = q.popleft()
                    for nxt in adj[curr]:
                        if nxt not in excl_v and nxt not in seen:
                            if (curr, nxt) not in excl_e and (nxt, curr) not in excl_e:
                                seen.add(nxt)
                                q.append(nxt)
        return comps

    cut_vertices = {
        v: count_components(adj_N, excl_v={v})
        for v in adj_N
        if count_components(adj_N, excl_v={v}) > 1
    }
    bridges = [
        e for e in edges_N if count_components(adj_N, excl_e={e}) > 1
    ]
    print(f"(a) Cut vertices (vertex: components): {cut_vertices}")
    print(f"    Bridges: {bridges}, kappa(N) = 1, lambda(N) = 1")

    # (b) Directed one-way street network D (Strongly Connected Components)
    arcs_D = [(1, 2), (2, 3), (3, 1), (3, 4), (4, 5), (5, 6), (6, 4)]
    verts_D = [1, 2, 3, 4, 5, 6]
    adj_D = {v: [] for v in verts_D}
    rev_D = {v: [] for v in verts_D}
    for u, v in arcs_D:
        adj_D[u].append(v)
        rev_D[v].append(u)

    visited, order = set(), []

    def dfs1(u):
        visited.add(u)
        for v in adj_D[u]:
            if v not in visited:
                dfs1(v)
        order.append(u)

    for v in verts_D:
        if v not in visited:
            dfs1(v)

    visited.clear()
    sccs = []

    def dfs2(u, comp):
        visited.add(u)
        comp.append(u)
        for v in rev_D[u]:
            if v not in visited:
                dfs2(v, comp)

    for v in reversed(order):
        if v not in visited:
            comp = []
            dfs2(v, comp)
            sccs.append(sorted(comp))

    print(f"(b) Strongly connected components of D: {sccs}")
    print("    Strongly connected: False (weakly connected only); Min arcs to add: 1 (e.g., 4 -> 1)")

    # (c) Eliminating bridges in N
    adj_N_19 = {k: set(v) for k, v in adj_N.items()}
    adj_N_19[1].add(9)
    adj_N_19[9].add(1)
    edges_N_19 = edges_N + [(1, 9)]
    bridges_after_19 = [
        e for e in edges_N_19 if count_components(adj_N_19, excl_e={e}) > 1
    ]
    cut_after_19 = [
        v for v in adj_N_19 if count_components(adj_N_19, excl_v={v}) > 1
    ]

    adj_N_57 = {k: set(v) for k, v in adj_N.items()}
    adj_N_57[5].add(7)
    adj_N_57[7].add(5)
    edges_N_57 = edges_N + [(5, 7)]
    bridges_after_57 = [
        e for e in edges_N_57 if count_components(adj_N_57, excl_e={e}) > 1
    ]
    print(f"(c) After adding link (1, 9): bridges = {bridges_after_19}, cut vertices = {cut_after_19}")
    print(f"    After adding link (5, 7): remaining bridges = {bridges_after_57}\n")


# ------------------------------------------------------------------------------
# TASK 5: Distance and Eccentricity (Server Placement in a Tree Network)
# ------------------------------------------------------------------------------
def task5_tree_distances():
    print("=== ASSIGNMENT 3 - TASK 5 ===")
    edges_T = [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (2, 7), (2, 8), (2, 9)]
    adj_T = {i: set() for i in range(1, 10)}
    for u, v in edges_T:
        adj_T[u].add(v)
        adj_T[v].add(u)

    ecc = {}
    sigma = {}
    for v in range(1, 10):
        dists = bfs_distances(adj_T, v)
        ecc[v] = max(dists.values())
        sigma[v] = sum(dists.values())

    radius = min(ecc.values())
    diameter = max(ecc.values())
    centre = [v for v, e in ecc.items() if e == radius]
    min_sigma = min(sigma.values())
    median = [v for v, s in sigma.items() if s == min_sigma]

    print(f"(a) Eccentricities: {ecc}")
    print(f"    Radius = {radius}, Diameter = {diameter}, Centre = {centre}")
    print(f"(b) Total distances sigma(v): {sigma}")
    print(f"    Median = {median} (sigma = {min_sigma}) vs Centre = {centre} (sigma = {sigma[centre[0]]})")

    sla_compliant = [v for v in range(1, 10) if ecc[v] <= 3]
    best_sla_node = min(sla_compliant, key=lambda v: sigma[v])
    extra_hops = sigma[best_sla_node] - min_sigma
    print(f"(c) SLA (ecc <= 3) compliant nodes: {sla_compliant}")
    print(f"    Best SLA placement: node {best_sla_node} (ecc={ecc[best_sla_node]}, sigma={sigma[best_sla_node]}), "
          f"extra total hops vs median = {extra_hops}")


if __name__ == "__main__":
    task1_data_centre_topologies()
    task2_matrices_and_walks()
    task3_graph_isomorphism()
    task4_connectivity()
    task5_tree_distances()
