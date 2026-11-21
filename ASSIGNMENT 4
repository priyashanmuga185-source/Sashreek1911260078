from collections import defaultdict, deque
from itertools import product

# ==============================================================================
# DISCRETE MATHEMATICS (UBA04) - ASSIGNMENT 4 (CO4)
# Euler Trails/Circuits, De Bruijn Graphs, Hamilton Cycles, Gray Codes
# ==============================================================================


# ------------------------------------------------------------------------------
# TASK 1: Euler Trails and Circuits (Fibre-Link Inspection of Campus Network)
# ------------------------------------------------------------------------------
def task1_euler_fleury():
    print("=== ASSIGNMENT 4 - TASK 1 ===")
    edges = [
        ("A", "B"), ("A", "C"), ("B", "C"), ("B", "D"),
        ("C", "D"), ("C", "E"), ("D", "E"), ("D", "F"), ("E", "F"),
    ]
    adj = defaultdict(list)
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    degrees = {v: len(adj[v]) for v in sorted(adj)}
    odd_vertices = [v for v, d in degrees.items() if d % 2 == 1]
    print(f"(a) Vertex degrees: {degrees}")
    print(f"    Odd-degree vertices: {odd_vertices} -> Open Euler trail exists (start B, end E)")

    # (b) Fleury's Algorithm with bridge detection
    rem_edges = [tuple(sorted(e)) for e in edges]

    def reachable_count(start, edge_list):
        g = defaultdict(list)
        for u, v in edge_list:
            g[u].append(v)
            g[v].append(u)
        seen = {start}
        q = deque([start])
        while q:
            curr = q.popleft()
            for nxt in g[curr]:
                if nxt not in seen:
                    seen.add(nxt)
                    q.append(nxt)
        return len(seen)

    def is_bridge(u, v, edge_list):
        before = reachable_count(u, edge_list)
        reduced = edge_list[:]
        reduced.remove(tuple(sorted((u, v))))
        after = reachable_count(u, reduced)
        return after < before

    curr = "B"
    trail = [curr]
    print("(b) Fleury's Algorithm trace:")
    while rem_edges:
        incident = [
            v for u, v in rem_edges if u == curr
        ] + [
            u for u, v in rem_edges if v == curr
        ]
        incident.sort()
        non_bridges = [nxt for nxt in incident if not is_bridge(curr, nxt, rem_edges)]
        bridges = [nxt for nxt in incident if is_bridge(curr, nxt, rem_edges)]
        chosen = non_bridges[0] if non_bridges else incident[0]
        print(f"    At {curr}: incident={incident}, bridges={bridges} -> choose {curr}-{chosen}")
        rem_edges.remove(tuple(sorted((curr, chosen))))
        curr = chosen
        trail.append(curr)

    print(f"    Euler trail: {' -> '.join(trail)}")

    # (c) Parity effect of adding BE vs AF
    deg_be = degrees.copy()
    deg_be["B"] += 1
    deg_be["E"] += 1
    deg_af = degrees.copy()
    deg_af["A"] += 1
    deg_af["F"] += 1
    print(f"(c) Add edge B-E -> odd vertices: {[v for v, d in deg_be.items() if d % 2]} (Euler circuit exists)")
    print(f"    Add edge A-F -> odd vertices: {[v for v, d in deg_af.items() if d % 2]} (Neither trail nor circuit)\n")


# ------------------------------------------------------------------------------
# TASK 2: Directed Euler Circuits (De Bruijn Sequences for Self-Test Generators)
# ------------------------------------------------------------------------------
def task2_debruijn_sequences():
    print("=== ASSIGNMENT 4 - TASK 2 ===")
    vertices = ["".join(bits) for bits in product("01", repeat=2)]
    edges = []
    adj = defaultdict(list)
    in_deg = defaultdict(int)
    out_deg = defaultdict(int)

    for b1, b2, b3 in product("01", repeat=3):
        u, v, label = b1 + b2, b2 + b3, b1 + b2 + b3
        edges.append((u, v, label))
        adj[u].append((v, label))
        out_deg[u] += 1
        in_deg[v] += 1

    balanced = all(in_deg[v] == out_deg[v] == 2 for v in vertices)
    print(f"(a) 8 directed edges: {[(u, v, lbl) for u, v, lbl in edges]}")
    print(f"    All vertices have in-deg == out-deg == 2: {balanced}")

    # (b) Hierholzer's algorithm starting at '00'
    work_adj = {u: sorted(adj[u], reverse=True) for u in vertices}
    stack = [("00", None)]
    circuit_edges = []
    while stack:
        u, incoming_lbl = stack[-1]
        if work_adj[u]:
            v, lbl = work_adj[u].pop()
            stack.append((v, lbl))
        else:
            stack.pop()
            if incoming_lbl is not None:
                circuit_edges.append(incoming_lbl)
    circuit_edges.reverse()

    cyclic_str = "".join(lbl[0] for lbl in circuit_edges)
    windows = [
        (cyclic_str * 2)[i : i + 3] for i in range(len(cyclic_str))
    ]
    print(f"(b) Directed Euler circuit edge labels: {circuit_edges}")
    print(f"    Cyclic 8-bit De Bruijn sequence: {cyclic_str}")
    print(f"    Unique 3-bit cyclic windows ({len(set(windows))}/8): {sorted(set(windows))}")

    # (c) 4-bit keypad lock (B(2, 4))
    num_codes = 2 ** 4
    linear_len = num_codes + 4 - 1
    separate_len = num_codes * 4
    print(f"(c) 4-bit keypad lock: cyclic De Bruijn length = {num_codes}, "
          f"linear keypresses = {linear_len} (vs {separate_len} separate attempts)\n")


# ------------------------------------------------------------------------------
# TASK 3: Hamilton Circuits (Sufficient Conditions for Drone Tours)
# ------------------------------------------------------------------------------
def task3_hamilton_drone_tours():
    print("=== ASSIGNMENT 4 - TASK 3 ===")
    verts = ["v1", "v2", "v3", "v4", "v5", "v6"]
    edges = [
        ("v1", "v2"), ("v1", "v3"), ("v2", "v4"), ("v2", "v5"), ("v2", "v6"),
        ("v3", "v4"), ("v3", "v5"), ("v3", "v6"), ("v4", "v5"), ("v4", "v6"), ("v5", "v6"),
    ]
    adj = {v: set() for v in verts}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)

    n = len(verts)
    degrees = {v: len(adj[v]) for v in verts}

    # (a) Dirac's theorem: deg(v) >= n/2 for all v
    dirac_holds = all(d >= n / 2 for d in degrees.values())
    print(f"(a) Degrees: {degrees}, n/2 = {n / 2} -> Dirac's condition holds: {dirac_holds} (inconclusive)")

    # (b) Ore's theorem: deg(u) + deg(v) >= n for all non-adjacent u, v
    non_adj = [
        (verts[i], verts[j], degrees[verts[i]] + degrees[verts[j]])
        for i in range(n)
        for j in range(i + 1, n)
        if verts[j] not in adj[verts[i]]
    ]
    ore_holds = all(s >= n for _, _, s in non_adj)
    print(f"(b) Non-adjacent pairs and degree sums: {non_adj}")
    print(f"    Ore's condition (sum >= {n}) holds: {ore_holds}")

    # Find explicit Hamilton cycle via backtracking
    def find_ham_cycle(path):
        if len(path) == n:
            return path + [path[0]] if path[0] in adj[path[-1]] else None
        for nxt in sorted(adj[path[-1]]):
            if nxt not in path:
                res = find_ham_cycle(path + [nxt])
                if res:
                    return res
        return None

    ham_cycle = find_ham_cycle(["v1"])
    print(f"    Verified Hamilton cycle: {' -> '.join(ham_cycle)}")

    # (c) G2 = K3,4 analysis
    S = ["s1", "s2", "s3"]
    T = ["t1", "t2", "t3", "t4"]
    print(f"(c) G2 = K_{len(S)},{len(T)}: Hamilton circuit = {len(S) == len(T)}, "
          f"Hamilton path = {abs(len(S) - len(T)) <= 1}")
    print("    Example Hamilton path: t1 -> s1 -> t2 -> s2 -> t3 -> s3 -> t4\n")


# ------------------------------------------------------------------------------
# TASK 4: Gray Codes and Hypercubes (Hamilton Cycles in Rotary Encoders)
# ------------------------------------------------------------------------------
def reflected_gray_code(n: int):
    if n == 1:
        return ["0", "1"]
    prev = reflected_gray_code(n - 1)
    return ["0" + code for code in prev] + ["1" + code for code in reversed(prev)]


def task4_gray_codes_hypercubes():
    print("=== ASSIGNMENT 4 - TASK 4 ===")
    # (a) Q3 Hamilton cycle via reflect-and-prefix
    gc3 = reflected_gray_code(3)
    hamming = lambda a, b: sum(x != y for x, y in zip(a, b))
    wrap_verified = all(
        hamming(gc3[i], gc3[(i + 1) % len(gc3)]) == 1 for i in range(len(gc3))
    )
    print(f"(a) Q3 Reflected Gray Code: {gc3}")
    print(f"    All consecutive transitions (including wrap-around) have distance 1: {wrap_verified}")

    # (b) Inductive verification for Q4 and Q5 closing edge
    for dim in [2, 3, 4, 5]:
        gcn = reflected_gray_code(dim)
        closing_dist = hamming(gcn[-1], gcn[0])
        assert closing_dist == 1
    print("(b) Verified inductive closing edge (10...0 -> 00...0) has Hamming distance 1 for n = 2..5")

    # (c) Bipartition parity check for Hamilton paths in Q3
    weight = lambda s: s.count("1")
    w000, w111, w011 = weight("000"), weight("111"), weight("011")
    print(f"(c) Weight parity: w(000)={w000} (even), w(111)={w111} (odd), w(011)={w011} (even)")
    print(f"    Hamilton path 000 -> 111 exists (opposite parity): {(w000 % 2) != (w111 % 2)}")
    print(f"    Hamilton path 000 -> 011 exists (same parity):     {(w000 % 2) != (w011 % 2)}\n")


# ------------------------------------------------------------------------------
# TASK 5: Euler vs Hamilton Traversals (Classifying Patrol & Courier Networks)
# ------------------------------------------------------------------------------
def task5_euler_vs_hamilton():
    print("=== ASSIGNMENT 4 - TASK 5 ===")
    networks = {
        "N1 (Bowtie)": (
            ["c", "a1", "a2", "b1", "b2"],
            [("c", "a1"), ("a1", "a2"), ("a2", "c"), ("c", "b1"), ("b1", "b2"), ("b2", "c")],
        ),
        "N2 (K4)": (
            [0, 1, 2, 3],
            [(i, j) for i in range(4) for j in range(i + 1, 4)],
        ),
        "N3 (K2,3)": (
            [0, 1, 2, 3, 4],
            [(u, v) for u in [0, 1] for v in [2, 3, 4]],
        ),
        "N4 (K5)": (
            [0, 1, 2, 3, 4],
            [(i, j) for i in range(5) for j in range(i + 1, 5)],
        ),
    }

    def has_ham_path_or_cycle(verts, edges, require_cycle):
        adj = {v: set() for v in verts}
        for u, v in edges:
            adj[u].add(v)
            adj[v].add(u)
        n = len(verts)

        def dfs(path):
            if len(path) == n:
                return (path[0] in adj[path[-1]]) if require_cycle else True
            for nxt in adj[path[-1]]:
                if nxt not in path and dfs(path + [nxt]):
                    return True
            return False

        starts = [verts[0]] if require_cycle else verts
        return any(dfs([s]) for s in starts)

    for name, (verts, edges) in networks.items():
        deg = {v: 0 for v in verts}
        for u, v in edges:
            deg[u] += 1
            deg[v] += 1
        odd_cnt = sum(d % 2 == 1 for d in deg.values())
        euler_circuit = odd_cnt == 0
        euler_open_trail = odd_cnt == 2
        ham_cycle = has_ham_path_or_cycle(verts, edges, True)
        ham_path = has_ham_path_or_cycle(verts, edges, False)
        print(
            f"{name:12s} | EulerCircuit={str(euler_circuit):5s} | "
            f"OpenEulerTrail={str(euler_open_trail):5s} | "
            f"HamCycle={str(ham_cycle):5s} | HamPath={str(ham_path):5s}"
        )

    # (b) & (c) Bowtie N1 analysis
    n1_verts, n1_edges = networks["N1 (Bowtie)"]
    print("(b) N1 Euler circuit: c -> a1 -> a2 -> c -> b1 -> b2 -> c (length 6; also shortest closed spanning walk)")

    # Adding 2 links (a1, b1) and (a2, b2) makes N1 both Eulerian and Hamiltonian
    n1_plus_2 = n1_edges + [("a1", "b1"), ("a2", "b2")]
    deg_2 = {v: sum(v in e for e in n1_plus_2) for v in n1_verts}
    both_ok = (
        all(d % 2 == 0 for d in deg_2.values())
        and has_ham_path_or_cycle(n1_verts, n1_plus_2, True)
    )

    # Adding 2 links (a1, b1) and (a1, b2) makes N1 Hamiltonian only (non-Eulerian)
    n1_ham_only = n1_edges + [("a1", "b1"), ("a1", "b2")]
    deg_ham_only = {v: sum(v in e for e in n1_ham_only) for v in n1_verts}
    ham_only_ok = (
        any(d % 2 == 1 for d in deg_ham_only.values())
        and has_ham_path_or_cycle(n1_verts, n1_ham_only, True)
    )
    print(f"(c) N1 + {{a1-b1, a2-b2}} -> Eulerian & Hamiltonian: {both_ok}")
    print(f"    N1 + {{a1-b1, a1-b2}} -> Hamiltonian only (non-Eulerian): {ham_only_ok}")


if __name__ == "__main__":
    task1_euler_fleury()
    task2_debruijn_sequences()
    task3_hamilton_drone_tours()
    task4_gray_codes_hypercubes()
    task5_euler_vs_hamilton()
