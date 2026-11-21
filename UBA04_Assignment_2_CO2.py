from itertools import combinations, product
from math import comb

# ==============================================================================
# DISCRETE MATHEMATICS (UBA04) - ASSIGNMENT 2 (CO2)
# Set Identities, Power Sets, Relations, Equivalence Relations, Partitions
# ==============================================================================


# ------------------------------------------------------------------------------
# TASK 1: Set Identities and Inclusion-Exclusion (Multi-Filter Content Screening)
# ------------------------------------------------------------------------------
def task1_sets_and_inclusion_exclusion():
    print("=== ASSIGNMENT 2 - TASK 1 ===")
    # (a) Algebraic identity verification via membership regions: A \ (B U C) == (A \ B) n (A \ C)
    identity_holds = all(
        (a and not (b or c)) == ((a and not b) and (a and not c))
        for a, b, c in product([False, True], repeat=3)
    )
    print(f"(a) A \\ (B U C) == (A \\ B) n (A \\ C): {identity_holds}")

    # (b) Inclusion-Exclusion counts
    U_size = 500
    A, B, C = 220, 180, 150
    AB, AC, BC = 70, 60, 50
    ABC = 20

    at_least_one = A + B + C - (AB + AC + BC) + ABC
    none = U_size - at_least_one
    exact_three = ABC
    exact_two = (AB - ABC) + (AC - ABC) + (BC - ABC)
    exact_one = (
        (A - AB - AC + ABC)
        + (B - AB - BC + ABC)
        + (C - AC - BC + ABC)
    )
    consistent = (none + exact_one + exact_two + exact_three) == U_size

    print(f"(b) At least one: {at_least_one}, None: {none}, Exact 1: {exact_one}, "
          f"Exact 2: {exact_two}, Exact 3: {exact_three}, Consistent: {consistent}")

    # (c) Symmetric difference A (+) B (+) C (odd number of filters)
    odd_filters = exact_one + exact_three
    formula_check = A + B + C - 2 * (AB + AC + BC) + 4 * ABC
    print(f"(c) High risk |A (+) B (+) C| = {odd_filters}, Formula check = {formula_check}\n")


# ------------------------------------------------------------------------------
# TASK 2: Power Sets and Cartesian Products (RBAC and Firewall Rules)
# ------------------------------------------------------------------------------
def task2_power_sets_and_products():
    print("=== ASSIGNMENT 2 - TASK 2 ===")
    P = {"r", "w", "x", "d"}
    power_P = [
        frozenset(s)
        for k in range(len(P) + 1)
        for s in combinations(sorted(P), k)
    ]
    F = {S for S in power_P if ("d" not in S) or ("w" in S)}
    print(f"(a) |P(P)| = {len(power_P)}, |F| = {len(F)}")

    closed_union = all((A | B) in F for A in F for B in F)
    closed_inter = all((A & B) in F for A in F for B in F)
    comp_counterexamples = [
        (set(A), set(frozenset(P) - A))
        for A in F
        if (frozenset(P) - A) not in F
    ]
    print(f"(a) Closed under union: {closed_union}, intersection: {closed_inter}, "
          f"complement: {len(comp_counterexamples) == 0}")
    print(f"    Complement counterexample (S, P\\S): {comp_counterexamples[0]}")

    # (b) Cartesian product intersection identity & firewall rule merge
    A_s, B_s, C_s, D_s = {1, 2}, {"x", "y"}, {2, 3}, {"y", "z"}
    lhs = set(product(A_s, B_s)) & set(product(C_s, D_s))
    rhs = set(product(A_s & C_s, B_s & D_s))
    print(f"(b) (A x B) n (C x D) == (A n C) x (B n D): {lhs == rhs}")

    S1, T1 = {"s1", "s2"}, {80}
    S2, T2 = {"s3"}, {443}
    separate = set(product(S1, T1)) | set(product(S2, T2))
    merged = set(product(S1 | S2, T1 | T2))
    extra_pairs = sorted(merged - separate)
    print(f"(b) Extra unintended connections in merged firewall rule: {extra_pairs}")

    # (c) RBAC access policies counting
    U_sz, R_sz, L_sz = 3, 2, 2
    product_sz = U_sz * R_sz * L_sz
    total_policies = 2 ** product_sz
    valid_nonempty_per_user = (2 ** (R_sz * L_sz) - 1) ** U_sz
    large_policies_exp = 20 * 10 * 5
    print(f"(c) |U x R x L| = {product_sz}, Total policies = {total_policies}, "
          f"Every user >= 1 entry = {valid_nonempty_per_user}")
    print(f"(c) For 20 users, 10 resources, 5 levels: 2^{large_policies_exp} policies\n")


# ------------------------------------------------------------------------------
# TASK 3: Types of Relations and Closures (Software Module Dependencies)
# ------------------------------------------------------------------------------
def bool_matmul(A, B):
    n = len(A)
    return [
        [int(any(A[i][k] and B[k][j] for k in range(n))) for j in range(n)]
        for i in range(n)
    ]


def bool_mat_or(A, B):
    n = len(A)
    return [[A[i][j] | B[i][j] for j in range(n)] for i in range(n)]


def task3_relations_and_closures():
    print("=== ASSIGNMENT 2 - TASK 3 ===")
    MR = [
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [1, 0, 0, 1],
        [0, 0, 0, 0],
    ]
    n = 4

    # (a) Properties
    reflexive = all(MR[i][i] == 1 for i in range(n))
    irreflexive = all(MR[i][i] == 0 for i in range(n))
    sym_witness = next(
        ((i + 1, j + 1) for i in range(n) for j in range(n) if MR[i][j] != MR[j][i]),
        None,
    )
    antisym = all(
        not (MR[i][j] == 1 and MR[j][i] == 1) for i in range(n) for j in range(n) if i != j
    )
    trans_witness = next(
        (
            (i + 1, j + 1, k + 1)
            for i in range(n)
            for j in range(n)
            for k in range(n)
            if MR[i][j] == 1 and MR[j][k] == 1 and MR[i][k] == 0
        ),
        None,
    )
    print(f"(a) Reflexive: {reflexive}, Irreflexive: {irreflexive}, "
          f"Symmetric: {sym_witness is None} (witness: {sym_witness}), "
          f"Antisymmetric: {antisym}, Transitive: {trans_witness is None} (witness: {trans_witness})")

    # (b) Boolean powers and transitive closure
    MR2 = bool_matmul(MR, MR)
    MR3 = bool_matmul(MR2, MR)
    MR4 = bool_matmul(MR3, MR)
    MR_plus = bool_mat_or(bool_mat_or(MR, MR2), bool_mat_or(MR3, MR4))

    print("(b) Transitive closure MR+:")
    for row in MR_plus:
        print("   ", row)
    indirect = [
        (i + 1, j + 1)
        for i in range(n)
        for j in range(n)
        if MR_plus[i][j] == 1 and MR[i][j] == 0
    ]
    circular_modules = [i + 1 for i in range(n) if MR_plus[i][i] == 1]
    print(f"    Indirect dependencies (R+ \\ R): {indirect}")
    print(f"    Circular dependency modules: {circular_modules}")

    # (c) Mutual reachability equivalence relation & smallest equivalence closure
    def get_classes(mat):
        visited = set()
        classes = []
        for i in range(n):
            if i not in visited:
                cls = [j + 1 for j in range(n) if mat[i][j] == 1]
                visited.update(j - 1 for j in cls)
                classes.append(cls)
        return classes

    M_sim = [
        [int(i == j or (MR_plus[i][j] == 1 and MR_plus[j][i] == 1)) for j in range(n)]
        for i in range(n)
    ]
    print(f"(c) Mutual reachability classes (~): {get_classes(M_sim)}")

    # Smallest equivalence relation containing R: (R U R^T U I)+
    M_base = [
        [int(i == j or MR[i][j] == 1 or MR[j][i] == 1) for j in range(n)]
        for i in range(n)
    ]
    M_eq = M_base
    for _ in range(n):
        M_eq = bool_matmul(M_eq, M_base)
    print(f"(c) Smallest equivalence closure classes: {get_classes(M_eq)}\n")


# ------------------------------------------------------------------------------
# TASK 4: Equivalence Relations and Partitions (Constant-Weight Codes)
# ------------------------------------------------------------------------------
def task4_equivalence_and_partitions():
    print("=== ASSIGNMENT 2 - TASK 4 ===")
    B8 = list(product([0, 1], repeat=8))

    # (a) Weight equivalence ~
    classes_sim = {}
    for b in B8:
        classes_sim.setdefault(sum(b), []).append(b)
    sizes_sim = {w: len(cls) for w, cls in sorted(classes_sim.items())}
    print(f"(a) Number of ~ classes: {len(classes_sim)}, Sizes: {sizes_sim}, "
          f"Sum: {sum(sizes_sim.values())}")

    # (b) Refinement ≈ (same weight and same first bit)
    classes_ref = {}
    for b in B8:
        classes_ref.setdefault((b[0], sum(b)), []).append(b)

    size_11110000 = len(classes_ref[(1, 4)])
    size_00000011 = len(classes_ref[(0, 2)])
    pairs_sim = sum(len(cls) ** 2 for cls in classes_sim.values())
    pairs_ref = sum(len(cls) ** 2 for cls in classes_ref.values())
    print(f"(b) Number of non-empty ≈ classes: {len(classes_ref)} (out of 18 theoretical pairs)")
    print(f"    |[11110000]_≈| = {size_11110000} (C(7,3)={comb(7,3)}), "
          f"|[00000011]_≈| = {size_00000011} (C(7,2)={comb(7,2)})")
    print(f"    |≈| ordered pairs = {pairs_ref} < |~| ordered pairs = {pairs_sim}")

    # (c) Single-bit error tolerance relation T
    x = (0, 0, 0, 0, 0, 0, 0, 0)
    y = (1, 0, 0, 0, 0, 0, 0, 0)
    z = (1, 1, 0, 0, 0, 0, 0, 0)
    hamming = lambda u, v: sum(a != b for a, b in zip(u, v))
    print(f"(c) Transitivity failure witness for T: d(x,y)={hamming(x,y)}, "
          f"d(y,z)={hamming(y,z)}, d(x,z)={hamming(x,z)}")
    print("    Smallest equivalence relation containing T is B8 x B8 (1 universal class of size 256)\n")


# ------------------------------------------------------------------------------
# TASK 5: Relational Matrices and Partitions (VLAN and Rack Assignment)
# ------------------------------------------------------------------------------
def task5_relational_matrices_partitions():
    print("=== ASSIGNMENT 2 - TASK 5 ===")
    servers = ["a", "b", "c", "d", "e", "f"]
    idx = {s: i for i, s in enumerate(servers)}
    n = len(servers)

    MR = [
        [1, 0, 1, 0, 0, 0],
        [0, 1, 0, 0, 1, 1],
        [1, 0, 1, 0, 0, 0],
        [0, 0, 0, 1, 0, 0],
        [0, 1, 0, 0, 1, 0],
        [0, 1, 0, 0, 0, 1],
    ]

    # (a) Test properties, locate transitivity violations, repair to equivalence relation
    refl = all(MR[i][i] == 1 for i in range(n))
    sym = all(MR[i][j] == MR[j][i] for i in range(n) for j in range(n))
    missing_pairs = set()
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if MR[i][j] == 1 and MR[j][k] == 1 and MR[i][k] == 0:
                    missing_pairs.add((servers[i], servers[k]))

    MR_fixed = [row[:] for row in MR]
    for u, v in missing_pairs:
        MR_fixed[idx[u]][idx[v]] = 1

    V = []
    seen = set()
    for i in range(n):
        if i not in seen:
            blk = [servers[j] for j in range(n) if MR_fixed[i][j] == 1]
            seen.update(idx[s] for s in blk)
            V.append(blk)

    print(f"(a) Reflexive: {refl}, Symmetric: {sym}, Transitive: {len(missing_pairs) == 0}")
    print(f"    Minimum ordered pairs to add: {sorted(missing_pairs)}")
    print(f"    Resulting VLAN partition V: {V}")

    # (b) Partition P = {{a,b}, {c,d,e}, {f}}
    P = [["a", "b"], ["c", "d", "e"], ["f"]]
    MRP = [[0] * n for _ in range(n)]
    for blk in P:
        for u in blk:
            for v in blk:
                MRP[idx[u]][idx[v]] = 1
    idem = bool_matmul(MRP, MRP) == MRP
    print(f"(b) MRP Boolean idempotence (M o M == M): {idem}")

    # (c) Rack partition Q = {{a,b,c}, {d,e,f}} vs VLAN partition V
    Q = [["a", "b", "c"], ["d", "e", "f"]]
    MRQ = [[0] * n for _ in range(n)]
    for blk in Q:
        for u in blk:
            for v in blk:
                MRQ[idx[u]][idx[v]] = 1

    R_inter = [[MRQ[i][j] & MR_fixed[i][j] for j in range(n)] for i in range(n)]
    R_union = [[MRQ[i][j] | MR_fixed[i][j] for j in range(n)] for i in range(n)]

    is_equiv = lambda M: (
        all(M[i][i] == 1 for i in range(n))
        and all(M[i][j] == M[j][i] for i in range(n) for j in range(n))
        and all(
            M[i][k] == 1
            for i in range(n)
            for j in range(n)
            for k in range(n)
            if M[i][j] == 1 and M[j][k] == 1
        )
    )

    inter_classes = []
    seen = set()
    for i in range(n):
        if i not in seen:
            blk = [servers[j] for j in range(n) if R_inter[i][j] == 1]
            seen.update(idx[s] for s in blk)
            inter_classes.append(blk)

    print(f"(c) RQ n RV is equivalence relation: {is_equiv(R_inter)}, Classes: {inter_classes}")
    print(f"    RQ U RV is equivalence relation: {is_equiv(R_union)}")


if __name__ == "__main__":
    task1_sets_and_inclusion_exclusion()
    task2_power_sets_and_products()
    task3_relations_and_closures()
    task4_equivalence_and_partitions()
    task5_relational_matrices_partitions()
