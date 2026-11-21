from itertools import combinations, product
from math import gcd, lcm

# ==============================================================================
# DISCRETE MATHEMATICS (UBA04) - ASSIGNMENT 5 (CO5)
# Posets, Hasse Diagrams, Lattices, Boolean Algebra & Homomorphisms
# ==============================================================================


# ------------------------------------------------------------------------------
# TASK 1: Partial Orders and Hasse Diagrams (Build-Task Scheduling)
# ------------------------------------------------------------------------------
def task1_poset_scheduling():
    print("=== ASSIGNMENT 5 - TASK 1 ===")
    S = [2, 3, 4, 6, 8, 12]
    leq = {(a, b) for a in S for b in S if b % a == 0}

    # (a) Poset axioms & covering pairs (Hasse diagram)
    reflexive = all((a, a) in leq for a in S)
    antisym = all(a == b for a in S for b in S if (a, b) in leq and (b, a) in leq)
    transitive = all(
        (a, c) in leq
        for a in S
        for b in S
        for c in S
        if (a, b) in leq and (b, c) in leq
    )
    covers = [
        (a, b)
        for a in S
        for b in S
        if a != b and (a, b) in leq and not any(
            c not in (a, b) and (a, c) in leq and (c, b) in leq for c in S
        )
    ]
    print(f"(a) Poset verified (Refl={reflexive}, Antisym={antisym}, Trans={transitive})")
    print(f"    Hasse covering pairs: {covers}")

    # (b) Extremal elements, chains, antichains, lattice check
    minimal = [a for a in S if not any(b != a and (b, a) in leq for b in S)]
    maximal = [a for a in S if not any(b != a and (a, b) in leq for b in S)]
    least = [a for a in S if all((a, b) in leq for b in S)]
    greatest = [a for a in S if all((b, a) in leq for b in S)]

    chains = [
        sub
        for k in range(1, len(S) + 1)
        for sub in combinations(S, k)
        if all((sub[i], sub[i + 1]) in leq for i in range(len(sub) - 1))
    ]
    antichains = [
        sub
        for k in range(1, len(S) + 1)
        for sub in combinations(S, k)
        if all((a, b) not in leq and (b, a) not in leq for a, b in combinations(sub, 2))
    ]
    max_chain_len = max(len(c) for c in chains)
    max_antichain_len = max(len(ac) for ac in antichains)

    # Lattice test: check lub and glb in S
    missing_lub = None
    missing_glb = None
    for a, b in combinations(S, 2):
        upper = [u for u in S if (a, u) in leq and (b, u) in leq]
        lub = [u for u in upper if all((u, w) in leq for w in upper)]
        if len(lub) != 1 and missing_lub is None:
            missing_lub = (a, b)
        lower = [l for l in S if (l, a) in leq and (l, b) in leq]
        glb = [l for l in lower if all((w, l) in leq for w in lower)]
        if len(glb) != 1 and missing_glb is None:
            missing_glb = (a, b)

    print(f"(b) Minimal: {minimal}, Maximal: {maximal}, Least: {least or None}, Greatest: {greatest or None}")
    print(f"    Longest chain size: {max_chain_len} (e.g. {[c for c in chains if len(c) == max_chain_len][0]})")
    print(f"    Largest antichain size: {max_antichain_len} (Dilworth chains: [2, 4, 8] & [3, 6, 12])")
    print(f"    Is lattice: False (no LUB for {missing_lub}, no GLB for {missing_glb})")

    # (c) Linear extensions & 2-worker parallel schedule
    linear_exts = []

    def backtrack(curr):
        if len(curr) == len(S):
            linear_exts.append(curr)
            return
        for x in S:
            if x not in curr and all((y, x) not in leq or y in curr for y in S if y != x):
                backtrack(curr + [x])

    backtrack([])
    print(f"(c) Total linear extensions: {len(linear_exts)}")
    print(f"    Two valid linear extensions: {linear_exts[0]} and {linear_exts[1]}")
    print("    Min completion time with 2 workers (1 hr/task): 3 hours (e.g., [2,3], [4,6], [8,12])\n")


# ------------------------------------------------------------------------------
# TASK 2: Lattices and Direct Products (Security Classification Labels)
# ------------------------------------------------------------------------------
def task2_direct_product_lattice():
    print("=== ASSIGNMENT 5 - TASK 2 ===")
    levels = ["U", "C", "S"]
    rank = {"U": 0, "C": 1, "S": 2}
    compartments = [
        frozenset(),
        frozenset({"Cr"}),
        frozenset({"Nu"}),
        frozenset({"Cr", "Nu"}),
    ]
    L = [(l, K) for l in levels for K in compartments]

    def join(x, y):
        return (levels[max(rank[x[0]], rank[y[0]])], x[1] | y[1])

    def meet(x, y):
        return (levels[min(rank[x[0]], rank[y[0]])], x[1] & y[1])

    # (a) Join, Meet, Cardinality, Bottom & Top
    x1, x2 = ("S", frozenset({"Cr"})), ("C", frozenset({"Nu"}))
    bottom, top = ("U", frozenset()), ("S", frozenset({"Cr", "Nu"}))
    print(f"(a) |L| = {len(L)}, Bottom = {bottom}, Top = {top}")
    print(f"    (S, {{Cr}}) v (C, {{Nu}}) = {join(x1, x2)}")
    print(f"    (S, {{Cr}}) ^ (C, {{Nu}}) = {meet(x1, x2)}")

    # (b) Distributivity, Complementedness, Boolean check
    distributive = all(
        meet(a, join(b, c)) == join(meet(a, b), meet(a, c))
        for a in L
        for b in L
        for c in L
    )
    complements = {
        a: [b for b in L if join(a, b) == top and meet(a, b) == bottom]
        for a in L
    }
    complemented = all(len(v) > 0 for v in complements.values())
    print(f"(b) Distributive: {distributive}, Complemented: {complemented}, Boolean: {distributive and complemented}")
    print(f"    Complement of (U, {{Cr}}): {complements[('U', frozenset({'Cr'}))]}")
    print(f"    Complements of (C, empty): {complements[('C', frozenset())]}")

    # (c) Homomorphisms pi(l, K) = K and phi(l, K) = |K|
    pi_hom = all(
        (x[1] | y[1]) == join(x, y)[1] and (x[1] & y[1]) == meet(x, y)[1]
        for x in L
        for y in L
    )
    phi_hom = all(
        max(len(x[1]), len(y[1])) == len(join(x, y)[1])
        and min(len(x[1]), len(y[1])) == len(meet(x, y)[1])
        for x in L
        for y in L
    )
    pi_partition = {
        tuple(sorted(K)): [lbl for lbl in L if lbl[1] == K]
        for K in compartments
    }
    print(f"(c) pi(l, K) = K is lattice homomorphism: {pi_hom}")
    print(f"    Induced partition of L by pi has {len(pi_partition)} blocks of size 3")
    print(f"    phi(l, K) = |K| is lattice homomorphism: {phi_hom}\n")


# ------------------------------------------------------------------------------
# TASK 3: Special Lattices (Permission Hierarchies and Divisor Lattices)
# ------------------------------------------------------------------------------
def task3_special_lattices():
    print("=== ASSIGNMENT 5 - TASK 3 ===")
    # (a) Pentagon lattice N5 = {0, a, b, c, 1} with 0 < a < b < 1 and 0 < c < 1
    N5 = ["0", "a", "b", "c", "1"]
    join_N5 = {
        ("a", "c"): "1", ("c", "a"): "1",
        ("b", "c"): "1", ("c", "b"): "1",
        ("a", "b"): "b", ("b", "a"): "b",
    }
    meet_N5 = {
        ("a", "c"): "0", ("c", "a"): "0",
        ("b", "c"): "0", ("c", "b"): "0",
        ("a", "b"): "a", ("b", "a"): "a",
    }
    j = lambda x, y: x if x == y else ("1" if "1" in (x, y) else (y if x == "0" else (x if y == "0" else join_N5[(x, y)])))
    m = lambda x, y: x if x == y else ("0" if "0" in (x, y) else (y if x == "1" else (x if y == "1" else meet_N5[(x, y)])))

    dist_viol = m("b", j("a", "c")) != j(m("b", "a"), m("b", "c"))
    c_complements = [x for x in N5 if j("c", x) == "1" and m("c", x) == "0"]
    mod_viol = j("a", m("c", "b")) != m(j("a", "c"), "b")  # since a <= b
    print(f"(a) N5 violates distributivity (b ^ (a v c) != (b^a) v (b^c)): {dist_viol}")
    print(f"    Complements of c in N5 (non-unique): {c_complements}")
    print(f"    N5 violates modularity (a <= b, yet a v (c^b) != (a v c) ^ b): {mod_viol}")

    # (b) Divisor lattices D30, D36, D42
    def divisors(n):
        return [d for d in range(1, n + 1) if n % d == 0]

    def is_boolean_divisor_lattice(n):
        D = divisors(n)
        return all(
            any(lcm(d, c) == n and gcd(d, c) == 1 for c in D)
            for d in D
        )

    for n in [30, 36, 42]:
        print(f"(b) D_{n} is Boolean algebra: {is_boolean_divisor_lattice(n)}")

    D30 = divisors(30)
    complements_30 = {d: 30 // d for d in D30}
    atoms_30 = [d for d in D30 if d > 1 and not any(1 < k < d and d % k == 0 for k in D30)]
    uncomplemented_36 = [
        d for d in divisors(36)
        if not any(lcm(d, c) == 36 and gcd(d, c) == 1 for c in divisors(36))
    ]
    print(f"    D30 atoms: {atoms_30}, complements: {complements_30}")
    print(f"    D36 elements without complement: {uncomplemented_36}")

    # (c) Subset T = {1, 2, 3, 5, 30} inside D30
    T = [1, 2, 3, 5, 30]
    lub_T = lambda a, b: min(u for u in T if u % a == 0 and u % b == 0)
    glb_T = lambda a, b: max(l for l in T if a % l == 0 and b % l == 0)
    is_sublattice = (lub_T(2, 3) == lcm(2, 3))
    T_distributive = all(
        glb_T(a, lub_T(b, c)) == lub_T(glb_T(a, b), glb_T(a, c))
        for a in T
        for b in T
        for c in T
    )
    print(f"(c) T = {T}: lub_T(2,3) = {lub_T(2, 3)} vs lcm(2,3) = {lcm(2, 3)} -> Sublattice: {is_sublattice}")
    print(f"    T is distributive lattice: {T_distributive}\n")


# ------------------------------------------------------------------------------
# TASK 4: Boolean Algebra and Logic Optimization (Redundant Sensor Voting)
# ------------------------------------------------------------------------------
def task4_boolean_optimization():
    print("=== ASSIGNMENT 5 - TASK 4 ===")
    # (a) F = A'BC + AB'C + ABC' + ABC == AB + BC + AC
    equiv_voting = all(
        (
            ((not A) and B and C)
            or (A and (not B) and C)
            or (A and B and (not C))
            or (A and B and C)
        )
        == ((A and B) or (B and C) or (A and C))
        for A, B, C in product([False, True], repeat=3)
    )
    print(f"(a) F == AB + BC + AC: {equiv_voting} (Literal count reduced from 12 to 6)")

    # (b) Absorption-complement & Consensus Theorem
    id_i = all((x or ((not x) and y)) == (x or y) for x, y in product([False, True], repeat=2))
    id_ii = all(
        ((x and y) or ((not x) and z) or (y and z)) == ((x and y) or ((not x) and z))
        for x, y, z in product([False, True], repeat=3)
    )
    print(f"(b) x + x'y == x + y: {id_i}, Consensus xy + x'z + yz == xy + x'z: {id_ii}")

    # (c) All 6 monotone Boolean functions of 2 variables (x, y)
    inputs_2 = [(0, 0), (0, 1), (1, 0), (1, 1)]
    all_funcs = list(product([0, 1], repeat=4))
    monotone_funcs = [
        f
        for f in all_funcs
        if all(
            f[i] <= f[j]
            for i, (x1, y1) in enumerate(inputs_2)
            for j, (x2, y2) in enumerate(inputs_2)
            if x1 <= x2 and y1 <= y2
        )
    ]
    names = {
        (0, 0, 0, 0): "0",
        (0, 0, 0, 1): "x AND y",
        (0, 0, 1, 1): "x",
        (0, 1, 0, 1): "y",
        (0, 1, 1, 1): "x OR y",
        (1, 1, 1, 1): "1",
    }
    f_or = lambda f, g: tuple(a | b for a, b in zip(f, g))
    f_and = lambda f, g: tuple(a & b for a, b in zip(f, g))
    sublattice = all(
        f_or(f, g) in monotone_funcs and f_and(f, g) in monotone_funcs
        for f in monotone_funcs
        for g in monotone_funcs
    )
    complemented = all(
        any(f_or(f, g) == (1, 1, 1, 1) and f_and(f, g) == (0, 0, 0, 0) for g in monotone_funcs)
        for f in monotone_funcs
    )
    print(f"(c) Monotone 2-var functions ({len(monotone_funcs)}): {[names[f] for f in monotone_funcs]}")
    print(f"    Sublattice of B16: {sublattice}, Boolean algebra (complemented): {complemented}\n")


# ------------------------------------------------------------------------------
# TASK 5: Boolean Algebras and Homomorphisms (Bit-Mask Feature Flags)
# ------------------------------------------------------------------------------
def task5_boolean_isomorphism_and_homomorphisms():
    print("=== ASSIGNMENT 5 - TASK 5 ===")
    D210 = [d for d in range(1, 211) if 210 % d == 0]
    primes = [2, 3, 5, 7]

    def f(d):
        return tuple(int(d % p == 0) for p in primes)

    # (a) Isomorphism f: D210 -> B4
    bijective = len({f(d) for d in D210}) == 16
    preserves_ops = all(
        f(lcm(x, y)) == tuple(a | b for a, b in zip(f(x), f(y)))
        and f(gcd(x, y)) == tuple(a & b for a, b in zip(f(x), f(y)))
        and f(210 // x) == tuple(1 - a for a in f(x))
        for x in D210
        for y in D210
    )
    print(f"(a) f: D210 -> B4 is Boolean isomorphism: {bijective and preserves_ops}")
    print(f"    x=6 -> {f(6)}, y=35 -> {f(35)}, lcm(6,35)={lcm(6,35)} -> {f(lcm(6,35))}, gcd(6,35)={gcd(6,35)} -> {f(gcd(6,35))}")
    print(f"    d=30 -> {f(30)}, complement 210/30 = 7 -> {f(7)}")

    # (b) Compression h(x1,x2,x3,x4) = (x1 ^ x2, x3 v x4) vs projection p(x1,x2,x3,x4) = (x1, x2)
    B4 = list(product([0, 1], repeat=4))
    b_or = lambda u, v: tuple(a | b for a, b in zip(u, v))
    b_and = lambda u, v: tuple(a & b for a, b in zip(u, v))

    h = lambda x: (x[0] & x[1], x[2] | x[3])
    p = lambda x: (x[0], x[1])

    h_counter = next(
        (
            (x, y)
            for x in B4
            for y in B4
            if h(b_or(x, y)) != b_or(h(x), h(y)) or h(b_and(x, y)) != b_and(h(x), h(y))
        ),
        None,
    )
    p_is_hom = all(
        p(b_or(x, y)) == b_or(p(x), p(y)) and p(b_and(x, y)) == b_and(p(x), p(y))
        for x in B4
        for y in B4
    )
    print(f"(b) h is lattice homomorphism: {h_counter is None} (counterexample: {h_counter})")
    print(f"    Projection p is lattice homomorphism: {p_is_hom}")

    # (c) Parity checker pi(x) = x1 (+) x2 (+) x3 (+) x4
    pi = lambda x: sum(x) % 2
    pi_is_hom = all(
        pi(b_or(x, y)) == (pi(x) | pi(y)) and pi(b_and(x, y)) == (pi(x) & pi(y))
        for x in B4
        for y in B4
    )
    pi_monotone = all(
        pi(x) <= pi(y)
        for x in B4
        for y in B4
        if all(a <= b for a, b in zip(x, y))
    )
    print(f"(c) Parity pi is lattice homomorphism: {pi_is_hom}, Order-preserving (monotone): {pi_monotone}")


if __name__ == "__main__":
    task1_poset_scheduling()
    task2_direct_product_lattice()
    task3_special_lattices()
    task4_boolean_optimization()
    task5_boolean_isomorphism_and_homomorphisms()
