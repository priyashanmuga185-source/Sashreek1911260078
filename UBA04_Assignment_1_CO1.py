from itertools import product

# ==============================================================================
# DISCRETE MATHEMATICS (UBA04) - ASSIGNMENT 1 (CO1)
# Propositional Logic, Normal Forms, Rules of Inference, Predicates & Quantifiers
# ==============================================================================


def imp(a: bool, b: bool) -> bool:
    return (not a) or b


# ------------------------------------------------------------------------------
# TASK 1: Propositional Logic and Logical Equivalence (Packet-Filtering Policies)
# ------------------------------------------------------------------------------
def task1_packet_filtering():
    print("=== ASSIGNMENT 1 - TASK 1 ===")
    vars_3 = list(product([False, True], repeat=3))

    def pol_a(p, q, r):
        return imp(p or q, r)

    def pol_b(p, q, r):
        return imp(p, r) and imp(q, r)

    def pol_c(p, q, r):
        return imp(p and q, r)

    # (a) Truth table, logical equivalence, and implication analysis
    print("p | q | r || A | B | C")
    for p, q, r in vars_3:
        print(
            f"{int(p)} | {int(q)} | {int(r)} || "
            f"{int(pol_a(p, q, r))} | {int(pol_b(p, q, r))} | {int(pol_c(p, q, r))}"
        )

    equiv_ab = all(pol_a(*v) == pol_b(*v) for v in vars_3)
    a_implies_c = all(imp(pol_a(*v), pol_c(*v)) for v in vars_3)
    c_implies_a = all(imp(pol_c(*v), pol_a(*v)) for v in vars_3)
    counterexamples_c_to_a = [v for v in vars_3 if pol_c(*v) and not pol_a(*v)]

    print(f"A == B: {equiv_ab}")
    print(f"A => C: {a_implies_c}, C => A: {c_implies_a}")
    print(f"Counterexamples for C => A (p, q, r): {counterexamples_c_to_a}")

    # (b) Negation of A and satisfiability of A ^ ~B
    neg_a_simplified_ok = all(
        (not pol_a(p, q, r)) == ((p or q) and (not r)) for p, q, r in vars_3
    )
    a_and_not_b_sat = any(pol_a(*v) and (not pol_b(*v)) for v in vars_3)
    print(f"~A == (p v q) ^ ~r: {neg_a_simplified_ok}")
    print(f"Satisfiability of A ^ ~B: {a_and_not_b_sat}")

    # (c) Converse, Inverse, Contrapositive of p -> r
    vars_2 = list(product([False, True], repeat=2))
    orig = lambda p, r: imp(p, r)
    conv = lambda p, r: imp(r, p)
    inv = lambda p, r: imp(not p, not r)
    contra = lambda p, r: imp(not r, not p)

    print(f"Original == Contrapositive: {all(orig(*v) == contra(*v) for v in vars_2)}")
    print(f"Original == Converse:       {all(orig(*v) == conv(*v) for v in vars_2)}")
    print(f"Converse == Inverse:        {all(conv(*v) == inv(*v) for v in vars_2)}")
    rate_limiter_witness = [v for v in vars_2 if orig(*v) and v[1] and not v[0]]
    print(f"Rate-limiter witness (p=False, r=True) refuting r => p: {rate_limiter_witness}\n")


# ------------------------------------------------------------------------------
# TASK 2: Principal Normal Forms (Data-Selector Circuit Design)
# ------------------------------------------------------------------------------
def task2_normal_forms():
    print("=== ASSIGNMENT 1 - TASK 2 ===")
    vars_3 = list(product([False, True], repeat=3))

    def F(p, q, r):
        return (p or q) and ((not p) or r)

    def G(p, q, r):
        return (p and r) or ((not p) and q) or (q and r)

    def H(p, q, r):
        return (p and r) or q

    # (a) PDNF minterms & (b) PCNF maxterms
    minterms = [i for i, v in enumerate(vars_3) if F(*v)]
    maxterms = [i for i, v in enumerate(vars_3) if not F(*v)]
    print(f"F PDNF minterms: {minterms}")
    print(f"F PCNF maxterms: {maxterms}")
    print(f"|Minterms| + |Maxterms| = {len(minterms) + len(maxterms)} (2^3 = 8)")

    # (c) Circuit comparisons
    g_minterms = [i for i, v in enumerate(vars_3) if G(*v)]
    h_minterms = [i for i, v in enumerate(vars_3) if H(*v)]
    h_disagreements = [(i, v) for i, v in enumerate(vars_3) if F(*v) != H(*v)]
    print(f"G minterms: {g_minterms} -> G == F: {g_minterms == minterms}")
    print(f"H minterms: {h_minterms} -> H == F: {h_minterms == minterms}")
    print(f"H vs F disagreement (index, (p, q, r)): {h_disagreements}\n")


# ------------------------------------------------------------------------------
# TASK 3: Rules of Inference (Intrusion Analysis after an Alert-Free Night)
# ------------------------------------------------------------------------------
def task3_rules_of_inference():
    print("=== ASSIGNMENT 1 - TASK 3 ===")
    vars_4 = list(product([False, True], repeat=4))  # (p, q, r, s)

    def P1(p, q, r, s):
        return imp(p, q or r)

    def P2(p, q, r, s):
        return not q

    def P3(p, q, r, s):
        return imp(r, s)

    def P4(p, q, r, s):
        return not s

    premises = [P1, P2, P3, P4]

    # (a) Validity of conclusion ~p
    valid_not_p = all(
        imp(all(P(*v) for P in premises), not v[0]) for v in vars_4
    )
    print(f"(P1 ^ P2 ^ P3 ^ P4) |= ~p: {valid_not_p}")

    # (b) Fallacy of affirming the consequent: (P3 ^ s) |= r
    fallacy_countermodels = [
        v for v in vars_4 if P3(*v) and v[3] and not v[2]
    ]
    print(f"Countermodels for (P3 ^ s) |= r (p, q, r, s): {fallacy_countermodels}")

    # (c) Indispensability of each premise
    for idx in range(4):
        other_premises = [P for j, P in enumerate(premises) if j != idx]
        witnesses = [
            v for v in vars_4 if all(P(*v) for P in other_premises) and v[0]
        ]
        print(f"Without P{idx + 1}, witnesses with p=True: {witnesses}")
    print()


# ------------------------------------------------------------------------------
# TASK 4: Predicates and Quantifiers (Process Monitoring and Access Control)
# ------------------------------------------------------------------------------
def task4_predicates_quantifiers():
    print("=== ASSIGNMENT 1 - TASK 4 ===")
    U = ["a", "b"]
    domain_subsets = [
        {U[i] for i, flag in enumerate(mask) if flag}
        for mask in product([False, True], repeat=len(U))
    ]

    # (a) Negation of policy S: forall x (P(x) -> M(x))
    for P, M in product(domain_subsets, repeat=2):
        S = all(imp(x in P, x in M) for x in U)
        neg_S = any((x in P) and (x not in M) for x in U)
        assert (not S) == neg_S
    print("Verified: ~forall x (P(x) -> M(x)) <=> exists x (P(x) ^ ~M(x))")

    # (b)(i) exists x (P(x) ^ L(x)) => exists x P(x) ^ exists x L(x)
    bi_holds = True
    bi_converse_witness = None
    for P, L in product(domain_subsets, repeat=2):
        lhs = any((x in P) and (x in L) for x in U)
        rhs = any(x in P for x in U) and any(x in L for x in U)
        if lhs and not rhs:
            bi_holds = False
        if rhs and not lhs and bi_converse_witness is None:
            bi_converse_witness = (P, L)
    print(f"(b)(i) Forward holds: {bi_holds}, Converse witness (P, L): {bi_converse_witness}")

    # (b)(ii) forall x (P(x) v L(x)) =/=> forall x P(x) v forall x L(x)
    bii_witness = None
    for P, L in product(domain_subsets, repeat=2):
        lhs = all((x in P) or (x in L) for x in U)
        rhs = all(x in P for x in U) or all(x in L for x in U)
        if lhs and not rhs and bii_witness is None:
            bii_witness = (P, L)
    print(f"(b)(ii) Counterexample (P, L): {bii_witness}")

    # (b)(iii) Equivalence
    biii_equiv = True
    for P, L, M in product(domain_subsets, repeat=3):
        lhs = all(imp(x in P, x in M) for x in U) and all(imp(x in L, x in M) for x in U)
        rhs = all(imp((x in P) or (x in L), x in M) for x in U)
        if lhs != rhs:
            biii_equiv = False
    print(f"(b)(iii) Equivalence holds across all models: {biii_equiv}")

    # (c) 3x3 permission table N(x, y): forall x exists y N(x,y) vs exists y forall x N(x,y)
    N = [
        [1, 0, 0],
        [0, 1, 0],
        [0, 0, 1],
    ]
    forall_x_exists_y = all(any(N[x][y] == 1 for y in range(3)) for x in range(3))
    exists_y_forall_x = any(all(N[x][y] == 1 for x in range(3)) for y in range(3))
    print(
        f"(c) 3x3 Identity Matrix -> forall x exists y N(x,y): {forall_x_exists_y}, "
        f"exists y forall x N(x,y): {exists_y_forall_x}\n"
    )


# ------------------------------------------------------------------------------
# TASK 5: Theory of Inference with Quantifiers (IoT Smart-Grid Nodes)
# ------------------------------------------------------------------------------
def task5_quantified_inference():
    print("=== ASSIGNMENT 1 - TASK 5 ===")
    U = ["a", "b"]
    domain_subsets = [
        {U[i] for i, flag in enumerate(mask) if flag}
        for mask in product([False, True], repeat=len(U))
    ]

    # (a) Verify Q1, Q2, Q3 |= exists x (E(x) ^ F(x))
    part_a_valid = True
    for S, A, E, F in product(domain_subsets, repeat=4):
        Q1 = all(imp(x in S, x in A) for x in U)
        Q2 = all(imp(x in A, x in E) for x in U)
        Q3 = any((x in S) and (x in F) for x in U)
        conc = any((x in E) and (x in F) for x in U)
        if Q1 and Q2 and Q3 and not conc:
            part_a_valid = False
    print(f"(a) Q1, Q2, Q3 |= exists x (E(x) ^ F(x)): {part_a_valid}")

    # (b) Counter-model for Q1 ^ exists x (A(x) ^ F(x)) |= exists x (S(x) ^ F(x))
    counter_b = None
    for S, A, F in product(domain_subsets, repeat=3):
        Q1 = all(imp(x in S, x in A) for x in U)
        obs = any((x in A) and (x in F) for x in U)
        conc = any((x in S) and (x in F) for x in U)
        if Q1 and obs and not conc:
            counter_b = {"S": S, "A": A, "F": F}
            break
    print(f"(b) Counter-model on {{a, b}}: {counter_b}")

    # (c) Derive forall x (S(x) -> ~B(x)) vs counter-model for forall x ~B(x)
    part_c_valid = True
    counter_c_strong = None
    for S, A, E, B in product(domain_subsets, repeat=4):
        Q1 = all(imp(x in S, x in A) for x in U)
        Q2 = all(imp(x in A, x in E) for x in U)
        Q4 = all(imp(x in E, x not in B) for x in U)
        conc_valid = all(imp(x in S, x not in B) for x in U)
        conc_strong = all(x not in B for x in U)
        if Q1 and Q2 and Q4:
            if not conc_valid:
                part_c_valid = False
            if not conc_strong and counter_c_strong is None:
                counter_c_strong = {"S": S, "A": A, "E": E, "B": B}
    print(f"(c) Q1, Q2, Q4 |= forall x (S(x) -> ~B(x)): {part_c_valid}")
    print(f"(c) Counter-model refuting forall x ~B(x): {counter_c_strong}")


if __name__ == "__main__":
    task1_packet_filtering()
    task2_normal_forms()
    task3_rules_of_inference()
    task4_predicates_quantifiers()
    task5_quantified_inference()
