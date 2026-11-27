# Smart prMA algorithm with one advice bit for range avoidance

For every $d\ge 1$ a deterministic polynomial-time algorithm with a promise-MA oracle and one bit of advice solves range avoidance for all size-$n^d$ circuits on infinitely many lengths $n$, asking only queries that satisfy the promise.

A promise problem $(\Pi_{\mathrm{yes}},\Pi_{\mathrm{no}})$ is in $\mathsf{prMA}$ if a deterministic polynomial-time $A(x,w,r)$ with $|w|,|r|\le\mathrm{poly}(|x|)$ satisfies: for $x\in\Pi_{\mathrm{yes}}$ some $w$ has $\Pr_r[A(x,w,r)\text{ accepts}]=1$, and for $x\in\Pi_{\mathrm{no}}$ every $w$ has acceptance probability at most $1/2$. A deterministic oracle algorithm with oracle $\Pi$ is smart if it never queries a string outside $\Pi_{\mathrm{yes}}\cup\Pi_{\mathrm{no}}$; with advice, correctness and smartness are required only under the correct advice string. A smart deterministic algorithm is single-valued: its output does not depend on how out-of-promise queries would be answered.

For every constant $d\ge 1$ there is a deterministic polynomial-time algorithm $\mathcal{A}$ with access to a $\mathsf{prMA}$ oracle and one advice bit $\{\alpha_n\}_{n\in\mathbb{N}}$ such that for infinitely many $n$: for every circuit $C:\{0,1\}^n\to\{0,1\}^{n+1}$ of size at most $n^d$, $\mathcal{A}(C,\alpha_n)$ is smart and outputs $y\in\{0,1\}^{n+1}\setminus\mathrm{Range}(C)$. In the uniform form, for every $\mathsf{P}$-uniform family $G_n:\{0,1\}^n\to\{0,1\}^{2n}$ of size at most $n^4$ ($n$ a power of two) there is a smart $\mathsf{FP}^{\mathsf{prMA}}/1$ algorithm that outputs a non-range string of $G_{n_i}$ on infinitely many lengths $n_i$ and asks no out-of-promise query on any power-of-two length.

## Expansion

The proof runs the iterative win-win paradigm. Brute force solves the instance $G_{n_0}$ in time $2^{O(n_0)}$. An instance-wise hardness-randomness tradeoff for functions computable in $\mathsf{P}^{\mathsf{NP}}$ with $r$ adaptive rounds of $\mathsf{NP}$ queries of witness length $s$ turns the solver for $G_{n_i}$ into a solver $\mathrm{Solve}$ for $G_{n_{i+1}}$, $n_{i+1}=n_i^C$, and a reconstruction procedure $\mathrm{Recon}$ in smart $\mathsf{P}^{\mathsf{prMA}}$: if $\mathrm{Solve}$ fails on $G_{n_{i+1}}$, then $\mathrm{Recon}$ recomputes, bit by bit, the previous solver's output while making only promise-satisfying queries. The construction of $\mathrm{Recon}$ uses the PCP theorem with low-degree self-correction, which is where non-relativizing techniques enter. Along each chain of lengths either some step fails, and the least failing index yields a good length solved by $\mathrm{Recon}$, or the solvers reach polynomial time with a $\mathsf{SAT}$ oracle; the advice bit records which case holds on the chosen length. Applying this to the truth-table generator, whose non-outputs are hard truth tables, and then Korten's $\mathsf{FP}^{\mathsf{NP}}$ reduction, which turns a circuit $C$ and a truth table of high circuit complexity into a string outside the range of $C$, gives the non-uniform statement.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/range-avoidance-problem.md)
- [The class MA (Merlin–Arthur)](../../complexity-classes/time-and-space-complexity-classes/ma.md)

## Proof depends on

- [Korten: solving Avoid yields hard truth tables](../range-avoidance-and-near-maximum-lower-bounds/korten-avoid-to-hard-truth-table.md)
- [Korten: constructing a hard truth table is APEPP-complete under P^NP reductions](../../complexity-classes/tfnp-hierarchies-and-avoidance/range-avoidance-and-explicit-constructions/korten-hard-truth-table-apepp-complete.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../../pcp-and-inapproximability/pcp-theorem.md)

## Sources

- Hanlin Ren and Ryan Williams, "Near-Maximum Circuit Lower Bounds for Exponential Time with Merlin-Arthur Queries", *IEEE Symposium on Foundations of Computer Science (FOCS)*, 2026, arXiv:2607.09963v1 (Theorem 1.2, Definition 2.1, Section 2.1, Theorems 4.1, 4.3 and 4.5, Lemma 4.4).
