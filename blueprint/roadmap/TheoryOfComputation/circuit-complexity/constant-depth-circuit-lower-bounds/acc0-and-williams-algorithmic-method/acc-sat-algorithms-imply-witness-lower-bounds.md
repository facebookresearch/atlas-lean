# ACC0-SAT algorithms with witness circuits contradict the nondeterministic time hierarchy

Suppose (i) $\mathsf{P}$ has polynomial-size $\mathsf{ACC}^0$ circuits; (ii) every satisfiable formula produced by the standard reduction from a language in $\mathsf{NTIME}[2^n]$ to Succinct 3SAT has a satisfying assignment encoded by a polynomial-size $\mathsf{ACC}^0$ circuit (succinct witnesses); and (iii) satisfiability of $\mathsf{ACC}^0$ circuits with $n+k\log n$ inputs, depth bounded by a constant and polynomial size is decidable in time $O(2^n/n^{k})$ for a sufficiently large constant $k$. Then every language in $\mathsf{NTIME}[2^n]$ is in $\mathsf{NTIME}[o(2^n)]$, contradicting the nondeterministic time hierarchy. If $\mathsf{NTIME}[2^n]$ had polynomial-size $\mathsf{ACC}^0$ circuits, (i) and (ii) would hold (by the Impagliazzo–Kabanets–Wigderson easy-witness argument), so combined with Williams's $\mathsf{ACC}^0$-SAT algorithm, which gives (iii), this yields that $\mathsf{NTIME}[2^n]$, and hence $\mathsf{NEXP}$, does not have polynomial-size $\mathsf{ACC}^0$ circuits.

## Proof sketch

Reduce $L\in\mathsf{NTIME}[2^n]$ to Succinct 3SAT: an input $x$ yields in polynomial time a clause-decoder circuit $C_x$ with $n+c\log n$ inputs. Since $C_x$ need not be an $\mathsf{ACC}^0$ circuit, guess an equivalent $\mathsf{ACC}^0$ circuit $C'_x$ (it exists by (i)) together with $\mathsf{ACC}^0$ circuits describing the gates of $C_x$ and their values, and verify the guesses with the fast SAT algorithm. Then guess a small $\mathsf{ACC}^0$ witness circuit $W$ (it exists by (ii)) and accept iff $\mathrm{Bad}_{C'_x,W}$ is unsatisfiable, again by the SAT algorithm; the whole procedure takes $O(2^n/n^{k})+\mathrm{poly}(n)$ nondeterministic time.

## Depends on

- [Nondeterministic time classes](../../../complexity-classes/time-and-space-complexity-classes/ntime.md)
- [The class $\mathsf{ACC}^0$](../../../complexity-classes/time-and-space-complexity-classes/acc0.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [Verifying a succinct satisfying assignment by circuit unsatisfiability](verifying-succinct-assignments-by-circuit-unsat.md)

## Proof depends on

- [Nondeterministic time hierarchy](../../../hierarchy-theorems-and-barriers/nondet-time-hierarchy.md)
- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)
- [Impagliazzo–Kabanets–Wigderson easy witness lemma for NEXP](../../algorithmic-method-nqp-and-almost-everywhere-bounds/easy-witness-ikw.md)
- [Williams's faster-than-brute-force algorithm for ACC0-SAT](williams-acc0-sat-algorithm.md)

## Sources

- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM 61(1), Article 2, 2014 (Fact 3.1, Lemma 3.1, Theorems 5.1–5.2, Lemma 5.1 and the proof of Theorem 1.1).
- Ryan Williams, "Improving Exhaustive Search Implies Superpolynomial Lower Bounds", SIAM Journal on Computing 42(3), 2013 (STOC 2010).
