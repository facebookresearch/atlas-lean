# ACC0-SAT algorithms with witness circuits contradict the nondeterministic time hierarchy

Suppose (i) every language in $\mathsf{NTIME}[2^n]$ has, for each yes-instance, a witness encoded by an $\mathsf{ACC}^0$ circuit of polynomial size (succinct witnesses), and (ii) satisfiability of $\mathsf{ACC}^0$ circuits of size $2^{n^{\varepsilon}}$ is decidable in time $2^{n-\omega(\log n)}$. Then every language in $\mathsf{NTIME}[2^n]$ is in $\mathsf{NTIME}[2^n/n^{c}]$ for some $c>0$, contradicting the nondeterministic time hierarchy. Combined with Williams's $\mathsf{ACC}^0$-SAT algorithm this yields $\mathsf{NEXP}\not\subseteq\mathsf{ACC}^0$.

## Proof sketch

Reduce an $\mathsf{NTIME}[2^n]$ language to succinct 3SAT with $\mathsf{ACC}^0$-computable clause decoders; guess a small $\mathsf{ACC}^0$ witness circuit $W$ and verify it by running the fast SAT algorithm on $\mathrm{Bad}_{D,W}$, which takes time $2^n/n^{c}$ altogether.

## Depends on

- [Nondeterministic time classes](../../../complexity-classes/time-and-space-complexity-classes/ntime.md)
- [The class $\mathsf{ACC}^0$](../../../complexity-classes/time-and-space-complexity-classes/acc0.md)
- [Verifying a succinct satisfying assignment by circuit unsatisfiability](verifying-succinct-assignments-by-circuit-unsat.md)

## Proof depends on

- [Verifying a succinct satisfying assignment by circuit unsatisfiability](verifying-succinct-assignments-by-circuit-unsat.md)
- [Nondeterministic time hierarchy](../../../hierarchy-theorems-and-barriers/nondet-time-hierarchy.md)
- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM, 2014.
- Ryan Williams, "Improving Exhaustive Search Implies Superpolynomial Lower Bounds", Author's full version, 2010.
