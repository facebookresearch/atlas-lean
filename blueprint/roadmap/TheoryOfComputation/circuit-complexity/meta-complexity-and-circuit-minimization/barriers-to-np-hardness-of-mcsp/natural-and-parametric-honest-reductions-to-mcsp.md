# Natural and parametric honest reductions to MCSP

Two restrictions on reductions to MCSP: a reduction is *natural* when the size parameter of every produced instance depends only on the input length, and *parametric honest* when every size parameter is at least $|x|^{\varepsilon}$. Textbook NP-completeness reductions, such as those from SAT to 3-SAT and from 3-SAT to Vertex Cover, are natural.

**Natural many-one reductions (Kabanets–Cai).** A Karp reduction $R$ from $A$ to $B$ is *natural* if for every instance $I$ of $A$ the size of $R(I)$, and every numerical parameter of $R(I)$, depends only on $|I|$, and $|I|$ and $|R(I)|$ are polynomially related. For a reduction to MCSP, the produced instance $(T,s)$ then has $|T|$ and $s$ determined by $|I|$.

**Parametric honest reductions (Hitchcock–Pavan).** An instance $(x,k)$ of MCSP is $\ell$-large if $k\ge\ell$. A polynomial-time many-one reduction $f$ from $L$ to MCSP is *parametric honest* if there is $\varepsilon>0$ such that $f(x)$ is $|x|^{\varepsilon}$-large for every $x$. The same notion is defined for strong nondeterministic reductions, whose every non-rejecting output must be $|x|^{\varepsilon}$-large.

**Turing versions (Saks–Santhanam).** A polynomial-time Turing reduction from $L$ to MCSP or MKtP is *parametric honest* if there is $\varepsilon>0$ such that every query made on input $x$ has parameter at least $|x|^{\varepsilon}$, and *natural* if the parameter of every query made on input $x$ depends only on $|x|$. In both cases the condition is only required while previous queries are answered correctly.

## Expansion

The reductions from SAT to 3-SAT and from 3-SAT to Vertex Cover are natural, and Masek's reduction from SAT to minimum DNF size is natural. Parametric honesty is not implied by ordinary honesty, which only bounds output length from below. The Turing form of naturalness is slightly weaker than the Kabanets–Cai form for many-one reductions, since it constrains the parameter but not the output length; it is incomparable with parametric honesty, which lets the parameter vary within a range.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [The minimum Kt problem MKtP](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/the-minimum-kt-problem.md)
- [Polynomial-time Turing (Cook) reduction](../../../randomized-and-quantum-complexity/interactive-proofs/closure-of-ip-under-reductions/polynomial-time-turing-reduction.md)

## Proof depends on

None.

## Sources

- Valentine Kabanets, Jin-Yi Cai, "Circuit Minimization Problem", *Proceedings of the 32nd Annual ACM Symposium on Theory of Computing (STOC)*, 2000, https://doi.org/10.1145/335305.335314 (Section 3.1, numbering of the full version dated 15 November 1999, ECCC TR99-045).
- John Matthew Hitchcock, A. Pavan, "On the NP-Completeness of the Minimum Circuit Size Problem", *Foundations of Software Technology and Theoretical Computer Science (FSTTCS)*, 2015, https://doi.org/10.4230/LIPIcs.FSTTCS.2015.236 (Definitions 2.2, 2.6 and 2.7).
- Michael Saks, Rahul Santhanam, "Circuit Lower Bounds from NP-Hardness of MCSP Under Turing Reductions", *Computational Complexity Conference (CCC)*, 2020, https://doi.org/10.4230/LIPIcs.CCC.2020.26 (Definitions 5 and 6).
