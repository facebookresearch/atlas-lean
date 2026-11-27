# Kabanets–Cai: if MCSP is in BPP, there are no one-way functions

If $\mathrm{MCSP} \in \mathsf{BPP}$, then for every keyed function family $F = \{F_k : \{0,1\}^n \to \{0,1\}^n\}_{k \in \{0,1\}^n}$ with key length and input length $n$ (as in Katz–Lindell's pseudorandom functions), computable in time polynomial in $n$, some probabilistic polynomial-time oracle adversary distinguishes $F_k$ for a uniform key $k$ from a uniformly random function $\{0,1\}^n \to \{0,1\}^n$ with advantage at least $1/4$ for all large $n$. Consequently no pseudorandom function family exists, and hence no one-way function exists. Kabanets and Cai state the non-uniform form (their Theorem 2: if $\mathrm{MCSP} \in \mathsf{P/poly}$, there is no strong pseudorandom generator in $\mathsf{P/poly}$). The uniform form follows from the same natural-proofs distinguisher, run with a $\mathsf{BPP}$ decider for $\mathrm{MCSP}$ whose error is made exponentially small, together with the uniform construction of pseudorandom functions from one-way functions. Allender, Buhrman, Koucký, van Melkebeek and Ronneburger give the corresponding inversion result: with an oracle for a polynomially dense set of strings of high $\mathrm{KT}$ complexity, a role they note $\mathrm{MCSP}$ can play, a probabilistic polynomial-time machine inverts any polynomial-time computable function on a noticeable fraction of its inputs (their Theorem 24 and Lemma 25).

## Proof sketch

The adversary queries the oracle on all inputs of a block of $m = O(\log n)$ bits to obtain a truth table of length $2^m$, and asks the MCSP decider whether it has circuits of size $n^c$. The truth table of $F_k$ restricted to such a block has small circuits, while a random function's truth table almost surely has circuit complexity near $2^m/m$ by counting.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../circuit-complexity/minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [Asymptotic PRF security relative to a class of distinguishers](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/prfsecure.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [One-way functions imply adaptively secure pseudorandom functions](../hard-core-predicates-and-stretch/one-way-functions-imply-pseudorandom-functions.md)

## Sources

- V. Kabanets and J.-Y. Cai, "Circuit Minimization Problem", Proceedings of the 32nd Annual ACM Symposium on Theory of Computing (STOC), 2000, Theorem 2.
- E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek and D. Ronneburger, "Power from Random Strings", SIAM Journal on Computing 35(6), 2006 (ECCC TR02-028, Section 5: Theorem 24, the HILL inversion with an oracle, and Lemma 25, the dense-set distinguisher).
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 2nd edition, CRC Press, 2014, Definition 3.25.
