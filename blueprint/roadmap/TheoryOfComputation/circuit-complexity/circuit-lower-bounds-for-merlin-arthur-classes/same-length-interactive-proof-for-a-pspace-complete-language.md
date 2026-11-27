# Same-length interactive proof for a PSPACE-complete language

Some $\mathsf{PSPACE}$-complete language has a function-restricted interactive proof whose verifier queries its oracle only on strings of the input's length: with the language itself as oracle it accepts every member, and it rejects every non-member with probability at least $1/2$ whatever the oracle.

There are a $\mathsf{PSPACE}$-complete language $L$ and a probabilistic polynomial-time oracle Turing machine $M$ such that for every input $x$:

1. $M$ asks oracle queries only of length $|x|$;
2. if $M$ is given $L$ as oracle and $x\in L$, then $M$ accepts with probability $1$;
3. if $x\notin L$, then for every oracle $M$ rejects with probability at least $1/2$.

Without the restriction on the length of oracle queries the statement holds for every $\mathsf{PSPACE}$-complete language.

## Expansion

In the language of program checking, $L$ has a function-restricted interactive proof in which the prover answers only questions of the same length as the input. The statement follows from work on interactive proofs by Lund, Fortnow, Karloff and Nisan, by Shamir, by Trevisan and Vadhan, and by Fortnow and Santhanam. Without the length restriction it gives the Karp–Lipton-style result that $\mathsf{PSPACE}\subseteq\mathrm{SIZE}(\mathrm{poly})$ implies $\mathsf{PSPACE}=\mathsf{MA}$: Merlin sends circuits for every query length and Arthur runs $M$ with them as the oracle. With the restriction, a single circuit for the input length suffices, which is what padding arguments with one bit of advice need.

## Depends on

- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)
- [The class IP](../../complexity-classes/time-and-space-complexity-classes/ip.md)

## Proof depends on

- [IP = PSPACE (Shamir)](../../randomized-and-quantum-complexity/ip-eq-pspace.md)

## Sources

- Rahul Santhanam, "Circuit Lower Bounds for Merlin-Arthur Classes", *SIAM Journal on Computing* 39(3), 2009, https://doi.org/10.1137/070702680 (Lemma 12 and the discussion following it, Section 3; numbering of the ECCC Report TR07-005 edition read).
