# AM ⊆ NP/poly

$\mathsf{AM}\subseteq\mathsf{NP}/\mathrm{poly}$.

## Proof sketch

Amplify the error of the AM protocol below $2^{-n-1}$; by a union bound a single random string of Arthur is good for all $2^n$ inputs of length $n$ simultaneously. Fixing it as advice turns the protocol into an NP verifier with Merlin's reply as the witness.

## Depends on

- [The class $\mathsf{AM}$ (Arthur–Merlin)](../../../complexity-classes/time-and-space-complexity-classes/am.md)
- [NP/poly](../../../complexity-classes/structural-complexity/boolean-hierarchy-and-polynomial-hierarchy-collapses/np-with-polynomial-advice.md)

## Proof depends on

- [Babai–Moran: AM[k] = AM for every constant k](am-round-collapse.md)

## Sources

- László Babai and Shlomo Moran, "Arthur–Merlin Games: A Randomized Proof System, and a Hierarchy of Complexity Classes", Journal of Computer and System Sciences 36(2), 254–276, 1988.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 7 (Exercise 7.5 of the January 2007 web draft: $\mathsf{BP}\cdot\mathsf{NP}\subseteq\mathsf{NP}/\mathrm{poly}$, and $\mathsf{BP}\cdot\mathsf{NP}=\mathsf{AM}$).
