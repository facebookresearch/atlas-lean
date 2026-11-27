# Alternating logarithmic space equals P

$\mathsf{AL}=\mathsf{ASPACE}(\log n)=\mathsf{P}$, with no constructibility assumptions.

## Proof sketch

$\mathsf{AL}\subseteq\mathsf{P}$ is the case $s=\log n$ of the exponential-time simulation of alternating space. For $\mathsf{P}\subseteq\mathsf{AL}$, the step count $(n+2)^D$ of a polynomial-time decider is computable in logarithmic space, and the alternating machine plays the local circuit-value game on its tableau, keeping only $O(\log n)$-bit coordinates and a claimed value.

## Depends on

- [Alternating time and space classes ATIME, ASPACE, AP, APSPACE and AL](alternating-time-and-space-classes.md)
- [The complexity class P](../../the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Alternating space s is contained in deterministic time 2^{O(s)}](aspace-in-dtime-exponential.md)
- [Deterministic time 2^{O(s)} is contained in alternating space s](dtime-exponential-in-aspace.md)
- [The Circuit Value Problem is P-complete](../../../completeness-other-classes/circuit-value-problem/cvp-p-complete.md)

## Sources

- Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer, "Alternation", Journal of the ACM 28(1), 1981.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
