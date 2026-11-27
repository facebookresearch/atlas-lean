# Negation and commutator steps of Barrington's construction

Let $G$ be a group. (i) If a program $P$ $\sigma$-computes $f$, then $P$ followed by the constant instruction $\sigma^{-1}$ $\sigma^{-1}$-computes $\neg f$. (ii) If $P$ $\sigma$-computes $f$ and $Q$ $\tau$-computes $g$, then the program $P\,Q\,P^{-1}\,Q^{-1}$ (where $P^{-1}$ reverses $P$ and inverts each instruction) $[\sigma,\tau]$-computes $f\wedge g$, where $[\sigma,\tau]=\sigma\tau\sigma^{-1}\tau^{-1}$. (iii) Conjugating every instruction by $\pi$ turns a $\sigma$-computation into a $\pi\sigma\pi^{-1}$-computation. Since $S_5$ contains $5$-cycles whose commutator is again a $5$-cycle, iterating these steps shows that every function computed by a De Morgan formula of depth $d$ is computed by a permutation branching program of width $5$ and length $4^{d}$.

## Proof sketch

Evaluation is a homomorphism, so $P^{-1}$ evaluates to the inverse of $P$'s value; if $f(x)=0$ or $g(x)=0$ one factor pair cancels in the commutator. Conjugation adjusts the target cycle at each gate.

## Depends on

- [Programs over a monoid and bounded-width branching programs](monoid-programs.md)

## Sources

- David A. Barrington, "Bounded-width polynomial-size branching programs recognize exactly those languages in NC^1", Journal of Computer and System Sciences 38(1), 1989.
- David A. Mix Barrington and Denis Thérien, "Finite Monoids and the Fine Structure of NC^1", Journal of the ACM 35(4), 1988.
