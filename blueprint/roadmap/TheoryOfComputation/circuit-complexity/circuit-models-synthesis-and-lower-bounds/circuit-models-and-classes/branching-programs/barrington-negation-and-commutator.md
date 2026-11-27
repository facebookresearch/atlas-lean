# Negation and commutator steps of Barrington's construction

Let $G$ be a group. (i) If a program $P$ $\sigma$-computes $f$, then $P$ followed by the constant instruction $\sigma^{-1}$ $\sigma^{-1}$-computes $\neg f$. (ii) If $P$ $\sigma$-computes $f$ and $Q$ $\tau$-computes $g$, then the program $P\,Q\,P^{-1}\,Q^{-1}$ (where $P^{-1}$ reverses $P$ and inverts each instruction) $[\sigma,\tau]$-computes $f\wedge g$, where $[\sigma,\tau]=\sigma\tau\sigma^{-1}\tau^{-1}$. (iii) Conjugating every instruction by $\pi$ turns a $\sigma$-computation into a $\pi\sigma\pi^{-1}$-computation. Since $S_5$ contains $5$-cycles whose commutator is again a $5$-cycle, iterating these steps shows that every function computed by a De Morgan formula of depth $d$ (negations at the leaves) is computed by a permutation branching program of width $5$ and length at most $4^{d}$, constant instructions being absorbed into a neighbouring instruction.

## Proof sketch

Evaluation is a homomorphism, so $P^{-1}$ evaluates to the inverse of $P$'s value; if $f(x)=0$ or $g(x)=0$ one factor pair cancels in the commutator. Any two $5$-cycles are conjugate in $S_5$, so conjugation (step (iii)) turns a $5$-cycle computation into one for any prescribed $5$-cycle; an AND gate quadruples the length and an OR gate is handled through De Morgan's law with steps (i) and (ii).

## Depends on

- [Programs over a monoid and bounded-width branching programs](monoid-programs.md)

## Sources

- David A. Barrington, "Bounded-width polynomial-size branching programs recognize exactly those languages in NC^1", Journal of Computer and System Sciences 38(1), 150–164, 1989.
- David A. Mix Barrington and Denis Thérien, "Finite Monoids and the Fine Structure of NC^1", Journal of the ACM 35(4), 941–952, 1988.
