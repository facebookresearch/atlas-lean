# Chen–Lyu–Williams: almost-everywhere ACC0 lower bounds for E^NP

There is a function $f \in \mathrm{E}^{\mathrm{NP}} = \mathrm{DTIME}^{\mathrm{NP}}[2^{O(n)}]$ such that for every $d, m$, every sufficiently large input length $n$, and every $\varepsilon = o(1)$, no $\mathrm{AC}^0[m]$ circuit of depth $d$ and size $2^{n^{\varepsilon}}$ agrees with $f$ on more than a $\frac{1}{2} + 2^{-n^{\varepsilon}}$ fraction of inputs. In particular $\mathrm{E}^{\mathrm{NP}} \not\subseteq \mathrm{i.o.}\text{-}\mathrm{ACC}^0$. More generally, every non-trivial derandomization algorithm for a class $\mathcal{C}$ yields an $\mathrm{E}^{\mathrm{NP}}$ function that is almost-everywhere average-case hard for $\mathcal{C}$.

## Proof sketch

Replace diagonalization against nondeterministic time by a constructive version of the Fortnow-Santhanam nondeterministic time hierarchy: for every weak nondeterministic algorithm (with smaller running time and short witnesses), a refuter algorithm constructs, at every large input length, inputs on which it fails to decide the hard language. Combining this refuter with the non-trivial derandomization (to check guessed succinct witnesses) yields an almost-everywhere worst-case hard function in $\mathrm{E}^{\mathrm{NP}}$; an XOR lemma based on approximate linear sums, together with PCPs of proximity, extends the bound to the average case.

## Depends on

- [Infinitely-often versus almost-everywhere circuit lower bounds](almost-everywhere-lower-bound.md)
- [Non-trivial satisfiability and derandomization algorithms for a circuit class](nontrivial-circuit-analysis.md)

## Proof depends on

- [Murray–Williams: NQP is not contained in ACC0](murray-williams-nqp-acc.md)

## Sources

- L. Chen, X. Lyu, R. Williams, "Almost-everywhere circuit lower bounds from non-trivial derandomization", FOCS (2020), ECCC TR20-150.
- L. Chen, R. Williams, "Stronger connections between circuit analysis and circuit lower bounds, via PCPs of proximity", CCC (2019).
- L. Chen, H. Ren, "Strong average-case circuit lower bounds from non-trivial derandomization", STOC (2020); SIAM Journal on Computing 51 (2022).
- L. Fortnow, R. Santhanam, "New non-uniform lower bounds for uniform classes", CCC (2016).
