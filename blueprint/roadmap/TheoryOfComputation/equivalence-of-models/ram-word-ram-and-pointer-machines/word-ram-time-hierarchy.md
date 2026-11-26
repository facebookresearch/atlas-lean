# A time hierarchy for the word RAM

For every time-constructible, polynomially bounded $T$ with $T(n)\ge n$, there is a constant $d$, independent of $T$, and a problem decided by one fixed word-RAM program over the additive basis within $O(T(n)^{d})$ instructions at every word size $w\ge k\log n$ (for a constant $k>0$), but by no word-RAM program within $O(T(n))$ instructions at any such family of word sizes. That is, $\mathsf{RAMTIME}(T)\subsetneq\mathsf{RAMTIME}(T^{d})$.

## Proof sketch

Translate to multi-tape machines: word-RAM time $T$ is within Turing time $\mathrm{poly}(T)$, apply the deterministic time hierarchy there, and simulate the separating machine back on the word RAM in linear overhead.

## Depends on

- [The word-RAM model](../../fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Polynomial time on the word RAM equals polynomial time on multi-tape Turing machines](word-ram-turing-polynomial-invariance.md)
- [Deterministic time hierarchy: quadratic versus linear time](../../hierarchy-theorems-and-barriers/time-hierarchy-theorem/time-hierarchy.md)

## Sources

- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 1973.
