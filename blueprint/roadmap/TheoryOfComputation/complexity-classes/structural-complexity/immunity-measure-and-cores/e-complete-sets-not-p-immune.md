# Berman: E-complete sets are not P-immune

Every language that is $\mathsf{E}$-complete (or $\mathsf{EXP}$-complete) under polynomial-time many-one reductions has an infinite subset in $\mathsf{P}$, and so does its complement. In particular such sets are not $\mathsf{P}$-bi-immune, in contrast with the existence of $\mathsf{P}$-bi-immune sets in $\mathsf{E}$.

## Proof sketch

Reduce to the complete set $A$ a language $K\in\mathsf{E}$ constructed so that the reduction $f$ is forced to be length-increasing infinitely often on a polynomial-time recognizable set where $K$ is trivial; the images of those points form an infinite polynomial-time subset of $A$ (or of $\overline{A}$).

## Depends on

- [P-immune and P-bi-immune sets; complexity cores](p-immune-sets-and-cores.md)
- [The class E](../../time-and-space-complexity-classes/e.md)

## Proof depends on

- [Balcázar–Schöning: E contains P-bi-immune sets](p-bi-immune-set-in-e.md)

## Sources

- Leonard Berman, "On the structure of complete sets: almost everywhere complexity and infinitely often speedup", 17th Annual Symposium on Foundations of Computer Science, 1976.
