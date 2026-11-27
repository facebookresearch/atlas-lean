# One bit of advice decides an undecidable language

There is a language $L\subseteq\{0,1\}^*$ that is in $\mathsf{P}/1$ (one advice bit per input length) but is undecidable; moreover $L$ can be chosen so that membership depends only on the input length. In fact every 'length language' $\{x : |x|\in U\}$ with $U\subseteq\mathbb{N}$ arbitrary is in $\mathsf{P}/1$.

## Proof sketch

Take $U$ undecidable (e.g. the codes of halting machines) and let the advice bit at length $n$ be $[n\in U]$; the machine outputs its advice bit. The language $\{x:|x|\in U\}$ is undecidable since $U$ many-one reduces to it via $n\mapsto 0^n$.

## Depends on

- [Polynomial time with exact-length advice](exact-length-advice-classes.md)
- [Halting set](../../../degrees-and-hierarchies/turing-reducibility/halting-set.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Theorem 3.7.
