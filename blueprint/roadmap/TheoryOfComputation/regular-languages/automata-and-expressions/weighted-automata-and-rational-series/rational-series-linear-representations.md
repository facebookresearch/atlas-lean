# Rational series of bounded dimension

Let $K$ be a [semiring](semirings-and-formal-power-series.md) and $\Sigma$ an alphabet. $\mathrm{Rat}_{\le n}$ is the set of series $f:\Sigma^*\to K$
defined by a [linear representation](linear-representations-of-recognizable-series.md) $(\lambda,\mu,\rho)$ of dimension at most $n$, that is
$f(w)=\lambda\,\mu(w)\,\rho$ with $\lambda\in K^{1\times n}$, $\rho\in K^{n\times1}$ and a monoid morphism $\mu:\Sigma^*\to K^{n\times n}$;
equivalently, the behaviors of weighted automata with at most $n$ states. By the
[Kleene–Schützenberger theorem](kleene-schutzenberger-theorem.md), the union of the $\mathrm{Rat}_{\le n}$ is the set of [rational series](rational-series.md).

## Depends on

- [Semirings and formal power series on a free monoid](semirings-and-formal-power-series.md)
- [Linear representations of recognizable series](linear-representations-of-recognizable-series.md)

## Sources

- Marcel-Paul Schützenberger, "On the Definition of a Family of Automata", Information and Control 4, 1961.
- Jean Berstel and Christophe Reutenauer, "Noncommutative Rational Series with Applications", Cambridge University Press, 2011.
