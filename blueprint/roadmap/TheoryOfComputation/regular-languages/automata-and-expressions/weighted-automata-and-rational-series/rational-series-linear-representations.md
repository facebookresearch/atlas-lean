# Linear representations and rational series of bounded dimension

Let $K$ be a semiring and $\Sigma$ an alphabet. A **formal power series** is a map $f:\Sigma^*\to K$. A **linear representation of dimension $n$** is a triple $(\lambda,\mu,\rho)$ with $\lambda\in K^{1\times n}$, $\rho\in K^{n\times1}$ and a monoid morphism $\mu:\Sigma^*\to K^{n\times n}$; it realizes $f(w)=\lambda\,\mu(w)\,\rho$. Such representations are exactly weighted finite automata with $n$ states. $\mathrm{Rat}_{\le n}$ denotes the series realized in dimension at most $n$; a series is **rational** if it lies in some $\mathrm{Rat}_{\le n}$ (Schützenberger: equivalently, it is built from polynomials by sum, Cauchy product and star).

## Depends on

- [Pushdown automaton](../../../context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)

## Sources

- Marcel-Paul Schützenberger, "On the Definition of a Family of Automata", Information and Control 4, 1961.
- Jean Berstel and Christophe Reutenauer, "Noncommutative Rational Series with Applications", Cambridge University Press, 2011.
