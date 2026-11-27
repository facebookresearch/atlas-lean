# Under the Aaronson-Ambainis conjecture, total functions on most oracles admit no superpolynomial quantum speedup

Assume the Aaronson-Ambainis conjecture. Then for every quantum algorithm $Q$ making $T$ queries to an $N$-bit oracle and all $\varepsilon, \delta > 0$, there is a deterministic classical algorithm making $\mathrm{poly}(T, 1/\varepsilon, 1/\delta)$ queries that approximates the acceptance probability of $Q$ within $\varepsilon$ on all but a $\delta$ fraction of oracles. Consequently, if $\mathrm{P} = \mathrm{P}^{\#\mathrm{P}}$ then $\mathrm{BQP}^{\mathcal{O}} \subseteq \mathrm{AvgP}^{\mathcal{O}}$ with probability $1$ over a random oracle $\mathcal{O}$.

## Proof sketch

The acceptance probability is a bounded polynomial of degree $2T$ in the oracle bits. Repeatedly query the most influential variable guaranteed by the conjecture: each query decreases the expected variance by a polynomial amount, so after polynomially many queries the restricted polynomial is nearly constant on most oracles, and its value is estimated classically.

## Depends on

- [The Aaronson-Ambainis conjecture on influential variables of bounded polynomials](aaronson-ambainis-influence-conjecture.md)

## Sources

- Scott Aaronson, Andris Ambainis, "The need for structure in quantum speedups", Theory of Computing 10 (2014); arXiv:0911.0996.
