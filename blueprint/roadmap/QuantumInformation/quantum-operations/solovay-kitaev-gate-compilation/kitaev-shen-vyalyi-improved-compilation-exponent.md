# Kitaev-Shen-Vyalyi: compilation with exponent arbitrarily close to three

For every universal gate set $\mathcal{G} \subset \mathrm{SU}(d)$ and every $\delta > 0$, every $U \in \mathrm{SU}(d)$ is approximated within $\varepsilon$ by a product of $O(\log^{3 + \delta}(1/\varepsilon))$ gates from $\mathcal{G}$, computable in time polylogarithmic in $1/\varepsilon$.

## Proof sketch

Refine the Solovay-Kitaev recursion using the Lie algebra structure: approximate the logarithm of the residual unitary by a sum of commutators of elements of a fine net, so that each recursion level improves accuracy from $\varepsilon$ to $\varepsilon^{2}$-like powers while multiplying the word length by a factor that tends to the optimal ratio, giving exponent $3 + \delta$.

## Depends on

- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)

## Proof depends on

- [Solovay-Kitaev theorem](solovay-kitaev-theorem.md)

## Sources

- Alexei Kitaev, Alexander Shen, Mikhail Vyalyi, "Classical and Quantum Computation", Graduate Studies in Mathematics 47, AMS (2002).
- Christopher M. Dawson, Michael A. Nielsen, "The Solovay-Kitaev algorithm", Quantum Information and Computation 6(1) (2006); arXiv:quant-ph/0505030.
