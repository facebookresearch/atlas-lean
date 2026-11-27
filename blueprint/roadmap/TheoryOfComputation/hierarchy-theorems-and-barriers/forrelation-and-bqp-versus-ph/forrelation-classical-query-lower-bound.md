# Aaronson-Ambainis: Forrelation is optimally hard for classical queries

Every bounded-error randomized algorithm for the Forrelation problem makes $\Omega(\sqrt N / \log N)$ queries. Conversely, every quantum algorithm making $t$ queries to an $N$-bit input can be simulated by a randomized algorithm making $O(N^{1 - 1/(2t)})$ queries, so the separation of $1$ versus $\tilde\Omega(\sqrt N)$ is essentially optimal for one-query quantum algorithms.

## Proof sketch

For the lower bound, consider $f$ uniform versus $f$ Gaussian-rounded with $g = \mathrm{sgn}(\hat f)$; any $q$ classical queries see marginals of a Gaussian vector whose covariance between queried points is $O(1/\sqrt N)$ per pair, and a careful argument bounds the distinguishing advantage by $\tilde O(q/\sqrt N)$. The simulation uses that the acceptance probability of a $t$-query algorithm is a polynomial of degree $2t$, which can be estimated by sampling its terms with random restrictions.

## Depends on

- [Forrelation of two Boolean functions](forrelation-of-two-boolean-functions.md)

## Proof depends on

- [A one-query quantum algorithm estimating forrelation](one-query-quantum-algorithm-for-forrelation.md)

## Sources

- Scott Aaronson, Andris Ambainis, "Forrelation: a problem that optimally separates quantum from classical computing", SIAM Journal on Computing 47(3) (2018), STOC (2015); arXiv:1411.5729.
