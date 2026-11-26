# Collision finders and accessible average max-entropy

Let $F = (F_n)$ be a polynomial-time function family on uniform inputs. An *$F$-collision finder* is a randomized algorithm $A$ that on input $x$ outputs an element of the fiber $F^{-1}(F(x))$ (any randomized map can be sanitized into one by replacing outputs outside the fiber by $x$). $F$ has *accessible average max-entropy at most $k(n)$* if for every probabilistic polynomial-time $F$-collision finder $A$ there is a family of sets $L(z) \subseteq F^{-1}(z)$ such that, for all large $n$,

$$\mathbb{E}_{x}\bigl[\log_2 |L(F(x))|\bigr] \le k(n) \quad\text{and}\quad \Pr_{x, \text{coins}}\bigl[A(x) \notin L(F(x))\bigr] \text{ is negligible}.$$

$F$ has *inaccessible entropy* $\Delta(n)$ if its accessible average max-entropy is at most $H(X \mid F(X)) - \Delta(n)$.

## Depends on

- [Real sample entropy of a function](real-sample-entropy.md)
- [Probabilistic polynomial-time Turing machines](../../../ComputerScience/cryptography/security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)

## Sources

- I. Haitner, T. Holenstein, O. Reingold, S. Vadhan and H. Wee, "Inaccessible Entropy II: IE Functions and Universal One-Way Hashing", Theory of Computing 16, 2020.
