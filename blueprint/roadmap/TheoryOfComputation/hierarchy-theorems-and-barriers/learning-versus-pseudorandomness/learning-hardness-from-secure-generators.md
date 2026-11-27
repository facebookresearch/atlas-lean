# Subexponentially secure generators rule out learners with small circuits for polynomial-size circuits

A family of length-doubling generators $G_k : \{0,1\}^k \to \{0,1\}^{2k}$ is subexponentially secure with exponent $d$ if for all large $k$ and every $m$ with $m^d \le k$, no De Morgan circuit of size $2^m$ distinguishes $G_k(\text{uniform})$ from uniform with advantage more than $2^{-m}$. A learner has circuit tests of size $t$ with $q$ queries if it agrees with a learner making at most $q$ queries and, for every seed and point $z$, the test "run the learner on a truth table and compare its hypothesis with the table at $z$" is a circuit with at most $t$ gates on truth tables.

Let $G$ be subexponentially secure and have polynomial circuit complexity. Then there is a polynomially bounded $s$ such that:

1. for every $c$, for all large $n$, every learner with circuit tests of size at most $2^{cn}$ and $q$ queries that learns all functions on $n$ bits of circuit size at most $s(n)$, with error $\varepsilon \le 1$ and confidence $1-\delta$, satisfies $(1-\delta)(1-\varepsilon) \le \frac12 + \frac{q}{2^{n+1}} + 2^{-cn}$;
2. for every $c$ and every $\varepsilon \le 1$, $\delta \ge 0$ with $(1-\delta)(1-\varepsilon) > 3/4$, for all large $n$, no learner with at most $2^{n-1}$ adaptive queries and circuits of at most $2^{cn}$ gates in total learns the functions on $n$ bits of circuit size at most $s(n)$ with error $\varepsilon$ and confidence $1-\delta$.

## Proof sketch

The GGM functions built from $G$ with keys of polynomial length have circuits of size $n(C + 4k) + 2$, which defines $s$, and inherit security against truth-table circuit tests from $G$ by a hybrid argument. A learner with small circuit tests yields a test of comparable size whose advantage is at least $(1-\delta)(1-\varepsilon) - \frac12 - q/2^{n+1}$ by the distinguishing lemma, contradicting security. Adaptive circuits of size $S$ give circuit tests of size $S + q(2^n(2n+3)+1) + 7$, still $2^{O(n)}$.

## Depends on

- [Learners computed by small circuits, with adaptive or non-adaptive membership queries](../../circuit-complexity/learning-under-the-uniform-distribution/learners-computed-by-small-circuits.md)
- [Pseudorandom generators against circuits](../../pseudorandomness-and-one-way-functions/derandomization/pseudorandom-generators-against-circuits.md)
- [The GGM construction: pseudorandom generators give pseudorandom functions](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/the-ggm-construction-pseudorandom-generators.md)

## Proof depends on

- [A membership-query learner for a keyed family distinguishes it from random functions](learners-distinguish-pseudorandom-functions.md)
- [The GGM construction: pseudorandom generators give pseudorandom functions](../../../ComputerScience/cryptography/symmetric-key/pseudorandom-functions/the-ggm-construction-pseudorandom-generators.md)

## Sources

- Leslie G. Valiant, "A Theory of the Learnable", Proceedings of the 16th Annual ACM Symposium on Theory of Computing, 1984.
- Oded Goldreich, Shafi Goldwasser and Silvio Micali, "How to Construct Random Functions", Journal of the ACM 33(4), 1986.
- Alexander A. Razborov and Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences, 1997.
