# Learning by inverting the labelling map of a keyed family (Occam form)

Let $F : \kappa \to (\{0,1\}^n \to \{0,1\})$ be a keyed family with finite key set $\kappa$. Its labelling map sends a key $K$ and points $x_1, \ldots, x_m$ to the labelled sample $((x_i, F_K(x_i)))_i$. Let $I$ be any randomized map from labelled samples to keys. Draw $m$ uniform examples of $F_K$ and let $K' = I(\text{sample})$. Then for every $\varepsilon \ge 0$,

$$
\Pr[\mathrm{err}(F_K, F_{K'}) > \varepsilon] \le \Pr[F_{K'} \text{ disagrees with some example}] + |\kappa|(1-\varepsilon)^m,
$$

and if $\ln|\kappa| + \ln(1/\delta) \le \varepsilon m$ the last term may be replaced by $\delta$. The same holds averaged over any prior on $K$. Thus any inverter of the labelling map is a learner, with no running-time assumption.

## Proof sketch

A returned key consistent with the sample is a consistent hypothesis from the finite class $\{F_k\}$. By the union bound over keys, the probability that some key with error above $\varepsilon$ is consistent with $m$ independent uniform examples is at most $|\kappa|(1-\varepsilon)^m$. Otherwise the inverter failed to be consistent.

## Depends on

- [Learning from uniform random examples](../../circuit-complexity/learning-under-the-uniform-distribution/learning-from-uniform-random-examples.md)

## Proof depends on

- [Union bound over a finite class (the Occam bound)](../../../ComputerScience/machine-learning/pac-learning/occam-bound-for-consistent-learners/pi-exists-bad-consistent-le.md)

## Sources

- Avrim Blum, Merrick Furst, Michael Kearns and Richard J. Lipton, "Cryptographic Primitives Based on Hard Learning Problems", Advances in Cryptology (CRYPTO 1993), 1993.
- Russell Impagliazzo and Leonid A. Levin, "No Better Ways to Generate Hard NP Instances than Picking Uniformly at Random", Proceedings of the 31st Annual Symposium on Foundations of Computer Science, 1990.
