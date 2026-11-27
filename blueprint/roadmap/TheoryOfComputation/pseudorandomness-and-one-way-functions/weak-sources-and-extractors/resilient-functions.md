# Coalition influence and resilient functions

Let $f : \{0,1\}^n \to \{0,1\}$ and $Q \subseteq [n]$ a coalition. $f$ is *undetermined at $x$ by the bits outside $Q$* if two strings agreeing with $x$ outside $Q$ take different values of $f$. Under a distribution $D$ on $\{0,1\}^n$, the *influence* $I_{Q,D}(f)$ is the probability, for $x \sim D$, that $f$ is undetermined at $x$ by the bits outside $Q$. The function is *$(q, \varepsilon)$-resilient* if $I_{Q,U}(f) \le \varepsilon$ for every coalition with $|Q| \le q$ under the uniform distribution $U$, and *$t$-independent $(q, \varepsilon)$-resilient* if $I_{Q,D}(f) \le \varepsilon$ for every such $Q$ and every $t$-wise independent $D$. A *non-oblivious bit-fixing source* has good coordinates $[n]\setminus Q$ that are (nearly) $t$-wise independent and bad coordinates $Q$ that may depend arbitrarily on the good ones.

## Depends on

- [k-wise independent hash family](../../../ComputerScience/data-structures/hashing/succinct-dictionaries-and-hash-families/word-ram-hash-families/k-wise-independent-hash-family.md)
- [k-wise independent and almost k-wise independent distributions](../../circuit-complexity/constant-depth-circuit-lower-bounds/ac0-fourier-and-pseudorandomness/k-wise-independent-distributions.md)

## Sources

- E. Chattopadhyay and D. Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics 189(3), 653–705, 2019 (numbering of ECCC TR15-119), Definitions 1.8, 1.9 and 1.12 (there the maximum is over coalitions of size exactly $q$, equivalent by monotonicity).
- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
