# Space-bounded pseudorandom generators are 2ε-biased

If $G : \{0,1\}^k \to \{0,1\}^\ell$ is an $(s, \varepsilon)$-pseudorandom generator against read-once programs of width $2^s$ with $s \ge 1$, then $G(U_k)$ is $2\varepsilon$-biased. The factor $2$ is necessary: the generator $\sigma \mapsto \sigma\sigma$ on one seed bit is $(s, 1/2)$-pseudorandom for every $s$ (its output is at distance $1/2$ from uniform), but its two output bits always have even parity, so its bias is $1$. Thus the printed claim that such generators are $\varepsilon$-biased (Goldreich, Exercise 8.38) holds only after this correction.

## Proof sketch

The parity on $S$ is a width-$2$ read-once test, and $\mathrm{bias}(S) = 2(\Pr[\oplus_S = 0] - \tfrac12)$, which is twice the distinguishing advantage of that test against uniform bits. The counterexample is checked directly.

## Depends on

- [Read-once branching programs and space-bounded pseudorandom generators](space-bounded-pseudorandom-generators.md)
- [Bias, ε-biased and k-wise ε-biased distributions](../small-bias-spaces/small-bias-distributions.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", public draft of Chapters 7–8, March 2007.
