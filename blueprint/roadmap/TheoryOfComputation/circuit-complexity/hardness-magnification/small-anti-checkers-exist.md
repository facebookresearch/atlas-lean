# Small anti-checkers exist for functions without small circuits

In this page the size of a circuit is the length of its binary encoding (Lipton and Young 1994, Definition 4), so the circuits of size at most $s$ are those with one of the $2^s$ encodings $0 \le i < 2^s$; write $\mathrm{CC}^{\mathrm{bin}}(f)$ for the least size in this sense of a circuit computing $f$, and $\mathrm{CC}^{\mathrm{bin}}_Y(f)$ for the least size of a circuit agreeing with $f$ on $Y$. There is a number $N_0$ such that for every $n > N_0$, every $\varepsilon > 0$, every $f : \{0,1\}^n \to \{0,1\}$ and every $s \le \mathrm{CC}^{\mathrm{bin}}(f)\,\varepsilon^2/(3n)$, there is a multiset of $s/\varepsilon^2$ inputs such that every circuit of size at most $s$ misclassifies at least a $1/2 - \varepsilon$ fraction of them (Lipton and Young 1994, Theorem 6). In particular, taking $\varepsilon = 1/3$: if $s \le \mathrm{CC}^{\mathrm{bin}}(f)/(27 n)$, then some $Y$ with $|Y| \le 9 s$ has $\mathrm{CC}^{\mathrm{bin}}_Y(f) > s$, since every circuit of size at most $s$ errs on a sixth of a multiset of $9s$ inputs.

## Proof sketch

Minimax (Lipton–Young): view the game in which one player picks a circuit of size $s$ and the other an input, with payoff $1$ for disagreement, and let $1/2 - \delta$ be its value. Sampling from optimal strategies (Corollary 4 of the source) gives $1 + n \ln 2/(2\delta^2)$ circuits whose majority is correct on every input, hence a circuit of size about $n s \ln 2/(2\delta^2) + s + O(n/\delta^2)$ computing $f$; as this is at least $\mathrm{CC}^{\mathrm{bin}}(f)$, $\delta$ is small compared with $\varepsilon$, and sampling the other player's optimal strategy gives $s \ln 2/(2(\varepsilon - \delta)^2) \le s/\varepsilon^2$ inputs on which every circuit of size $s$ errs on at least a $1/2 - \varepsilon$ fraction.

## Depends on

- [Anti-checkers](anti-checkers.md)

## Proof depends on

- [Yao's minimax principle](../../randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- R. J. Lipton and N. E. Young, "Simple Strategies for Large Zero-Sum Games with Applications to Complexity Theory", STOC 1994.
- I. C. Oliveira, J. Pich and R. Santhanam, "Hardness Magnification near State-Of-The-Art Lower Bounds", Computational Complexity Conference (CCC) 2019.
