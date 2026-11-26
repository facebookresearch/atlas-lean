# Small anti-checkers exist for functions without small circuits

Let $\mathcal{F}$ be a family of fewer than $2^b$ functions on at most $2^m$ inputs ($m > 0$). If no $m$ members of $\mathcal{F}$ have $f$ as their strict pointwise majority, then some set of at most $16 b$ inputs refutes every member of $\mathcal{F}$ (each member disagrees with $f$ somewhere on the set). Consequently, for $n \le m$, if $\mathrm{CC}(f)$ exceeds $m s$ plus the size of a circuit for strict majority on $m$ bits, then $\mathrm{CC}_Y(f) > s$ for some $Y$ with $|Y| \le 16 b$, where $b = O(s \log s)$ bounds the description length of circuits of size $s$.

## Proof sketch

Minimax (Lipton–Young): view the game in which one player picks a circuit of size $s$ and the other an input, with payoff for disagreement. If no small anti-checker exists, a multiplicative-weights / sampling argument finds a distribution on circuits that agrees with $f$ on every input with probability above $1/2$; sampling $m$ circuits and taking their majority yields a circuit of size $m s + O(\mathrm{size}(\mathrm{MAJ}_m))$ computing $f$.

## Depends on

- [Anti-checkers](anti-checkers.md)

## Proof depends on

- [Yao's minimax principle](../../randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- R. J. Lipton and N. E. Young, "Simple Strategies for Large Zero-Sum Games with Applications to Complexity Theory", STOC 1994.
- I. C. Oliveira, J. Pich and R. Santhanam, "Hardness Magnification near State-Of-The-Art Lower Bounds", Computational Complexity Conference (CCC) 2019.
