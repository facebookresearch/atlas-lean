# MCSP is not in AC0[p]

For every prime $p$, deciding MCSP on $N$-bit truth tables with depth-$d$ $\mathrm{AC}^0[p]$ circuits requires size $\exp(\Omega(N^{0.49/(d-1)}))$. So MCSP is not in $\mathrm{AC}^0[p]$, and in particular not in $\mathrm{AC}^0[2]$.

**Theorem (Golovnev–Ilango–Impagliazzo–Kabanets–Kolokolova–Tal).** Let $p\ge2$ be a prime. For every depth $d$ and all large enough $N=2^n$, every depth-$d$ $\mathrm{AC}^0[p]$ circuit computing MCSP on $N$-bit truth tables (with the size parameter as a second input) has size

$$\exp\left(\Omega\left(N^{0.49/(d-1)}\right)\right).$$

The source states the bound for every depth $d>0$; it is meaningful for $d\ge2$, where $d-1\ge1$.

The *coin problem* with bias $\varepsilon$ asks to distinguish $N$ independent bits that are each $1$ with probability $1/2$ from bits that are each $1$ with probability $1/2-\varepsilon$, with constant advantage. The sharpened coin-problem lower bound quoted as Theorem 2.6 states that any depth-$d$ $\mathrm{AC}^0[p]$ circuit solving it has size at least $\exp(\Omega((1/\varepsilon)^{1/(d-1)}))$.

## Expansion

Take $t=\lceil 2^{0.49n}\rceil$ and biases $p_i=0.01+0.49\,i/t$ for $0\le i\le t$, with product distributions $\mu_i$ and expected circuit sizes $s_i$. Lupanov's estimates give $s_t\ge0.9\cdot2^n/n$ and $s_0\le0.1\cdot2^n/n$, so some consecutive pair has $s_{i+1}-s_i\ge\Omega(2^{0.51n}/n)$, far above the concentration window $\sqrt{N}\,n^2$. With threshold $s^*=(s_i+s_{i+1})/2$, $\mathrm{MCSP}(\cdot,s^*)$ separates $\mu_i$ from $\mu_{i+1}$ with constant advantage. Randomly zeroing coordinates turns this into a coin-problem solver of the same size and depth with $\varepsilon=\Theta(N^{-0.49})$, and the coin-problem lower bound finishes the proof.


Known unstated proof prerequisites needed before this node is ready for formalization:

- Coin-problem lower bound for AC0[p] (Golovnev et al. Theorem 2.6)
- Explicit Shannon–Lupanov circuit-size bounds $s_t \ge 0.9\cdot 2^n/n$ and $s_0 \le 0.1\cdot 2^n/n$ (Golovnev et al. Theorems 2.1 and 2.2)

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [AC0(m): constant-depth circuits with MOD gates](../../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)

## Proof depends on

- [Concentration of circuit complexity under product distributions](concentration-of-circuit-complexity.md)
- [Shannon: most Boolean functions need exponential circuits](../../shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- Alexander Golovnev, Rahul Ilango, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, Avishay Tal, "AC^0[p] Lower Bounds Against MCSP via the Coin Problem", *International Colloquium on Automata, Languages, and Programming (ICALP)*, 2019, https://doi.org/10.4230/LIPIcs.ICALP.2019.66 (Theorem 4.1, using Theorems 2.1, 2.6 and 3.1).
