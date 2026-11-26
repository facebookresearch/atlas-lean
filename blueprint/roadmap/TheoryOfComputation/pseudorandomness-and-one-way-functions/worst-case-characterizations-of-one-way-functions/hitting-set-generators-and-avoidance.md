# Hitting set generators and algorithms that avoid them

A **hitting set generator** is a family $H=\{H_n:\{0,1\}^{\ell(n)}\to\{0,1\}^n\}_{n\in\mathbb{N}}$ of efficiently computable functions with $\ell(n)<n$. An algorithm $A$ **avoids** $H$ if, for every $n$, $A$ accepts at least half of the strings in $\{0,1\}^n$ and rejects every string in the image of $H_n$. $H$ is **secure against a class $\mathcal C$** (infinitely often, respectively) if no algorithm in $\mathcal C$ avoids $H$ (on all large $n$, respectively). Every string in the image of $H_n$ has $t$-time-bounded Kolmogorov complexity at most $\ell(n)+O(\log n)$ for every polynomial time bound $t$ sufficiently larger than the running time of $H$, while at least half of all $n$-bit strings have complexity at least $n-1$. Hence an algorithm that distinguishes $K^t(x)\le\ell(n)+O(\log n)$ from $K^t(x)\ge n-1$ avoids $H$ whenever $\ell(n)\le n-\omega(\log n)$: approximating time-bounded Kolmogorov complexity avoids every such hitting set generator.

## Depends on

- [Kolmogorov complexity](../../kolmogorov-complexity/k.md)
- [Pseudorandom generators against circuits](../derandomization/pseudorandom-generators-against-circuits.md)

## Sources

- Shuichi Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS (2018), ECCC TR18-138.
- Shuichi Hirahara, "Capturing One-Way Functions via NP-Hardness of Meta-Complexity", STOC (2023), ECCC TR23-037.
