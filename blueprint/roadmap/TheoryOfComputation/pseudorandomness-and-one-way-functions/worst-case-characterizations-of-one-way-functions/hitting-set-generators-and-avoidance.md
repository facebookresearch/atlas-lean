# Hitting set generators and algorithms that avoid them

A **hitting set generator** is a family $H=\{H_n:\{0,1\}^{\ell(n)}\to\{0,1\}^n\}_{n\in\mathbb{N}}$ of efficiently computable functions with $\ell(n)<n$. An algorithm $A$ **avoids** $H$ if, for every $n$, $A$ accepts at least half of the strings in $\{0,1\}^n$ and rejects every string in the image of $H_n$. $H$ is **secure against a class $\mathcal C$** (infinitely often, respectively) if no algorithm in $\mathcal C$ avoids $H$ (on all large $n$, respectively). Since images of $H_n$ have time-bounded complexity at most $\ell(n)+O(\log n)$ while most strings are incompressible, avoiding a hitting set generator is reducible to approximating time-bounded Kolmogorov complexity, and the two tasks are equivalent in complexity.

## Depends on

- [Kolmogorov complexity](../../kolmogorov-complexity/k.md)
- [Pseudorandom generators against circuits](../derandomization/pseudorandom-generators-against-circuits.md)

## Sources

- Shuichi Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS (2018), ECCC TR18-138.
- Shuichi Hirahara, "Capturing One-Way Functions via NP-Hardness of Meta-Complexity", STOC (2023), ECCC TR23-037.
