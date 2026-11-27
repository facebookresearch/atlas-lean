# XOR products have exponentially small discrepancy

For a two-party gadget $g : X \times Y \to \{0,1\}$ and $k \ge 1$, let $g^{\oplus k}((x_1..x_k), (y_1..y_k)) = \bigoplus_i g(x_i, y_i)$. Then the uniform discrepancy satisfies

$$\mathrm{disc}_{\mathrm{unif}}(g^{\oplus k})^4 \le \big(4\, \mathrm{disc}_{\mathrm{unif}}(g)\big)^k.$$

The proof goes through the fourth power of the two-party box norm, that is the cube expectation below: it tensorizes exactly under XOR products, bounds $\mathrm{disc}_{\mathrm{unif}}^4$ from above, and is at most four times $\mathrm{disc}_{\mathrm{unif}}$. The box norm itself, its fourth root, is not bounded by $4\,\mathrm{disc}_{\mathrm{unif}}$: for the $N \times N$ inner-product sign matrix the cube expectation is $1/N$, so the box norm is $N^{-1/4}$, while $\mathrm{disc}_{\mathrm{unif}} \le N^{-1/2}$. The sharper bound $\mathrm{disc}_{\mathrm{unif}}(g^{\oplus k}) \le (64\, \mathrm{disc}_{\mathrm{unif}}(g))^k$ is due to Lee, Shraibman and Špalek.

## Proof sketch

The cube expectation $\mathbb{E}_{x,x',y,y'}[s(x,y)s(x,y')s(x',y)s(x',y')]$ of the sign matrix $s$, with all four variables independent and uniform, multiplies under XOR products. It bounds $\mathrm{disc}_{\mathrm{unif}}^4$ from above by Cauchy–Schwarz twice. It is at most $4\,\mathrm{disc}_{\mathrm{unif}}$: for fixed $x'$ it is a bilinear form $\mathbb{E}_{x,y}[a(x)\,s(x,y)\,b(y)]$ with $a, b$ taking values in $[-1,1]$, and splitting $a$ and $b$ into positive and negative parts gives four $[0,1]$-valued bilinear forms, each at most $\mathrm{disc}_{\mathrm{unif}}$ because their extremes are at rectangle indicators.

## Depends on

- [Discrepancy of a function under a distribution](discrepancy-under-a-distribution.md)

## Sources

- A. Chattopadhyay, Y. Filmus, S. Koroth, O. Meir and T. Pitassi, "Query-to-Communication Lifting Using Low-Discrepancy Gadgets", SIAM Journal on Computing 50(1), 2021 (Definition 1.1, and Theorem 2.11 quoting Lee–Shraibman–Špalek).
- T. Lee, A. Shraibman and R. Špalek, "A Direct Product Theorem for Discrepancy", CCC 2008.
- F. R. K. Chung, "Quasi-Random Classes of Hypergraphs", Random Structures & Algorithms 1(4), 1990.
