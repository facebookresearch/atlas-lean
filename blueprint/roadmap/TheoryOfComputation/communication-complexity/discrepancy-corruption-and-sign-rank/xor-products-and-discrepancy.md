# XOR products have exponentially small discrepancy

Let $\Lambda$ be a finite set, $g : \Lambda \times \Lambda \to \{0,1\}$ a two-party gadget, and $\mathrm{disc}(g)$ its discrepancy under the uniform distribution (the maximum over rectangles $R$ of $|\Pr[g(U,V)=0,\ (U,V)\in R]-\Pr[g(U,V)=1,\ (U,V)\in R]|$ for independent uniform $U,V$). For $k \ge 1$ let $g^{\oplus k}((x_1..x_k), (y_1..y_k)) = \bigoplus_i g(x_i, y_i)$. Then

$$\mathrm{disc}(g)^k \le \mathrm{disc}(g^{\oplus k}) \le \big(64\, \mathrm{disc}(g)\big)^k .$$

The upper bound is the XOR lemma for discrepancy of Lee, Shraibman and Špalek.

## Proof sketch

The lower bound holds because a product of rectangles of the factors is a rectangle of the product. Derived here by an elementary route, a weaker form of the upper bound, $\mathrm{disc}(g^{\oplus k})^4 \le \big(4\, \mathrm{disc}(g)\big)^k$: the cube expectation $\mathbb{E}_{x,x',y,y'}[s(x,y)s(x,y')s(x',y)s(x',y')]$ of the sign matrix $s=(-1)^g$, with all four variables independent and uniform, multiplies under XOR products. It bounds $\mathrm{disc}^4$ from above by Cauchy–Schwarz twice. It is at most $4\,\mathrm{disc}$: for fixed $x'$ it is a bilinear form $\mathbb{E}_{x,y}[a(x)\,s(x,y)\,b(y)]$ with $a, b$ taking values in $[-1,1]$, and splitting $a$ and $b$ into positive and negative parts gives four $[0,1]$-valued bilinear forms, each at most $\mathrm{disc}$ because their extremes are at rectangle indicators. The box norm itself, the fourth root of the cube expectation, is not bounded by $4\,\mathrm{disc}$: for the $N \times N$ inner-product sign matrix the cube expectation is $1/N$, so the box norm is $N^{-1/4}$, while $\mathrm{disc} \le N^{-1/2}$.

## Depends on

- [Discrepancy of a function under a distribution](discrepancy-under-a-distribution.md)

## Sources

- A. Chattopadhyay, Y. Filmus, S. Koroth, O. Meir and T. Pitassi, "Query-to-Communication Lifting Using Low-Discrepancy Gadgets", SIAM Journal on Computing 50(1), 2021 (Definition 1.1, and Theorem 2.11 quoting Lee–Shraibman–Špalek).
- T. Lee, A. Shraibman and R. Špalek, "A Direct Product Theorem for Discrepancy", CCC 2008.
