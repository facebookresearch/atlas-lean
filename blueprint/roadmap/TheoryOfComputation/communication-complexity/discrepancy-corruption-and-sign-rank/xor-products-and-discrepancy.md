# XOR products have exponentially small discrepancy

For a two-party gadget $g : X \times Y \to \{0,1\}$ and $k \ge 1$, let $g^{\oplus k}((x_1..x_k), (y_1..y_k)) = \bigoplus_i g(x_i, y_i)$. Then the uniform discrepancy satisfies

$$\mathrm{disc}(g^{\oplus k})^4 \le \big(4\, \mathrm{disc}(g)\big)^k.$$

The proof goes through the two-party cube (box) norm, which tensorizes exactly under XOR products and is at most four times the discrepancy; sharper bounds of the form $\mathrm{disc}(g^{\oplus k}) \le (c\,\mathrm{disc}(g))^k$ are due to Lee, Shraibman and Špalek.

## Proof sketch

The cube expectation $\mathbb{E}_{x,x',y,y'}[s(x,y)s(x,y')s(x',y)s(x',y')]$ of the sign matrix $s$ multiplies under XOR products, bounds $\mathrm{disc}^4$ from above by Cauchy–Schwarz twice, and is at most $4\,\mathrm{disc}$.

## Depends on

- [Discrepancy of a function under a distribution](discrepancy-under-a-distribution.md)

## Sources

- A. Chattopadhyay, Y. Filmus, S. Koroth, O. Meir and T. Pitassi, "Query-to-Communication Lifting Using Low-Discrepancy Gadgets", SIAM Journal on Computing 50(1), 2021.
- F. R. K. Chung, "Quasi-Random Classes of Hypergraphs", Random Structures & Algorithms 1(4), 1990.
