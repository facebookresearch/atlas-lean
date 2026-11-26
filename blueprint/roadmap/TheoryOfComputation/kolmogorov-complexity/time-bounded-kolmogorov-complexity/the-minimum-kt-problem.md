# The minimum Kt problem MKtP

*MKtP* is the language of pairs $(x, 1^s)$ with $Kt(x) \le s$; for a function $s$ computable in polynomial time, $\mathrm{MKtP}[s] = \{x : Kt(x) \le s(|x|)\}$. For a constant $c$, the promise problem $\mathrm{GapMKtP}_c$ separates $Kt(x) \le s$ from $Kt(x) > s + c\log|x|$. Since there is a constant $c_0$ with $Kt(x) \le |x| + c_0\log|x|$ for every $x$ of length at least $2$, every threshold $s \ge |x| + c_0\log|x|$ accepts $x$, so only smaller thresholds matter, and for those unary and binary encodings are polynomially related.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Sources

- Y. Liu and R. Pass, "On the Possibility of Basing Cryptography on EXP ≠ BPP", CRYPTO 2021.
- E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek and D. Ronneburger, "Power from Random Strings", SIAM Journal on Computing 35(6), 2006.
