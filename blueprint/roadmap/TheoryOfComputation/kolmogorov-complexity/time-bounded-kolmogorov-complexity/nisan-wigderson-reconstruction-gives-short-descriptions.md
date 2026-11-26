# Distinguishers for the Nisan–Wigderson generator give short time-bounded descriptions

Let $C$ be a list-decodable code whose codewords are truth tables of Boolean functions on $n$ bits, let $D$ be a combinatorial design with $m$ sets of size $n$ in a universe of size $\ell$ and pairwise intersections at most $a$, and let a deterministic test $T$ distinguish the Nisan–Wigderson generator $\mathrm{NW}^{C(x)}_D$ from uniform with advantage $\varepsilon$. Then $x$ has a description, relative to $T$, of length $O(m 2^{a} + \log(1/\varepsilon)) + $ (list-decoding index) that runs in time polynomial in $2^n$ and the running time of $T$.

## Proof sketch

The standard NW reconstruction: a hybrid argument turns the distinguisher into a predictor of one bit of the codeword with advantage $\varepsilon/m$, using advice consisting of the truth tables of the other codeword restrictions on the small intersections ($m 2^a$ bits); list decoding the predictor recovers $C(x)$ and hence $x$.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Sources

- N. Nisan and A. Wigderson, "Hardness vs Randomness", Journal of Computer and System Sciences 49(2), 1994.
- E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek and D. Ronneburger, "Power from Random Strings", SIAM Journal on Computing 35(6), 2006.
- S. Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS 2018.
