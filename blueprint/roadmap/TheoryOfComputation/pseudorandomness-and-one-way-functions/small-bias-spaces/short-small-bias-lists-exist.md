# Short ε-biased lists exist for every admissible length

Let $n \ge 1$, $\varepsilon \ge 0$ and $d \ge 1$ satisfy $2 \cdot 2^n \exp(-\varepsilon^2 d/2) < 1$. Then there is a list $s_1, \dots, s_d \in \{0,1\}^n$ whose uniform distribution is $\varepsilon$-biased, i.e. $\bigl|\sum_{j=1}^d (-1)^{\bigoplus_{i\in S} s_{j,i}}\bigr| \le \varepsilon d$ for every nonempty $S \subseteq [n]$. In particular $d = O(n/\varepsilon^2)$ suffices; such lists generate small-bias Cayley graphs.

## Proof sketch

For a fixed nonempty $S$, the parities on $S$ of $d$ independent uniform strings are $d$ independent unbiased bits (shear one coordinate of $S$). Hoeffding's inequality bounds the fraction of lists biased at $S$ by $2\exp(-\varepsilon^2 d/2)$, and a union bound over fewer than $2^n$ sets leaves a good list.

## Depends on

- [Small-bias distribution and generator](../space-bounded-and-small-bias-generators/small-bias-distributions.md)
- [Hoeffding's inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- J. Naor and M. Naor, "Small-Bias Probability Spaces: Efficient Constructions and Applications", SIAM Journal on Computing 22(4), 838–856, 1993.
- N. Alon, O. Goldreich, J. Håstad and R. Peralta, "Simple Constructions of Almost k-wise Independent Random Variables", Random Structures & Algorithms 3(3), 289–304, 1992.
