# Fully polynomial almost uniform samplers and self-reducible witness families

For a relation $R$ with witness sets $R(x)=\{y:(x,y)\in R\}$, an **FPAUS** is a randomized algorithm that, on input $x$ with $R(x)\ne\emptyset$ and $\delta>0$, runs in time polynomial in $|x|$ and $\log(1/\delta)$ and outputs a witness whose distribution is within total variation distance $\delta$ of uniform on $R(x)$. An **FPRAS** for $|R(x)|$ outputs, in time polynomial in $|x|$ and $1/\varepsilon$, a value within a factor $1\pm\varepsilon$ of $|R(x)|$ with probability at least $3/4$. $R$ is (one-bit) **self-reducible** if $R(x)$ partitions as $R(x)=\bigsqcup_{b\in\{0,1\}}b\cdot R(x_b)$ with $x_b$ polynomial-time computable from $x$ and $b$, down to instances of trivial size.

## Depends on

- [Search problems: FNP, FP and TFNP](../../complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)
- [Karp-Luby: FPRAS for DNF counting](../karp-luby-algorithm-for-dnf-counting/karp-luby-dnf-counting.md)

## Sources

- Mark R. Jerrum, Leslie G. Valiant and Vijay V. Vazirani, "Random Generation of Combinatorial Structures from a Uniform Distribution", Theoretical Computer Science 43, 1986.
- Alistair Sinclair, "CS294 Partition Functions, Lecture 4", Lecture notes, University of California, Berkeley, 2025.
