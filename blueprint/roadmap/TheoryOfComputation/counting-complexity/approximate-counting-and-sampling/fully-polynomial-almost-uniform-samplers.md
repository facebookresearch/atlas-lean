# Fully polynomial almost uniform samplers and self-reducible witness families

For a relation $R$ with witness sets $R(x)=\{y:(x,y)\in R\}$, an **FPAUS** is a randomized algorithm that, on input $x$ with $R(x)\ne\emptyset$ and $\delta>0$, runs in time polynomial in $|x|$ and $\log(1/\delta)$ and outputs a witness whose distribution is within total variation distance $\delta$ of uniform on $R(x)$. An **FPRAS** for $|R(x)|$ outputs, in time polynomial in $|x|$ and $1/\varepsilon$, a value within a factor $1\pm\varepsilon$ of $|R(x)|$ with probability at least $3/4$. Jerrum, Valiant and Vazirani's original almost uniform generators instead require every output probability to lie within a factor $1+\delta$ of a common value (and allow rejection with probability at most $1/2$); the equivalence below holds for either notion. $R$ is (one-bit) **self-reducible** if $R(x)$ partitions as $R(x)=\bigsqcup_{b\in\{0,1\}}b\cdot R(x_b)$ with $x_b$ polynomial-time computable from $x$ and $b$, with $|x_b|<|x|$, until the witnesses have length $0$; this is the special case of Jerrum–Valiant–Vazirani self-reducibility in which one bit of the witness is fixed per step (they allow $O(\log|x|)$ bits).

## Depends on

- [Search problems: FNP, FP and TFNP](../../complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)
- [Karp-Luby: FPRAS for DNF counting](../karp-luby-algorithm-for-dnf-counting/karp-luby-dnf-counting.md)

## Sources

- Mark R. Jerrum, Leslie G. Valiant and Vijay V. Vazirani, "Random Generation of Combinatorial Structures from a Uniform Distribution", Theoretical Computer Science 43, 169–188, 1986, Section 6 (definitions of self-reducibility, almost uniform generators and randomized approximation schemes).
- Alistair Sinclair and Mark Jerrum, "Approximate Counting, Uniform Generation and Rapidly Mixing Markov Chains", Information and Computation 82(1), 1989 (variation-distance formulation).
- Alistair Sinclair, "CS294 Partition Functions, Lecture 4", Lecture notes, University of California, Berkeley, 2025.
