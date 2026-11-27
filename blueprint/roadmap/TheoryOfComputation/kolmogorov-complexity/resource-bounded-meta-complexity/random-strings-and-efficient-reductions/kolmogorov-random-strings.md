# Sets of Kolmogorov-random strings R_C, R_K and R_{K^t}

For a universal machine $U$, $R_{C_U}=\{x : C_U(x)\ge|x|\}$ and $R_{K_U}=\{x : K_U(x)\ge|x|\}$ are the plain and prefix-free Kolmogorov-random strings, and $R_{K^t_U}$ the time-bounded ones. Unlike most of Kolmogorov complexity, what reduces efficiently to these sets depends on the choice of $U$.

**Definitions.** For a Turing machine $U$, $C_U(x)$ is the length of a shortest $d$ with $U(d)=x$, and $K_U(x)$ is the same quantity for a prefix machine $U$ (if $U(d)$ halts with output, $U(dz)$ is undefined for every nonempty $z$). The *random strings* are

$$
R_{C_U}=\{x : C_U(x)\ge|x|\},\qquad R_{K_U}=\{x : K_U(x)\ge|x|\}.
$$

For a time bound $t$ (non-decreasing, time-constructible, $t(n)\ge n$), $K^t_U(x)$ is the length of a shortest $p$ such that $U(p)$ outputs $x$ and halts in fewer than $t(|x|)$ steps, and $R_{K^t_U}=\{x : K^t_U(x)\ge|x|\}$. A prefix machine $U$ is a *time-efficient universal prefix machine* if there are a constant $c$ and constants $c_M$ for each prefix machine $M$ such that $K_U(x)\le K_M(x)+c_M$ for all $x$, and $K^t_U(x)\le K^{t'}_M(x)+c_M$ for all $x$ and all time bounds with $t>(t')^c$. Then $R_{K_U}\subseteq R_{K^t_U}$.

**Basic facts.** $R_C$ and $R_K$ are co-r.e. and complete for the halting problem under weak-truth-table reductions, and $R_C$ is complete under disjunctive truth-table reductions (Kummer). Membership $x\in R_{K^t_M}$ can be decided in any time $t'(|x|)>2^{|x|}t(|x|)$ by simulating $M$ on all shorter programs.

**Dependence on $U$.** There is a universal machine $U$ for which $\{0^{2^x} : x\notin H\}$, with $H$ the halting problem, is $\le^P_{dtt}$-reducible to $R_{C_U}$. Yet for every computable time bound $t$ there are universal machines $U_1,U_2$ such that $R_{C_{U_1}}$ is not many-one reducible to $R_{C_{U_2}}$ in time $t$, and a universal $U$ and a decidable set not dtt-reducible to $R_{C_U}$ in time $t$.

## Expansion

The machine dependence comes from padding: a universal machine may be modified to give short descriptions to selected strings, or to withhold them, without losing universality, since the change shifts complexities by at most a constant. Time-bounded random strings of length $n$ can be computed in time about $2^nt(n)$, which is why reductions to $R_{K^t}$ behave differently from reductions to $R_K$.

## Depends on

- [Kolmogorov complexity](../../k.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

None.

## Sources

- Eric Allender, Harry Buhrman and Michal Koucký, "What Can Be Efficiently Reduced to the Kolmogorov-Random Strings?", *Annals of Pure and Applied Logic* 138, 2006, [doi:10.1016/j.apal.2005.05.013](https://doi.org/10.1016/j.apal.2005.05.013) (Section 1, Theorem 1, Corollaries 2 and 3; numbering of the ECCC TR04-044 version).
- Eric Allender, Harry Buhrman, Luke Friedman and Bruno Loff, "Reductions to the set of random strings: The resource-bounded case", *Logical Methods in Computer Science* 10(3:5), 2014, DOI 10.2168/LMCS-10(3:5)2014, [arXiv:1406.7658v2](https://arxiv.org/abs/1406.7658v2) (Section 2, Definition 2.1, Proposition 2.4).
