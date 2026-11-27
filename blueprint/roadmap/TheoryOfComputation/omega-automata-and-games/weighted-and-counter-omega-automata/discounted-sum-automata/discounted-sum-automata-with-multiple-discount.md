# Discounted-sum automata with multiple discount factors

A discounted-sum automaton with multiple discount factors is a nondeterministic automaton whose transitions carry a rational weight and a rational discount factor greater than one; a run's value is its sum of weights, each divided by the product of the discount factors before it, and a word's value is the infimum over its runs.

A *nondeterministic discounted-sum automaton with multiple discount factors* (NMDA), on finite or on infinite words, is a tuple $\mathcal A=(\Sigma,Q,\iota,\delta,\gamma,\rho)$ with a finite alphabet $\Sigma$, a finite set $Q$ of states, a set $\iota\subseteq Q$ of initial states, a transition relation $\delta\subseteq Q\times\Sigma\times Q$, a weight function $\gamma:\delta\to\mathbb Q$ and a discount-factor function $\rho:\delta\to\mathbb Q\cap(1,\infty)$. A run is a sequence $p_0\sigma_0p_1\sigma_1\cdots$ with $p_0\in\iota$ and $(p_i,\sigma_i,p_{i+1})\in\delta$; writing $r[i]$ for its $i$-th transition, the value of a run $r$ of length $|r|\le\infty$ is

$$
\mathcal A(r)=\sum_{i=0}^{|r|-1}\gamma(r[i])\prod_{j=0}^{i-1}\frac{1}{\rho(r[j])},
$$

and the value of $\mathcal A$ on a word $w$ is $\mathcal A(w)=\inf\{\mathcal A(r): r \text{ a run on } w\}$. The NMDA is *integral* if all discount factors are integers, and *deterministic* (a DMDA) if $|\iota|=1$ and each state has at most one successor per letter. When $\rho$ is constant, equal to $\lambda$, it is a $\lambda$-NDA (a classical discounted-sum automaton).

For NMDAs $\mathcal A,\mathcal B$ on the same kind of words, *non-strict containment* asks whether $\mathcal A(w)\le\mathcal B(w)$ for all words $w$, *strict containment* whether $\mathcal A(w)<\mathcal B(w)$ for all $w$, and *equivalence* whether $\mathcal A(w)=\mathcal B(w)$ for all $w$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Discount factors greater than one divide later weights; some authors use factors in $(0,1)$ and multiply instead. On infinite words the value of every run converges because the weights are bounded and every discount factor exceeds one.

## Sources

- Udi Boker and Guy Hefetz, "On the Comparison of Discounted-Sum Automata with Multiple Discount Factors", in *Foundations of Software Science and Computation Structures (FoSSaCS 2023)*, Lecture Notes in Computer Science 13992, Springer, 2023, pp. 371–391, doi:[10.1007/978-3-031-30829-1_18](https://doi.org/10.1007/978-3-031-30829-1_18); numbering of arXiv:2301.04086v2 ([arXiv](https://arxiv.org/abs/2301.04086v2)): Section 2, Definition 1 (NMDAs, runs, values, integral and deterministic NMDAs, NDAs) and the comparison problems of Section 3.
