# Integer weighted automata on infinite words

An integer weighted automaton reads an infinite word along a nondeterministic path whose transitions carry integer weights, and accepts the word when some prefix of some path ends in a final state with total weight zero.

An *integer weighted automaton* $\mathcal A=(Q,A,\sigma,q_0,F)$ has a finite set $Q$ of states, a finite alphabet $A$, transitions $\sigma\subseteq Q\times A\times Q\times\mathbb Z$, an initial state $q_0$ and final states $F\subseteq Q$; it is complete: every state has at least one transition on every letter. For a path $\pi=t_0t_1\cdots$ with $t_j=(q_j,a_j,q_{j+1},z_j)$ and a finite prefix $p=t_0\cdots t_n$, the *weight* of $p$ is $\gamma(p)=z_0+\cdots+z_n$, and $p$ *reaches* $q_{n+1}$. The language of $\mathcal A$ is

$$
L(\mathcal A)=\{w\in A^\omega:\ \text{some path }\pi\text{ labeled }w\text{ has a prefix }p\text{ with }\gamma(p)=0\text{ that reaches a state of }F\}.
$$

In *reverse acceptance* the weight is computed on the reversed prefix $p^R$; this gives the language $L_R(\mathcal A)$. The *universality problem* asks whether $L(\mathcal A)=A^\omega$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Acceptance asks for a single zero-weight prefix, so it is a reachability condition along infinite runs rather than a Büchi condition.

## Sources

- Vesa Halava, Tero Harju, Reino Niskanen and Igor Potapov, "Weighted automata on infinite words in the context of Attacker–Defender games", *Information and Computation* 255, 2017, pp. 27–44, doi:[10.1016/j.ic.2017.05.001](https://doi.org/10.1016/j.ic.2017.05.001); read in arXiv:1411.4796v3 ([arXiv](https://arxiv.org/abs/1411.4796v3)), whose numbering is used: Section 2 (Notations and Definitions).
