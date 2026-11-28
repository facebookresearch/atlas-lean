# Nilpotency of sand automata is undecidable

Sand automata act on configurations of sand grains, one column per cell, by a local rule that reads height differences in a bounded neighborhood; no algorithm decides whether a given one-dimensional sand automaton empties every finite configuration.

**Sand automata.** A *configuration* is an element of $\widetilde{\mathbb Z}^{\mathbb Z}$, where $\widetilde{\mathbb Z}=\mathbb Z\cup\{-\infty,+\infty\}$ and $c_i$ is the number of grains in column $i$ ($-\infty$ is a sink, $+\infty$ a source). A configuration is *finite* if $c_i=0$ for all $|i|$ large enough, and *periodic* if there is $p\neq0$ with $c_i=c_{i+tp}$ for all $i$ and $t\in\mathbb Z$. Two conventions are needed for the theorem below to say what is meant. The source does not require $p\ne0$, but with $p=0$ every configuration would be periodic. Its definitions also let finite and periodic configurations contain columns $\pm\infty$; since the global map never changes such a column, such a configuration never reaches the empty configuration, so in the nilpotency problem below $\mathcal F$ is the set of finite configurations in $\mathbb Z^{\mathbb Z}$, with every column holding an integer number of grains. For $l\ge1$ and an integer $m$, the *measuring device* $\beta^m_l(n)$ equals $n-m$ if $|n-m|\le l$, and $+\infty$ (respectively $-\infty$) if $n>m+l$ (respectively $n<m-l$); for a column $i$ with $c_i$ finite, $d^i_l(c)$ is the vector $(\beta^{c_i}_l(c_{i-l}),\dots,\beta^{c_i}_l(c_{i-1}),\beta^{c_i}_l(c_{i+1}),\dots,\beta^{c_i}_l(c_{i+l}))$ of measured differences to the $2l$ neighboring columns. A *sand automaton* $\langle r,\lambda\rangle$, given as an instance by $r$ and the finite table of $\lambda$, has a radius $r\ge1$ and a local rule $\lambda:\widetilde{[-r,r]}^{2r}\to[-r,r]$, and its global map is

$$
f(c)_i=\begin{cases}c_i&\text{if }c_i=\pm\infty,\\ c_i+\lambda(d^i_r(c))&\text{otherwise.}\end{cases}
$$

For a set $\mathfrak U$ of configurations, $f$ is *$\mathfrak U$-nilpotent* if for every $c\in\mathfrak U$ there is $n$ with $f^n(c)=\underline0$, the configuration with no grains. The problem $\mathbf{NIL}(\mathfrak U)$ asks, given a sand automaton, whether it is $\mathfrak U$-nilpotent.

**Theorem (Cervelle, Formenti and Masson).** $\mathbf{NIL}(\mathcal F)$ is undecidable (Theorem 18).

Theorem 18 of the source also states the undecidability of $\mathbf{NIL}(\mathcal P)$ for the periodic configurations, but that half is not stated here, because no sand automaton is nilpotent on periodic configurations. A constant configuration $\bar h$, every column equal to $h \in \mathbb Z$, is periodic, all its measured differences are $0$, and so $f^n(\bar h) = \overline{h + n\lambda_0}$ with $\lambda_0 = \lambda(0, \dots, 0)$; reaching $\underline 0$ from $\bar 1$ needs $\lambda_0 < 0$ and from $\overline{-1}$ needs $\lambda_0 > 0$. So $\mathbf{NIL}(\mathcal P)$ has answer no on every instance; a meaningful periodic version would need a smaller class of configurations, and the source's proof sketch, which repeats a finite configuration periodically, only shows that a configuration that never vanishes carries over.

For cellular automata, the undecidability of nilpotency ([nilpotency of cellular automata is undecidable](nilpotency-of-cellular-automata-is-undecidable.md)) is a basic tool; the source stresses that sand automata are not a sub-model of cellular automata, and proves the theorem directly by simulating counter machines.

## Depends on

- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem on empty input for two-counter machines with a finite control. A sand automaton represents the finite control and each counter by stacks of grains; for each counter, three stacks carry commands from the control to the top of the counter stack and back (a reference stack, a direction stack and a command stack for increment or decrement), zero tests being read off the stack heights, and further stacks record the step of the computation and the role of each stack. When the halting state is reached the configuration is erased to $\underline0$, and configurations that do not encode a correct state of the simulation, either because a value is out of range or because the stacks are not arranged as in a simulation, are erased as well. So the automaton is $\mathcal F$-nilpotent exactly when the machine halts.

## Sources

- J. Cervelle, E. Formenti and B. Masson, "Basic properties for sand automata", in *Mathematical Foundations of Computer Science 2005 (MFCS 2005)*, Lecture Notes in Computer Science 3618, pp. 192–211, Springer, 2005, doi:[10.1007/11549345_18](https://doi.org/10.1007/11549345_18); read in arXiv:cs/0411007v1 ([arXiv](https://arxiv.org/abs/cs/0411007v1)), whose numbering is used: the configurations and the topology of Section 2, the definition of sand automata in Section 3, and Theorem 18 with its proof sketch in Section 6 (Nilpotency).
