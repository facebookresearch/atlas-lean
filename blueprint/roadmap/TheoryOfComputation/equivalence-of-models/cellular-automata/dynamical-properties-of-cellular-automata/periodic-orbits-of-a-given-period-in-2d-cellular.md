# Periodic orbits of a given period in two-dimensional cellular automata are undecidable

For every period p, no algorithm decides whether a given two-dimensional cellular automaton has a configuration that returns to itself after p steps, although every cellular automaton has some periodic configuration of period at most its number of states.

**Setting.** Let $F$ be a two-dimensional [cellular automaton](../cellular-automata-on-z-d.md) with a finite set $A$ of states, acting on configurations $c\in A^{\mathbb Z\times\mathbb Z}$; as an instance it is given by $A$, a finite neighborhood and the table of its local rule. For $p\ge1$ its *period-$p$ set* is

$$
\Pi^p=\{c\in A^{\mathbb Z\times\mathbb Z}\mid F^p(c)=c\},
$$

and its *periodic set* is $\Pi=\bigcup_{p\ge1}\Pi^p$. A *local lattice language* (LLL) is the set of configurations of $A^{\mathbb Z\times\mathbb Z}$ in which every block of a given finite shape belongs to a given finite set of allowed blocks.

**Theorem (Lindgren, Moore and Nordahl).** Let $L$ be an LLL over an alphabet $A$ with $\lvert A\rvert\ge2$. There is a cellular automaton on $A^{\mathbb Z\times\mathbb Z}$ whose fixed-point set $\Pi^1$ is $L$; and for every $p\ge2$ there is a cellular automaton on $(A\times\{0,\dots,p\})^{\mathbb Z\times\mathbb Z}$ whose period-$p$ set is $L\times\{0,\dots,p-1\}^{\mathbb Z\times\mathbb Z}$, which is nonempty exactly when $L$ is. Both automata are computable from $L$ and $p$. Therefore, for each fixed $p\ge1$, it is undecidable, given a two-dimensional cellular automaton, whether it has a configuration $c$ with $F^p(c)=c$, that is, whether $\Pi^p$ is nonempty. (Configurations of least period dividing $p$ count; the source's period-$p$ set is defined by $F^p(c)=c$.) The source states that the period-$p$ set of its automaton for $p\ge2$ is the LLL itself; what its construction gives is the product above, which suffices for the undecidability.

Since homogeneous configurations are mapped to homogeneous configurations, a cellular automaton with $k$ states always has a periodic orbit of some period $p\le k$, so the question whether $\Pi$ is nonempty is trivial. Conversely, the period-$p$ set of a cellular automaton of radius $r$ is itself an LLL, of range $2pr+1$.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Remarks

For $p=1$, let the automaton change the state of a cell exactly when the cell belongs to a forbidden block of the LLL; then a configuration is fixed if and only if it contains only allowed blocks. For $p\ge2$, enlarge the alphabet to $A\times\{0,\dots,p\}$, keep the first component, and let the second component $n$ become $(n+1)\bmod(p+1)$ at cells whose first component lies in a forbidden block and $(n+1)\bmod p$ elsewhere. Forbidden status depends only on the first components, which never change. A cell in a forbidden block has period $p+1$, so a configuration with such a cell is not in $\Pi^p$; a cell outside forbidden blocks with second component $p$ moves to $1$ and never returns to $p$; and a configuration whose first components form a configuration of $L$ and whose second components lie in $\{0,\dots,p-1\}$ has period $p$. Hence $\Pi^p=L\times\{0,\dots,p-1\}^{\mathbb Z\times\mathbb Z}$. Wang tile sets are special LLLs, so by the undecidability of the tiling problem it is undecidable whether an LLL is nonempty, and hence whether $\Pi^p$ is nonempty.

## Sources

- Kristian Lindgren, Cristopher Moore and Mats Nordahl, "Complexity of two-dimensional patterns", *Journal of Statistical Physics* 91(5–6), pp. 909–951, 1998, doi:[10.1023/A:1023027932419](https://doi.org/10.1023/A:1023027932419); read in arXiv:cond-mat/9804071v1 ([arXiv](https://arxiv.org/abs/cond-mat/9804071v1)), whose sectioning is used: the definition of LLLs in Section 2.2, the discussion of extensibility and the tiling problem in Section 2.7, the definition of period-$p$ sets in Section 3.1, and the propositions of Section 3.2 ("Periodic sets"), which are unnumbered, with their proofs and the remark after them.
