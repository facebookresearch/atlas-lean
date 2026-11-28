# Periodic orbits of a given period in two-dimensional cellular automata are undecidable

For every period p, no algorithm decides whether a given two-dimensional cellular automaton has a configuration that returns to itself after p steps, although every cellular automaton has some periodic configuration of period at most its number of states.

**Setting.** Let $F$ be a two-dimensional [cellular automaton](../cellular-automata-on-z-d.md) with a finite set $A$ of states, acting on configurations $c\in A^{\mathbb Z\times\mathbb Z}$; as an instance it is given by $A$, a finite neighborhood and the table of its local rule. For $p\ge1$ its *period-$p$ set* is

$$
\Pi^p=\{c\in A^{\mathbb Z\times\mathbb Z}\mid F^p(c)=c\},
$$

and its *periodic set* is $\Pi=\bigcup_{p\ge1}\Pi^p$. A *local lattice language* (LLL) is the set of configurations of $A^{\mathbb Z\times\mathbb Z}$ in which every block of a given finite shape belongs to a given finite set of allowed blocks.

**Theorem (Lindgren, Moore and Nordahl).** For every LLL and every $p\ge1$ there is a cellular automaton whose period-$p$ set is that LLL. Therefore, for each fixed $p\ge1$, it is undecidable, given a two-dimensional cellular automaton, whether it has a configuration $c$ with $F^p(c)=c$, that is, whether $\Pi^p$ is nonempty. (Configurations of least period dividing $p$ count; the source's period-$p$ set is defined by $F^p(c)=c$.)

Since homogeneous configurations are mapped to homogeneous configurations, a cellular automaton with $k$ states always has a periodic orbit of some period $p\le k$, so the question whether $\Pi$ is nonempty is trivial. Conversely, the period-$p$ set of a cellular automaton of radius $r$ is itself an LLL, of range $2pr+1$.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

For $p=1$, let the automaton change the state of a cell exactly when the cell belongs to a forbidden block of the LLL; then a configuration is fixed if and only if it contains only allowed blocks. For $p>1$, enlarge the alphabet to $A\times\{0,\dots,p\}$ and let the second component count modulo $p+1$ at cells in a forbidden block and modulo $p$ elsewhere, leaving the first component unchanged; every configuration is then periodic, the configurations with only allowed blocks have period $p$, and all others have period $p+1$ or $p(p+1)$, so $\Pi^p$ is the given LLL. Wang tile sets are special LLLs, so by the undecidability of the tiling problem it is undecidable whether an LLL is nonempty, and hence whether $\Pi^p$ is nonempty.

## Sources

- Kristian Lindgren, Cristopher Moore and Mats Nordahl, "Complexity of two-dimensional patterns", *Journal of Statistical Physics* 91(5–6), pp. 909–951, 1998, doi:[10.1023/A:1023027932419](https://doi.org/10.1023/A:1023027932419); read in arXiv:cond-mat/9804071v1 ([arXiv](https://arxiv.org/abs/cond-mat/9804071v1)), whose sectioning is used: the definition of LLLs in Section 2.2, the discussion of extensibility and the tiling problem in Section 2.7, the definition of period-$p$ sets in Section 3.1, and the propositions of Section 3.2 ("Periodic sets"), which are unnumbered, with their proofs and the remark after them.
