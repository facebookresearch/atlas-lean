# Copyless cost register automata

A cost register automaton is a deterministic automaton with registers holding semiring values, updated at each letter by expressions in the old register values; it is copyless when each old register value is used at most once per update.

Let $S$ be a semiring and $\mathcal X$ a finite set of registers. A *cost register automaton* (CRA) over $S$ is a tuple $(\Sigma,Q,q_0,I,F,\mathcal X,\delta)$ with a finite alphabet $\Sigma$, a finite set $Q$ of states with initial state $q_0$, initial register values $I:\mathcal X\to S$, final coefficients $F:Q\times\mathcal X\to S$, and a deterministic transition function $\delta$ that maps $(q,a)\in Q\times\Sigma$ to a state $q'$ and an update giving each register a new value as an expression built from constants of $S$ and the old register values with $\oplus$ and $\odot$. A configuration is a pair $(q,\sigma)$ of a state and a valuation $\sigma\in S^{\mathcal X}$; each word $w$ determines a single run, and if it ends in $(q,\sigma_w)$ the output is $\mathcal B(w)=\bigoplus_{x\in\mathcal X}F[q,x]\odot\sigma_w(x)$.

The CRA is *linear* if every update is affine, $c\oplus\bigoplus_{x}s_x\odot x$; linear CRA define exactly the functions of weighted automata. An update is *copyless* if every register occurs at most once across all the expressions of the update, and a CRA is *copyless* if all its updates are. Copyless updates may multiply registers, as in $z\leftarrow c\odot z\odot\bigoplus_x F(q,x)\odot x$. Copyless linear CRA are contained in copyless CRA, which are contained in linear CRA (Mazowiecki and Riveros).

## Depends on

- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)
- [Semirings and formal power series on a free monoid](../semirings-and-formal-power-series.md)

## Proof depends on

None.

## Expansion

Copyless linear CRA define functions of linearly ambiguous weighted automata; copyless CRA lie strictly between the finitely ambiguous and the full class of weighted automata in expressiveness, as the source recalls. The decision problems of the boundedness page (thresholds, boundedness, zero isolation) apply to any function $\Sigma^*\to S$, so to CRA.

## Sources

- Wojciech Czerwiński, Engel Lefaucheux, Filip Mazowiecki, David Purser and Markus A. Whiteland, "The boundedness and zero isolation problems for weighted automata over nonnegative rationals", in *Proceedings of the 37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, pp. 1–13, doi:[10.1145/3531130.3533336](https://doi.org/10.1145/3531130.3533336); read in arXiv:2205.13516v1 ([arXiv](https://arxiv.org/abs/2205.13516v1)), whose numbering is used: Section 2.2 (cost register automata, linear and copyless restrictions) and the reduction of Lemma E.2 in Appendix E, whose updates multiply registers.
