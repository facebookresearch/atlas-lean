# Copyless cost register automata over the tropical semirings

A tropical cost register automaton is a deterministic automaton whose registers, holding integers or infinity, are updated by minima of
registers plus constants; it is copyless when each register's old value flows into at most one new register value.

Let $\mathbb{K}$ be $\mathbb{Z}_\infty = \mathbb{Z} \cup \{\infty\}$ or $\mathbb{N}_\infty = \mathbb{N} \cup \{\infty\}$ with the operations $\min$ and $+$ (the tropical semirings), with
$\min \emptyset = \infty$. A *cost register automaton* over $\mathbb{K}$ ($\mathbb{K}$-CRA) of dimension $k$ is a deterministic finite automaton equipped with registers
$r_1, \dots, r_k$ with values in $\mathbb{K}$, initial register values in $\mathbb{K}^k$, and for each transition an update

$$
r_i \leftarrow \min\{ r_1 + m_{1,i},\ r_2 + m_{2,i},\ \dots,\ r_k + m_{k,i},\ m_{k+1,i} \} \qquad (i \in [k]),
$$

with constants $m_{j,i} \in \mathbb{K}$, all registers being updated simultaneously; as an input, an automaton is given by its finite tables, each constant written as an integer in binary or as $\infty$; each final state carries an output expression
$\min\{r_1 + m_1, \dots, r_k + m_k, m_{k+1}\}$. The value $\mathcal{C}(w)$ of a word $w$ is $\infty$ if the underlying automaton rejects $w$, and otherwise the output
expression of the final state evaluated after updating the registers along the unique run on $w$. The automaton is *copyless* ($\mathbb{K}$-CCRA) if every update
satisfies $|\{ i : m_{j,i} \ne \infty \}| \le 1$ for each register $r_j$, so that the old value of each register influences at most one new value.

A *weighted automaton* over $\mathbb{K}$ is a nondeterministic automaton with weights in $\mathbb{K}$ on its transitions, an initial weight and final weights; the value of
a word is the minimum, over accepting runs, of the sum of the weights, and $\infty$ if there is none. Every $\mathbb{K}$-CCRA is equivalent to a linearly ambiguous
weighted automaton over $\mathbb{K}$.

## Depends on

- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)
- [Semirings and formal power series on a free monoid](../semirings-and-formal-power-series.md)

## Proof depends on

None.

## Sources

- S. Almagor, M. Cadilhac, F. Mazowiecki and G. A. Pérez, "Weak cost register automata are still powerful", *International Journal of Foundations of Computer Science* 31(6):689–709, 2020, doi:10.1142/S0129054120410026; conference version in *Developments in Language Theory (DLT 2018)*, Lecture Notes in Computer Science 11088, pp. 83–95, 2018, doi:10.1007/978-3-319-98654-8_7. Read in arXiv:1804.06336v1: Section 2 (tropical semirings, weighted automata and cost register automata over $\mathbb{Z}_\infty$ and $\mathbb{N}_\infty$, copylessness) and Proposition 2 (the normal form) of Section 3, with the numbering of that version.
