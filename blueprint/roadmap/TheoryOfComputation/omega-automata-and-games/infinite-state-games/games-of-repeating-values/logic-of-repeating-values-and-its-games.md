# The logic of repeating values and its games

The logic of repeating values extends linear temporal logic with past by tests that a data value held by a variable now reappears, in some variable, at a later or an earlier position. In its games, an environment player and a system player alternately choose the values of their own variables, and the system wins if the resulting infinite sequence satisfies a given formula.

**Syntax and semantics.** Let $\mathrm{BV}$ be a countable set of Boolean variables, ranging over $\{\top, \bot\}$, and $\mathrm{DV}$ a countable set of data variables, ranging over an infinite domain $\mathbb{D}$. Formulas of LRV are

$$
\phi ::= q \mid x \approx \mathsf{X}^j y \mid x \approx \langle \phi ? \rangle y \mid x \not\approx \langle \phi ? \rangle y \mid x \approx \langle \phi ? \rangle^{-1} y \mid x \not\approx \langle \phi ? \rangle^{-1} y \mid \phi \land \phi \mid \lnot \phi \mid \mathsf{X} \phi \mid \phi \mathbin{\mathsf{U}} \phi \mid \mathsf{X}^{-1} \phi \mid \phi \mathbin{\mathsf{S}} \phi
$$

with $q \in \mathrm{BV}$, $x, y \in \mathrm{DV}$ and $j \in \mathbb{Z}$. A model is a finite or infinite sequence $\sigma$ of valuations of all variables, with positions $1, 2, \dots$. Besides the usual clauses for the Boolean and temporal operators, $\sigma, i \models x \approx \mathsf{X}^j y$ if $1 \le i + j \le |\sigma|$ and $\sigma(i)(x) = \sigma(i+j)(y)$; $\sigma, i \models x \approx \langle \phi ? \rangle y$ if there is $j > i$ with $\sigma(i)(x) = \sigma(j)(y)$ and $\sigma, j \models \phi$ (a *future obligation*); $x \not\approx \langle \phi ? \rangle y$ asks instead for $\sigma(i)(x) \ne \sigma(j)(y)$; and the forms with $^{-1}$ ask for such a $j < i$ (*past obligations*). Fragments are written with symbols in brackets: $\top$ forbids nested formulas (the formula inside $\langle \cdot ? \rangle$ must be $\top$, written $x \approx \Diamond y$), $\approx$ forbids the disequality obligations $\not\approx$, $\rightarrow$ forbids past obligations and $\leftarrow$ forbids future obligations. For example $\mathrm{LRV}[\top, \approx, \rightarrow]$ has only non-nested future equality obligations, besides local tests $x \approx \mathsf{X}^j y$ and full LTL with past.

**Games.** The Boolean and data variables are partitioned between the players *environment* and *system*. In each round, environment first chooses values for all its variables and system then chooses values for all of its own; the infinite play is the model $\sigma = (v^e_1 \oplus v^s_1)(v^e_2 \oplus v^s_2) \cdots$ of the combined valuations. A strategy of environment maps the finite history to its next valuation, and a strategy of system maps the history together with environment's current valuation to system's next valuation. Given a formula $\phi$, system wins a play if $\sigma, 1 \models \phi$, and a strategy of system is winning if it wins against every strategy of environment. The *winning strategy existence problem* asks, given $\phi$ in a fragment of LRV, whether system has a winning strategy. A game is *single-sided* if the formula uses no data variable of environment: of environment's variables it uses only Boolean ones, while it may use data variables of system.

Satisfiability of LRV is related to control-state reachability in vector addition systems, and LRV games to games on vector addition systems with states. Single-sided $\mathrm{LRV}[\top, \leftarrow]$ games, with only past obligations, are decidable, by a reduction to single-sided games on vector addition systems with states.

## Depends on

- [Formulas of linear temporal logic](../../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [Satisfaction of LTL formulas on ω-words](../../../../Logic/temporal-logic/linear-temporal-logic/satisfies.md)

## Proof depends on

None.

## Sources

- D. Figueira, A. Majumdar and M. Praveen, "Playing with Repetitions in Data Words Using Energy Games", *Logical Methods in Computer Science* 16(3):1, 2020, doi:10.23638/LMCS-16(3:1)2020, <https://lmcs.episciences.org/4898>; numbering of arXiv:1802.07435v7: the syntax, semantics (Table 1) and fragments of LRV in Section 2, the game of repeating values in Section 3, and the decidability of single-sided $\mathrm{LRV}[\top, \leftarrow]$ games in Section 5.
