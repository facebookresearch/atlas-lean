# Decision problems for two-head finite automata are not semi-decidable

For every $k \ge 2$, emptiness, finiteness, infiniteness, universality, inclusion, equivalence, regularity and
context-freeness are not even semi-decidable for $k$-head finite automata, already for deterministic one-way ones.

Let $k \ge 2$ and let $X$ be one of the classes $\mathrm{1DFA}(k)$, $\mathrm{1NFA}(k)$, $\mathrm{2DFA}(k)$, $\mathrm{2NFA}(k)$
of [multi-head finite automata](multi-head-finite-automata.md). For automata of class $X$ given as input, none of the following
problems is semi-decidable (recursively enumerable): emptiness of $L(M)$, finiteness, infiniteness, universality, inclusion
$L(M_1) \subseteq L(M_2)$, equivalence $L(M_1) = L(M_2)$, regularity of $L(M)$, and context-freeness of $L(M)$. In particular
all of them are undecidable.

The number of heads $k$ is fixed. For one head the automata accept exactly the regular languages, and all these problems are
decidable. Two consequences recorded by the source: no algorithm converts an automaton of class $X$ into an equivalent one of
the same class with the minimal number of states, and no language family with semi-decidable word problem that effectively
contains $\mathscr{L}(X)$ has a pumping lemma. The problems become decidable for automata with a constant number of head
reversals that accept letter-bounded languages, and stay undecidable for such automata on arbitrary languages.

## Depends on

- [Multi-head finite automata](multi-head-finite-automata.md)
- [Context-free languages](../../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)

## Proof depends on

- [The halting problem is not co-recognizable by multi-stack machines](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-co-recognizable-halting.md)

## Expansion

For a Turing machine $M$, the set $\mathrm{VALC}(M)$ of valid accepting computations, written as words
$\# w_0 \# w_1 \# \cdots \# w_m \#$ of successive configurations from an initial to an accepting one, is accepted by a
deterministic one-way two-head automaton: one head reads $w_i$ while the other reads $w_{i+1}$, and the automaton checks
symbol by symbol that $w_{i+1}$ is a successor of $w_i$, while a finite-state check verifies the overall form of the word.
Hence $L(M)$ is empty exactly when $\mathrm{VALC}(M)$ is empty, finite exactly when $\mathrm{VALC}(M)$ is finite, and so on,
and the properties of Turing machines that are not semi-decidable transfer to the multi-head automata.

## Sources

- M. Holzer, M. Kutrib and A. Malcher, "Multi-head finite automata: characterizations, concepts and open problems", in *Complexity of Simple Programs (CSP 2008)*, Electronic Proceedings in Theoretical Computer Science 1, pp. 93–107, 2009, doi:10.4204/EPTCS.1.9; numbering of the version arXiv:0906.3051v1: Theorem 15, Example 9 (two heads accept the valid computations), Theorems 16 and 17 (pumping lemmas and minimization), and Theorem 20 (bounded languages).
