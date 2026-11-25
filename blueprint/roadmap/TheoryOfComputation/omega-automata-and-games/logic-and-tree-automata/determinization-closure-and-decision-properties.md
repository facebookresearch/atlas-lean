# Determinization, closure and decision properties of regular tree languages

Let $\mathcal{F}$ be a ranked alphabet.

1. **Determinization.** For every recognizable set $L$ of ground terms over $\mathcal{F}$ there is a deterministic finite tree automaton that accepts $L$. The states of the deterministic automaton are sets of states of a given nondeterministic one.
2. **Boolean closure.** The recognizable tree languages over $\mathcal{F}$ are closed under union, complementation and intersection.
3. **Decision problems.** Emptiness of the language of a finite tree automaton is decidable in linear time. Membership of a given ground term in the language of a given automaton is decidable in linear time for deterministic and in polynomial time for nondeterministic automata.
4. **Yields.** For a context-free word grammar $G$, the set of derivation trees of $G$ is a regular tree language, whose yields (frontier words) form the language of $G$. Conversely, the set of yields of any regular tree language is a context-free word language. Hence a word language is context-free exactly when it is the set of yields of a regular tree language. Not every regular tree language is the set of derivation trees of a context-free grammar.

## Depends on

- [Bottom-up finite tree automata](bottom-up-finite-tree-automata.md)
- [Language generated from a nonterminal](../../context-free-languages/grammars-and-pushdown-automata/context-free-grammars/language-from.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Theorem 1.1.9 (equivalence of DFTAs and NFTAs), Theorem 1.3.1 (closure under union, complementation and intersection), Theorems 1.7.3 and 1.7.4 (uniform membership and emptiness), and Theorem 2.4.3 (derivation trees and yields of context-free word grammars).
- J. W. Thatcher and J. B. Wright, "Generalized finite automata theory with an application to a decision problem of second-order logic", *Mathematical Systems Theory* 2(1):57–81, 1968.
