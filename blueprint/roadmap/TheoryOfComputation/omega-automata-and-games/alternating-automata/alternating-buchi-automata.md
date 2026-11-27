# Alternating Büchi automata

An *alternating Büchi automaton* is an [alternating automaton](alternating-automata-on-finite-words.md) $\mathcal{A} = (\Sigma, S, s_0, \rho, F)$ read on
infinite words. A run on $a_0 a_1 \cdots$ is a possibly infinite tree labelled by states, with root labelled $s_0$, in which every node at depth $i$
labelled $s$ has children whose labels satisfy $\rho(s, a_i)$; a node with $\rho(s, a_i) = \mathrm{true}$ needs no children. The run is accepting if every
infinite branch carries infinitely many labels in $F$. Every nondeterministic [Büchi automaton](../emptiness-of-b-chi-automata/mem-language-iff.md) is an alternating Büchi automaton of essentially
the same size with the same language.

## Depends on

- [Alternating automata on finite words](alternating-automata-on-finite-words.md)
- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, Lecture Notes in Computer Science 1043, Springer, 1996, pp. 238–266; numbering from the author's posted version, <https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf>: Section 2.6, the definition of alternating Büchi automata and their runs, and Proposition 19 (Muller and Schupp).
