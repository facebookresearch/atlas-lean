# Every context-free language is a projection of a visibly pushdown language

For every [context-free language](../grammars-and-pushdown-automata/context-free-languages.md) $L$ over $\Sigma$ there is a [visibly pushdown language](visibly-pushdown-automata.md) $L'$ over the pushdown alphabet
$\langle \Sigma \times \{c\}, \Sigma \times \{r\}, \Sigma \times \{\ell\} \rangle$ with $L = h(L')$, where $h$ maps each symbol $(a, s)$ to $a$. Given a pushdown automaton for $L$ without $\varepsilon$-moves in which
every step pushes one symbol, pops one symbol or leaves the stack unchanged (one exists for every context-free language, accepting the empty word by an initial final state if needed), relabel each $a$-transition that pushes by $(a, c)$, each one that pops by $(a, r)$ and the others by
$(a, \ell)$; the resulting VPA accepts the words of $L$ annotated with the stack operations used to accept them.

## Depends on

- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)
- [Context-free languages](../grammars-and-pushdown-automata/context-free-languages.md)

## Proof depends on

- [Context-free languages are accepted by pushdown automata](../grammars-and-pushdown-automata/pushdown-automata-and-context-free-grammars/exists-pda-accepts.md)

## Expansion

This page becomes ready once:

- The normal form of pushdown automata without $\varepsilon$-moves, accepting by final state, in which every step pushes one symbol, pops one symbol or leaves the stack unchanged (proof prerequisite; not yet stated)

## Sources

- R. Alur and P. Madhusudan, "Visibly pushdown languages", *Proceedings of the 36th ACM STOC*, 2004; full version of August 2005, whose numbering is cited, <https://www.cis.upenn.edu/~alur/Stoc04.pdf>: Section 2.1, Proposition 1 (embedding context-free languages as VPLs) with its proof.
- R. Alur and P. Madhusudan, "Adding nesting structure to words", *Journal of the ACM* 56(3), 2009, author copy <https://www.cis.upenn.edu/~alur/Jacm09.pdf>: Theorem 5.2 (relation between CFLs and VPLs).
