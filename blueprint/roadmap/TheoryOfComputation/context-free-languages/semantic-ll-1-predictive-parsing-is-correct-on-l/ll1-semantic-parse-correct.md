# Correctness of LL(1) predictive parsing

The following holds. Let $g$ be an LL(1) context-free grammar over a terminal alphabet $T$ with decidable equality, with start symbol $S$, and let $w \in T^*$. Then

$$\bigl(\exists k \in \mathbb{N}:\ \mathrm{parse}(k, S, w) = \mathrm{true}\bigr) \iff w \in L(g),$$

where $\mathrm{parse}(k, \gamma, w)$ is the LL(1) predictive parser with step budget $k$, started with the stack containing only $S$: it matches terminals on top of the stack against the input and expands a nonterminal on top by the LL(1) table entry for the next input letter (or the end of input), accepting when stack and input become empty together.

## Sources

- A. V. Aho, M. S. Lam, R. Sethi, and J. D. Ullman, *Compilers: Principles, Techniques, and Tools*, 2nd ed., Chapter 4.
- J. E. Hopcroft, R. Motwani, and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, 3rd ed., Chapter 5.
