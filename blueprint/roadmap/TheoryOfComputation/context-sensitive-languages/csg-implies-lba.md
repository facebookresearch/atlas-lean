# Every context-sensitive grammar over a finite alphabet has an LBA recognizing it

The following holds. Let $\Gamma$ be a finite terminal alphabet, $N$ a type of nonterminals, and $g$ a [context-sensitive grammar](context-sensitive-grammars/is-context-sensitive.md) over $\Gamma$ with nonterminals $N$: every production has a nonterminal on its left side and a right side at least as long as its left side, without exception, so no production $S \to \varepsilon$ is allowed and $\varepsilon \notin L(g)$. Then there are a finite tape alphabet $\Sigma$, an injective map $e : \Gamma \to \Sigma$, a finite set $Q$ of states and a nondeterministic linear bounded automaton $M$ with states $Q$ over $\Sigma$ such that

$$L(g) = \{\, w \in \Gamma^* : M \text{ accepts } e(w_1) e(w_2) \cdots e(w_{|w|}) \,\}.$$

The automaton works within the cells of its input, sees whether its head is at the left end, the right end or an interior cell, and may write symbols of $\Sigma$ (or blank) that are not images of input letters, which leaves room for nonterminals and markers. The context-sensitivity hypothesis matters: for unrestricted grammars the statement fails.

## Sources

- J. E. Hopcroft and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, Addison-Wesley, 1979, §9.3, Theorem 9.5.
