# Context-sensitive membership is decidable, in PSPACE

The following holds. Let $g$ be a context-sensitive grammar over the binary terminal alphabet $\{0, 1\}$, with any type of nonterminals. Then membership $w \in L(g)$ for $w \in \{0,1\}^*$ is a computable predicate, and $L(g)$ belongs to $\mathsf{PSPACE}$, the class of languages decided by deterministic multi-tape Turing machines in polynomial space.

The context-sensitivity hypothesis matters: for unrestricted grammars membership need not be decidable.

## Sources

- J. E. Hopcroft and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, Addison-Wesley, 1979, §9.3, Theorem 9.5 (a linear bounded automaton recognizes the language, hence nondeterministic linear space).
- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §8.2 (Savitch's theorem).
