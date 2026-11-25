# Context-sensitive membership is decidable, in PSPACE

The following holds. Let $g$ be a context-sensitive grammar over the binary terminal alphabet $\{0, 1\}$, with any type of nonterminals. Then membership $w \in L(g)$ for $w \in \{0,1\}^*$ is a computable predicate, and $L(g)$ belongs to $\mathsf{PSPACE}$, the class of languages decided by deterministic multi-tape Turing machines in polynomial space.

The context-sensitivity hypothesis matters: for unrestricted grammars membership need not be decidable.

## Sources

- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §5.1 (Theorem 5.9) and §8.2 (Savitch's theorem).
- J. E. Hopcroft, R. Motwani, and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, 3rd ed., Pearson, 2007, §11.1.
