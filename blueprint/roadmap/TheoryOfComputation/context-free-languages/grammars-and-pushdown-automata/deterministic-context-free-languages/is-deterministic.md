# Deterministic pushdown automaton

Let $M$ be a pushdown automaton with input alphabet $T$, state set $\sigma$ and stack alphabet $\Gamma$, whose
transition function assigns to each state $q$, each input $a \in T$ or $\varepsilon$, and each top stack symbol
$\gamma$ a finite set $\delta(q, a, \gamma)$ of pairs (next state, word pushed in place of $\gamma$). Then $M$ is
deterministic if $|\delta(q, \varepsilon, \gamma)| \le 1$ and $|\delta(q, a, \gamma)| \le 1$ for all $q$, $a \in T$
and $\gamma$, and, whenever $\delta(q, \varepsilon, \gamma)$ is nonempty, $\delta(q, a, \gamma) = \emptyset$ for
every $a \in T$.

## Sources

- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage Learning, 2013, Chapter 2 (deterministic pushdown automata); J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, 3rd ed., Addison-Wesley, 2006, Section 6.4.
