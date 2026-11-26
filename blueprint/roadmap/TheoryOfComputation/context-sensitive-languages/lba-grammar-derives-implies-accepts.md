# Soundness of the grammar of an LBA

Let $M$ be a nondeterministic linear bounded automaton with a finite set $Q$ of states and a finite tape alphabet $\Gamma$: its tape is the input word, its transitions depend on the state, the symbol under the head and whether the head is at an end of the tape, and it accepts $w$ if some run from the initial configuration on $w$ reaches the accepting state. Let $G_M$ be the grammar associated with $M$ by the standard construction: its productions generate a word together with an encoding of the corresponding tape cells, activate the initial configuration, simulate the moves of $M$ on the encoded cells, and convert the cells back to terminal letters once the accepting state appears.

The following holds: for every nonempty word $w \in \Gamma^*$, if $G_M$ derives $w$, then $M$ accepts $w$.

Together with the converse inclusion (every nonempty word accepted by $M$ is derived by $G_M$), this gives $L(M) \setminus \{\varepsilon\} = L(G_M) \setminus \{\varepsilon\}$.

## Sources

- M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §5.1.
- J. E. Hopcroft, R. Motwani, and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, 3rd ed., Pearson, 2007, §11.1.
