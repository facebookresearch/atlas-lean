# Sound items for a grammar and a DFA

For an encoded grammar $g$ and an encoded DFA $D$, a
natural number $x$ is a sound item when there are natural numbers $A$, $p$, $q$ and a word $w$
such that $x = \langle A, \langle p, q \rangle \rangle$, where $\langle \cdot, \cdot \rangle$ is the
natural-number pairing, the nonterminal $A$ yields $w$ in the grammar denoted by $g$, and the
automaton denoted by $D$, run on $w$ from state $p$, ends in state $q$.
