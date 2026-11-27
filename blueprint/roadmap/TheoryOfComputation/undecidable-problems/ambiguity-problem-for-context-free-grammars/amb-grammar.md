# The ambiguity grammar of a PCP instance

Let $P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$
be a list of dominoes over an alphabet $\alpha$, with top words $t_i$ and bottom words $b_i$. The
ambiguity grammar of $P$ is the encoded context-free grammar over the terminals
$\alpha \sqcup \mathbb{N}$ (letters and indices) with nonterminals $S = 0$, $A = 1$, $B = 2$, start
symbol $S$, and the productions $S \to A$ and $S \to B$ together with, for every $i < m$, the
productions $A \to t_i\, A\, i$, $A \to t_i\, i$, $B \to b_i\, B\, i$ and $B \to b_i\, i$, in which
the index $i$ is a terminal.
