# Domino-independent productions of the universality grammar

For a finite alphabet
$\alpha$ and $k \in \mathbb{N}$, this is a list of productions whose nonterminals $N_0, N_1, \dots$
are encoded as natural numbers and whose terminals are the letters $a \in \alpha$ and the two bits
$\mathbf{t}$ (true) and $\mathbf{f}$ (false). Writing $c(i) = \mathbf{t}\,\mathbf{f}^i$ for the
unary code of an index $i$, the list consists of the productions $N_3 \to \varepsilon$,
$N_5 \to \varepsilon$, $N_6 \to \varepsilon$, $N_7 \to \varepsilon$; $N_5 \to \mathbf{t}\,N_5$,
$N_5 \to \mathbf{f}\,N_5$, $N_6 \to \mathbf{t}\,N_6$, $N_6 \to \mathbf{f}\,N_6$;
$N_0 \to N_3$, $N_0 \to N_3\,\mathbf{f}\,N_5$, $N_0 \to N_6\,c(k)\,N_6$, $N_0 \to N_1$,
$N_0 \to N_2$; for each letter $a \in \alpha$, the productions $N_3 \to a\,N_3$,
$N_4 \to a\,N_3$, $N_6 \to a\,N_6$, $N_0 \to N_6\,\mathbf{t}\,a\,N_6$ and
$N_0 \to N_6\,\mathbf{f}\,a\,N_6$; and for each $i < k$, the production $N_7 \to c(i)\,N_7$.

The nonterminal $N_0$ is the start symbol. The intended languages are: for $N_3$ the words of
letters, for $N_4$ the nonempty words of letters, for $N_5$ the words of bits, for $N_6$ all
words, and for $N_7$ the concatenated codes of indices below $k$. The start productions (those
with left side $N_0$) generate the malformed words and the two mismatch nonterminals $N_1$ and
$N_2$.
