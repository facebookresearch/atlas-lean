# Chain of triple nonterminals

Write $(p, \gamma, q)$ for the nonterminal symbol given by
states $p, q$ and a stack symbol $\gamma$ (the nonterminals of the triple grammar are these
triples and one extra initial nonterminal). The chain form of a list $\gamma_1 \cdots \gamma_k$
of stack symbols along a nonempty list $s_0, s_1, \dots, s_m$ of states is the word
$(s_0, \gamma_1, s_1)(s_1, \gamma_2, s_2) \cdots (s_{j-1}, \gamma_j, s_j)$ with $j = \min(k, m)$:
consecutive states bracket each stack symbol. Along the empty list of states the chain form is
the empty word. In the intended use $m = k$, so every stack symbol is bracketed.
