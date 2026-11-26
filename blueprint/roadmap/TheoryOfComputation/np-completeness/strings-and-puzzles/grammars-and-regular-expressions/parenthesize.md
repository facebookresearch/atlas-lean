# Parenthesized grammar

The parenthesized grammar of $(n, s, P)$ for a number $k$: every production $A \to w$ is replaced by $A \to (w)$, where $($ is terminal $k$ and $)$ is terminal $k + 1$, and the nonterminals and initial symbol are unchanged. Terminals already in a production are kept as they are, so the result is a grammar over $\{0, \dots, k + 1\}$ only when the input grammar uses terminals below $k$; for $k = 1$ a terminal $7$ survives.
