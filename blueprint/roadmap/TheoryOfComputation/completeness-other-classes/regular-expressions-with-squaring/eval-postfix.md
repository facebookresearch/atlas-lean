# Evaluation of postfix regular expressions with squaring

A list of natural-number tokens
is evaluated from left to right on a given stack of languages of bitstrings. Token $0$ pushes the
empty language, token $1$ pushes the language containing only the empty bitstring, and tokens $2$
and $3$ push the languages containing only the one-letter bitstring false, respectively true.
Token $4$ pops the top language $S$ and the language $T$ below it and pushes the concatenation
$TS$; token $5$ pops $S$ and $T$ in the same way and pushes $T \cup S$; token $6$ pops $S$ and
pushes its Kleene star; token $7$ pops $S$ and pushes its square $SS$. When the tokens run out,
the evaluation returns the language on the stack if the stack holds exactly one language. It
fails if the stack holds any other number of languages at the end, if a token is larger than
$7$, or if an operator token finds too few languages on the stack.
