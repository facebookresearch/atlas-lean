# Driver stacks after tokenization

For a CNF formula $\varphi$ and a witness $w$, these
are the contents of the clause-check driver's stacks once the tokenizer has accepted $\varphi$:
the token stack holds the token list of $\varphi$ reversed, the table stack holds the
table-stack encoding of the occurrence table of $\varphi$ and $w$, and every other stack is
empty.
