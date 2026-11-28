# Well-formed instances of EQUATION SATISFIABILITY OVER A FINITE GROUP

For a group of $n$ elements, an instance is a list of tokens $(\mathit{tag}, \mathit{index})$, and it is well-formed when every tag is $0$ (a constant), $1$ (a variable) or $2$ (an inverted variable), and every constant token $(0, c)$ has $c < n$. Evaluation also gives values to other tokens: an out-of-range constant evaluates to the identity, and a tag of $3$ or more evaluates as an inverted variable; such tokens are rejected by well-formedness.
