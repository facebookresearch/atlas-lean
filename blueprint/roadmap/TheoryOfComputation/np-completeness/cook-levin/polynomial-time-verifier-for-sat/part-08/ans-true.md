# Answer of the SAT host with the three-literal filter

For all bit strings $x$ and $w$,
the answer of the SAT host with flag true on $(x, w)$ is the conjunction of two bits. The first
is false if the complete length-prefixed CNF decoder fails on $x$; if $x$ decodes to a CNF
formula $\varphi$, it is true exactly when every clause of $\varphi$ has at most three literals.
The second is the return value of the SAT verifier on $(x, w)$.
