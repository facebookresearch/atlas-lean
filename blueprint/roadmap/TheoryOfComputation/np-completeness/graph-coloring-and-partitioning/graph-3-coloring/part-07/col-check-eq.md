# The 3-COLOR verifier as an edge loop

For all bit strings $x$ and $w$, the verifier accepts
$(x, w)$ iff reading a unary prefix $1^n 0$ off $x$ succeeds, giving $n$ and the rest $r$ of $x$,
and then $w$ has at least $2n$ bits, each of the witness colors $c_0, \dots, c_{n-1}$ of $w$ is
valid (not $11$), and the edge loop accepts $r$ with the vertex colors $c_0, \dots, c_{n-1}$.
