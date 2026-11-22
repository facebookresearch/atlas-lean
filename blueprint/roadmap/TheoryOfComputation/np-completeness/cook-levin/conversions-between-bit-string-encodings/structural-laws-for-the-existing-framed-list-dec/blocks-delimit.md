# Parsing a framed head leaves the raw remainder

The framed form of a bit string $p = p_1 \cdots p_m$ is $1 p_1 \cdots 1 p_m 0$. The block parser splits a bit
string into consecutive framed blocks, returning the list of their payloads, and fails unless the whole input is a
concatenation of framed forms.

For all bit strings $p$ and $r$, the block parser on the framed form of $p$ followed by $r$ fails exactly when it
fails on $r$; otherwise it returns $p$ followed by the payloads it returns on $r$.
