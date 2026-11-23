# Decoding a pair of naturals fails exactly on a malformed first frame

A pair $(m, n)$ of natural numbers is coded as the framed form of the binary code of $m$ followed by the binary code
of $n$. For every bit string $x$, the decoder of pairs of natural numbers fails on $x$ exactly when no prefix of $x$
is the framed form $1 p_1 \cdots 1 p_k 0$ of a bit string $p$; if $x$ is the framed form of $p$ followed by $r$, it
returns $(D(p), D(r))$, where $D$ is the total decoder of natural numbers of [payload
normalization](../normalizing-the-total-binary-natural-number-deco/normalize-nat-eq-encode-decode.md).
