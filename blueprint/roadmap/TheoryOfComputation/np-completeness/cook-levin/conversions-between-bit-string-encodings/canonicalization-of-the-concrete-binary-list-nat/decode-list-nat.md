# Decoding a list of naturals is block parsing then number decoding

A list of natural numbers is coded as the concatenation of the framed forms $1 c_1 \cdots 1 c_j 0$ of the binary
codes $c$ of its entries. For every bit string $x$, the decoder of lists of natural numbers fails on $x$ exactly
when $x$ is not a concatenation of framed forms; if $x$ is the concatenation of the framed forms of
$p^1, \ldots, p^k$, it returns $(D(p^1), \ldots, D(p^k))$, where $D$ is the total decoder of natural numbers of
[payload normalization](../normalizing-the-total-binary-natural-number-deco/normalize-nat-eq-encode-decode.md).
