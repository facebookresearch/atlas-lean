# Decoded list has at most one element per input bit

Let $\alpha$ be a type with a canonical bit-string encoding: an encoding map from $\alpha$ to bit strings and a
decoder that sends each bit string to an element of $\alpha$ or to failure and inverts the encoding. A list
$(a_1, \ldots, a_k)$ over $\alpha$ is encoded as the concatenation of the framed forms
$1 c_1 \cdots 1 c_m 0$ of the codes $c = c_1 \cdots c_m$ of $a_1, \ldots, a_k$; the list decoder splits its
input into framed blocks (failing unless the input is exactly such a concatenation) and decodes each block
(failing if one fails).

For every bit string $x$, if the list decoder returns a list $(a_1, \ldots, a_k)$ on $x$, then $k \le |x|$. No
assumption is made on the blocks beyond successful decoding: they need not be codes produced by the encoding.
