# Decoded pair exposes its raw component payloads

Let $\alpha$ and $\beta$ be types with canonical bit-string encodings (see [decoded list
length](decoded-list-length-le.md)). The code of a pair $(a, b)$ is the framed form of the code of $a$ followed by
the code of $b$; the pair decoder reads one framed block $p$ from the front of its input, leaving a remainder
$r$, and decodes $p$ as an element of $\alpha$ and $r$ as an element of $\beta$.

For every bit string $x$, if the pair decoder returns $(a, b)$ on $x$, then there are bit strings $p$ and $r$ such
that $x$ is the framed form of $p$ followed by $r$, the decoder of $\alpha$ returns $a$ on $p$ and the decoder of
$\beta$ returns $b$ on $r$. Here $p$ and $r$ need not be codes produced by the encodings.
