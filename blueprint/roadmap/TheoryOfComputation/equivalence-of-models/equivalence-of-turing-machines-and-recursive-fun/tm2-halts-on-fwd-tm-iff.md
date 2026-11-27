# The wrapped machine of a code halts exactly where the code is defined

Let $c$ be a code
for a partial recursive function on lists of natural numbers and $n \in \mathbb{N}$, and suppose
that every value of $c$ on the one-element list $[n]$ is itself a one-element list. Then the
wrapped multi-stack machine of $c$ halts on the binary digits of $n$ (least significant first,
with $1$ read as true, $0$ as false and no leading zeros, so that $0$ gives the empty word) if
and only if the evaluation of $c$ at $[n]$ is defined.
