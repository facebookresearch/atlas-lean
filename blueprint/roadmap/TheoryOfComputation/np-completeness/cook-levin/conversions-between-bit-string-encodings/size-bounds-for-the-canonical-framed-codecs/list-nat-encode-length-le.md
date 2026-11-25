# Framed length bound for lists of $m$-bit naturals

The canonical code of a list $(a_1, \ldots, a_k)$ of natural numbers is the concatenation of the framed forms
$1 c_1 \cdots 1 c_j 0$ of the binary codes $c$ of $a_1, \ldots, a_k$ (binary digits, least significant first, no
trailing zero, empty for $0$).

Let $m$ be a natural number and $(a_1, \ldots, a_k)$ a list of natural numbers each of which has at most $m$
binary digits. Then the canonical code of the list has length at most $k(2m + 1)$.
