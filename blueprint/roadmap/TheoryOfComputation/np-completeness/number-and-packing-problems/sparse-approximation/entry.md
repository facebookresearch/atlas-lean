# Matrix entry in SPARSE APPROXIMATION

For an instance of SPARSE APPROXIMATION and natural numbers $r$ and $c$, the entry $A_{rc}$ is the value of the rational code at position $c$ of the stored row at position $r$ of $A$, both positions counted from $0$: the code $((p, q), d)$ gives $(p - q)/d$ when $d > 0$. A row position beyond the stored rows reads as an empty row, and a position beyond the end of its row reads as the code $((0, 0), 1)$, so either gives $0$; a code that is present but has denominator $d = 0$ also gives $0$.
