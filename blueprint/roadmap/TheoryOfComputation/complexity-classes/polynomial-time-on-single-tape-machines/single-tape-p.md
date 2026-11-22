# Polynomial time on single-tape machines

The class of decision problems $L$ for which
there are a finite alphabet $\Sigma$ with a designated default element, an injective map $\iota$
from the bits to $\Sigma$, a single-tape Turing machine $M$ over $\Sigma$ and a polynomial $p$
with natural-number coefficients such that, for every bit list $w$, the machine $M$ started on the
word $\iota(w)$ (the bits of $w$ mapped by $\iota$) halts on the one-cell tape $\iota(L(w))$
within $p(|w|)$ steps.
