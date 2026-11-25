# Constant offsets of the literals of a clause kind

Let $g$ be the number of symbol codes
of the clause kinds, and let $s, p, c \in \mathbb{N}$ and $q : \mathbb{N} \to \mathbb{N}$
(situation offset, push count, consumed count and pushed codes). The constant offset of literal
$l$ is: for an in-range shift clause $\mathrm{sh}(x)$, $cg + x$ if $l = 0$, $s$ if $l = 1$ and
$pg + x$ otherwise; for the overflow-fill clause $\mathrm{ov}$, $s$ if $l = 0$ and $pg$
otherwise; for a pushed-fill clause $\mathrm{pf}(j)$, $s$ if $l = 0$ and $jg + q(j)$
otherwise.
