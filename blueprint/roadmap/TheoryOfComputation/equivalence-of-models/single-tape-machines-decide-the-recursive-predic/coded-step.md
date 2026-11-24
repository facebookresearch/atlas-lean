# One step of a single-tape machine on coded configurations

Let $M$ be a single-tape Turing
machine with transition function $\delta$, and write $\bot$ both for the halting state and for the
blank. For a finite list $l$ of cells, let $\mathrm{hd}(l)$ be the first entry of $l$, the blank
$\bot$ when $l$ is empty; let $\mathrm{tl}(l)$ be $l$ without its first entry, the empty list when
$l$ is empty; and for a cell $w$ let $w \cdot l$, the push of $w$ onto $l$, be $l$ when $w = \bot$
and $l$ is empty, and $w$ prepended to $l$ otherwise. A coded configuration $(\bot, h, L, R)$ in
the halting state has no successor. For a running state $q$, write $\delta(q, h) = ((w, d), q')$,
where $w$ is the symbol to write, $d$ is either no move or a direction, and $q'$ is the new state,
possibly the halting state $\bot$. The successor of $(q, h, L, R)$ is $(q', w, L, R)$ if $d$ is no
move, $(q', \mathrm{hd}(L), \mathrm{tl}(L), w \cdot R)$ if $d$ is left, and
$(q', \mathrm{hd}(R), w \cdot L, \mathrm{tl}(R))$ if $d$ is right.
