# The cells of the view

Let $t$ be a two-way tape over $\Gamma$ with head cell $h$, left
stack tape $(\ell_0, \dots, \ell_{p-1})$ and right stack tape $(r_0, \dots, r_{q-1})$. For every
integer $i$, the cell at position $i$ of the view of $t$ as a tape of cells is $h$ if $i = 0$,
$r_{i-1}$ if $0 < i \le q$, $\ell_{-i-1}$ if $-p \le i < 0$, and the blank otherwise.
