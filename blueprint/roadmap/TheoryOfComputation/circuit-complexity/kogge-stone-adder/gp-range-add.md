# Adjacent blocks compose

Fix bit vectors $x, y$ of the same width, write
$\mathrm{GP}(\ell, m)$ for the generate–propagate pair of the block of the $m$ bits
$\ell, \dots, \ell + m - 1$, and write $h \circ l$ for the block operator with $h$ placed above
$l$. Then for all natural numbers $\ell, a, b$,
$\mathrm{GP}(\ell, a + b) = \mathrm{GP}(\ell + a, b) \circ \mathrm{GP}(\ell, a)$.
