# Mixed-radix number

For a base $b$, a top digit $c$, a length $m$ and digits
$D : \mathbb{N} \to \mathbb{N}$, $\mathrm{mix}(b, c, 0, D) = c$ and
$\mathrm{mix}(b, c, m + 1, D) = D(0) + b \cdot \mathrm{mix}(b, c, m, n \mapsto D(n + 1))$; that
is, $D(0) + b\,(D(1) + b\,(\cdots + b\,(D(m - 1) + b\,c)))$, least significant digit first.
