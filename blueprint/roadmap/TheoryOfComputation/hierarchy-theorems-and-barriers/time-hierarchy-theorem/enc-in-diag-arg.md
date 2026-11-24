# The reformatting function in bits

For $f : \mathbb{N} \to \mathbb{N}$ and a bit list $x$,
the input bits of the clocked universal machine on its argument for the diagonal language of $f$
on $x$ are, when $x$ encodes a code, the cell of $f(|x|)$, then the cells of the input symbols of
$x$, then the bit false, then $x$ reversed; when $x$ encodes no code, they are the fixed list
$[\mathrm{false}, \mathrm{true}, \mathrm{true}, \mathrm{false}, \mathrm{false}]$.
