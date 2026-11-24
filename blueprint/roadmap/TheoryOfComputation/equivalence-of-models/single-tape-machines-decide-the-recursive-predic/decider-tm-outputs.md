# The decider outputs the answer bit

Let $M$ be a finite multi-stack machine whose stack
alphabets are all finite, with its input and output stack alphabets identified with the bits, and
let $w$ be a word of bits. Suppose that $M$, started with the input stack holding the reverse of
$w$ followed by $\mathrm{true}$, halts with the output stack holding a list $u$ of length at most
$1$, every other stack empty and its variable back at its initial value. Then there is a bit $b$
such that the decider of $M$, started on the input-bit cells of $w$, halts with the one-cell
output holding the input-bit cell for $b$, and $b = \mathrm{true}$ exactly when $u$ is nonempty
and its first symbol is the symbol for $\mathrm{true}$.
