# Stack alphabets of the wrapped machine

Let $\mathrm{tr}$ be Mathlib's multi-stack machine
that evaluates partial recursive codes, with stacks
$K' = \{\mathrm{main}, \mathrm{rev}, \mathrm{aux}, \mathrm{stack}\}$ and alphabet
$\Gamma' = \{\mathtt{cons}_l, \mathtt{cons}, \mathtt{bit0}, \mathtt{bit1}\}$. The stacks of the
wrapped machine are indexed by $K' \sqcup \{\mathrm{false}, \mathrm{true}\}$: each stack in $K'$
has alphabet $\Gamma'$, and the two stacks $\mathrm{false}$ and $\mathrm{true}$ (the input and
output stacks of the wrapped machine) have the alphabet $\{\mathrm{false}, \mathrm{true}\}$ of
bits.
