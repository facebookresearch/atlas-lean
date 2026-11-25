# Program of the raw-input SUBSET-SUM to PARTITION machine

The program of the raw-input machine, on its [stacks](k-2.md) and [labels](lab-2.md), with Boolean
internal state. At $\mathsf{copy1}$ it moves the bits of $\mathit{raw}$ onto $\mathit{buffer}$
one at a time, then goes to $\mathsf{copy2}$. At $\mathsf{copy2}$ it pops the bits of
$\mathit{buffer}$ one at a time, pushing each onto both $\mathit{raw}$ and the normalizer's input
stack, then goes to the normalizer's label $\mathsf{loop}$. At the copy of a normalizer label it
runs the [list normalizer](../../cook-levin/conversions-between-bit-string-encodings/a-finite-list-nat-canonicalizer/README.md)'s instruction on its copied stacks, except that the
normalizer's halting labels $\mathsf{good}$ and $\mathsf{bad}$ become $\mathsf{nonempty}$ and
$\mathsf{bad}$. At $\mathsf{nonempty}$ it goes to $\mathsf{compare}$ if the normalizer's output
stack is nonempty and to $\mathsf{bad}$ otherwise. At $\mathsf{compare}$ it compares
$\mathit{raw}$ with the normalizer's output bit by bit, moving equal bits onto $\mathit{left}$
and $\mathit{right}$; if both end together it goes to $\mathsf{restore}$, and on a difference to
$\mathsf{bad}$. At $\mathsf{restore}$ it moves the bits of $\mathit{left}$ onto the padding
machine's input stack $X$, then goes to $\mathsf{start}$, which sets the internal state to false
and goes to the padding machine's label $\mathsf{target}$. At the copy of a padding-machine label
it runs the [padding machine](prog-3.md)'s instruction on its copied stacks, its halting label
$\mathsf{done}$ becoming $\mathsf{done}$. At $\mathsf{bad}$ it pushes the canonical encoding of
the one-entry list $(1)$ onto the padding machine's output stack $O$ and goes to
$\mathsf{done}$, where it halts.
