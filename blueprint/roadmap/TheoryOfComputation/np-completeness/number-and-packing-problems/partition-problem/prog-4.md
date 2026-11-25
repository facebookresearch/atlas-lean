# Program of the raw-input PARTITION membership machine

The program of the raw-input membership machine, on its [stacks](k-4.md) and [labels](lab-4.md),
with Boolean internal state. At the copy of a normalizer label it runs the
[list normalizer](../../cook-levin/conversions-between-bit-string-encodings/a-finite-list-nat-canonicalizer/README.md)'s instruction on its copied stacks, except that the
normalizer's halting labels $\mathsf{good}$ and $\mathsf{bad}$ become $\mathsf{move1}$ and
$\mathsf{bad}$. At $\mathsf{move1}$ it moves the bits of the normalizer's output stack onto the
buffer one at a time, then goes to $\mathsf{move2}$; at $\mathsf{move2}$ it moves the bits of the
buffer onto the transducer's input stack $X$, then goes to $\mathsf{start}$, which sets the
internal state to false and goes to the transducer's label $\mathsf{copy}$. At the copy of a
transducer label it runs the [membership transducer](prog-5.md)'s instruction on its copied
stacks, its halting label $\mathsf{done}$ becoming $\mathsf{done}$. At $\mathsf{bad}$ it pushes
the encoding of the SUBSET-SUM instance with no numbers and target $1$ onto the doubling machine's
output stack $O$ and goes to $\mathsf{done}$, where it halts.
