# Run of the VERTEX-COVER to SUBSET-SUM machine

Let $x$ be a bit string. Start the
VERTEX-COVER to SUBSET-SUM machine at its start label with any state bit and with stacks in
which the input stack $\mathsf{X}$ holds the bit symbols of $x$, first bit on top, and every other
stack is empty. Then within at most $40(|x| + 1)^4$ steps the machine reaches the label
$\mathsf{done}$ with some state bit and stacks in which the output stack $\mathsf{O}$ holds,
top first, the image of $x$ under the bit-string reduction from VERTEX-COVER to SUBSET-SUM.
