# The answer machine

Let $M$ be a finite multi-stack machine whose stack alphabets are all
finite, with its input and output stack alphabets identified with the bits. The answer machine of
$M$ is the single-tape machine over the non-blank cells of the single-tape emulation of $M$ with a
single state that, in one step, replaces the symbol under the head by the input-bit cell for the
answer read from that cell (the answer $\mathrm{false}$ if the cell is blank), does not move, and
halts.
