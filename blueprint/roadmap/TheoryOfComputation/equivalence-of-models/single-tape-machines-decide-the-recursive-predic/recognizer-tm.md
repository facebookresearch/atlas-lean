# The recognizer of a multi-stack machine

Let $M$ be a finite multi-stack machine all of
whose stack alphabets are finite, and let $e$ be an identification of the alphabet of its input
stack with the booleans. The recognizer of $M$ is the single-tape machine, over the non-blank
cells of the multi-stack-to-single-tape translation of $M$, that first runs the machine
prepending the bottom cell determined by $M$ and $e$ (the bottom-flagged cell holding
$e^{-1}(\mathrm{true})$ on the input stack and nothing on the other stacks) to its input and, when
that machine halts, runs the single-tape emulation of $M$.
