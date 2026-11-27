# The recognizer halts iff the multi-stack machine does

Let $M$ be a multi-stack machine
with finitely many stacks, labels and internal states and with finite stack alphabets, and let
$e$ be a bijection from the alphabet of its input stack to the bits. For every list of bits $w$,
the recognizer built from $M$ and $e$ halts on the word of input cells of the bits of $w$ if and
only if $M$ halts when started on the input stack obtained by applying $e^{-1}$ to each entry of
the reversal of $w$ followed by $\mathsf{true}$.
