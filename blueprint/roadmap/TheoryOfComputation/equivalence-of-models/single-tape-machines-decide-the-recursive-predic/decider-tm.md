# The decider of a multi-stack machine

Let $M$ be a finite multi-stack machine whose stack
alphabets are all finite, with its input and output stack alphabets identified with the bits. The
decider of $M$ is the single-tape machine over the non-blank cells of the single-tape emulation of
$M$ that runs the recognizer of $M$ and, once the recognizer halts, runs the answer machine of $M$
on the resulting tape.
