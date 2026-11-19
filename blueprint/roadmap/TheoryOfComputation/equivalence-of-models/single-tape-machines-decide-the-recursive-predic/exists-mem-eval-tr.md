# The emulation's final tape

Let $M$ be a multi-stack machine with finitely many stacks,
labels and internal states and a finite input alphabet, let $L$ be a list of symbols of its input
stack, and suppose that $M$, started with $L$ on its input stack and every other stack empty,
halts at the configuration $c$. Then its plain single-tape emulation, started on the tape that
holds the symbols of $L$ bottom first on the input stack with the first cell flagged as the
bottom, halts at a configuration $c_0$ for which there is a list $L'$ of columns, each holding an
optional symbol for every stack and padded with blank columns, such that for every stack $k$ the
entries of $L'$ for $k$ are the symbols of stack $k$ of $c$ listed bottom first, followed by
blanks, and the tape of $c_0$ is blank to the left of the head and holds $L'$ from the head
rightwards, with the bottom-of-stack flag set on its first cell and cleared on all others.
