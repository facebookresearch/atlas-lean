# An exact linear-time step counter from binary input

There is a fixed deterministic multi-tape Turing machine which, on input the binary representation of $n\in\mathbb{N}$, enters a designated signal state exactly $n$ times and halts within $c(n+1)$ steps for a constant $c$; on input $0$ it never signals. This makes $n\mapsto n$ 'time-constructible from binary' with exact counts.

## Proof sketch

Convert binary to unary by repeated halving, writing $n$ marks in $O(n)$ total time (the amortized cost of binary decrement is $O(1)$), then sweep the marks, entering the signal state once per mark.

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 3–5", 2007, Exercise 4.5.
