# An exact linear-time step counter from binary input

There is a fixed deterministic multi-tape Turing machine which, on input the binary representation of $n\in\mathbb{N}$, enters a designated signal state exactly $n$ times and halts within $c(n+1)$ steps for a constant $c$; on input $0$ it never signals. This makes $n\mapsto n$ 'time-constructible from binary' with exact counts.

## Proof sketch

Copy the input to a work tape and repeatedly decrement it in binary until it reaches $0$, entering the signal state once per decrement. A decrement flips the trailing $0$s and the lowest $1$, so the head travels only over the flipped bits and back; as for binary increment, the total number of flips over $n$ decrements is at most $2n$, so the run takes $O(n)$ steps after the $O(\log(n+1))$ copying phase (Goldreich's amortized step-counter).

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 3–5", 2007, Exercise 4.5 (published by Cambridge University Press, 2008).
