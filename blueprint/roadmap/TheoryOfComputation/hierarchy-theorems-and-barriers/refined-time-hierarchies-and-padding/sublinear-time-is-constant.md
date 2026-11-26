# Sublinear deterministic time equals constant time

If a deterministic multi-tape machine reading its input sequentially halts within $t(n)=o(n)$ steps on every input of length $n$, then it halts within a constant number of steps on all inputs. Consequently, for $t=o(n)$, $\mathsf{DTIME}(t)=\mathsf{DTIME}(1)$ on binary words: every such language is determined by a bounded prefix of the input.

## Proof sketch

Pick $n_0$ with $t(n_0)< n_0$. On every input of length $\ge n_0$, the machine halts after reading at most $t(n_0)$ symbols when run on the length-$n_0$ prefix behaviour, since it cannot distinguish longer inputs with the same prefix before reading past position $t(n_0)$; a uniform bound $\max(t(0),\dots,t(n_0))$ follows.

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 3–5", 2007, Exercise 4.3.
