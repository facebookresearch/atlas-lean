# Sublinear deterministic time equals constant time

If a deterministic multi-tape machine, whose input head starts on the first input symbol and moves at most one cell per step and which is not given the input length separately, halts within $t(n)=o(n)$ steps on every input of length $n$, then it halts within a constant number of steps on all inputs. Consequently, for $t=o(n)$, $\mathsf{DTIME}(t)=\mathsf{DTIME}(1)$ on binary words: every such language is determined by a bounded prefix of the input.

## Proof sketch

Pick $n_1$ with $t(n)+1<n$ for all $n\ge n_1$, and let $T=\max\{t(n): n<n_1\}$. Let $w$ be an input on which the machine runs for $\tau$ steps; its input head visits only positions $1,\dots,\tau+1$. If $|w|<n_1$ then $\tau\le T$. Otherwise $\tau\le t(|w|)<|w|-1$, so the prefix $u$ of $w$ of length $\tau+1$ is proper and the run on $u$ is identical, taking $\tau=|u|-1$ steps; $|u|\ge n_1$ would give $\tau\le t(|u|)<|u|-1$, so $|u|<n_1$ and again $\tau\le T$. This is the argument of Goldreich's Exercise 4.3 (the set of inputs that are read entirely is finite).

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective, Chapters 3–5", 2007, Exercise 4.3 (published by Cambridge University Press, 2008).
