# Sublinear deterministic time equals constant time

Let $M$ be a deterministic multi-tape Turing machine with a read-only input tape, and say that $M$ runs in time $T(n)$ if it makes at most $T(n)$ steps on every input of length $n$. If $M$ runs in time $T(n)$ and $T(n_0)<n_0+1$ for some $n_0$, then $M$ runs in constant time: it never reads the $(n_0+1)$-st input symbol, so it makes at most $T(n_0)$ steps on every input of length at least $n_0$. In particular every such machine running in time $t(n)=o(n)$ runs in constant time, so $\mathsf{DTIME}(t)=\mathsf{DTIME}(1)$ for $t=o(n)$: every such language is determined by a bounded prefix of the input.

## Proof sketch

Let $T_w$ be the maximum number of steps on inputs of length $n_0$, attained at $w$. Since $T_w\le T(n_0)<n_0+1$, the input head (which starts on the first input symbol and moves at most one cell per step) never reaches position $n_0+1$, so every input with prefix $u$ of length $n_0$ is processed exactly as $u$ is, in at most $T_w$ steps; inputs shorter than $n_0$ are finitely many. For $t=o(n)$, any $n_0$ with $t(n_0)<n_0+1$ works.

## Depends on

- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- David Gajser, "Verifying Time Complexity of Deterministic Turing Machines", arXiv:1307.3648v2, 2014 (published in Theoretical Computer Science 600, 86–97, 2015), Section 2 (model and "runs in time"), Lemma 3.1 and its proof, and the proof of Theorem 3.4 ("a Turing machine that runs in time $T(n)$ such that $T(n_0)<n_0+1$ for some $n_0\in\mathbb{N}$, runs in constant time").
- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 4.3 (supplementary).
