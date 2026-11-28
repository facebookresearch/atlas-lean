# Verifying a time bound for multi-tape machines is undecidable exactly when T(n) ≥ n+1

For a function $T$, whether a given multi-tape Turing machine runs in time $T(n)$ is undecidable if $T(n) \ge n + 1$ for
every $n$, and decidable otherwise.

**Theorem.** Let $T : \mathbb{N} \to \mathbb{R}_{\ge 0}$. The problem $\mathrm{HALT}_{T(n)}$ of
[deciding whether a multi-tape Turing machine runs in time T(n)](turing-machines-running-within-a-time-bound.md) is
undecidable if and only if $T(n) \ge n + 1$ for all $n \in \mathbb{N}$.

For example, verifying the time bounds $n + 1$, $n^2 + 1$ or $2^n$ is undecidable, while the bounds $n^3$ (which is $0$ at
$n = 0$) and the constant $5$ can be verified. The input of the problem is the machine; $T$ is fixed.

## Depends on

- [Turing machines running within a time bound](turing-machines-running-within-a-time-bound.md)
- [Time-bounded multi-tape machine](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/time-bounded-by.md)
- [Decidability by multi-stack machines](../decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

If $T(n_0) < n_0 + 1$ for some $n_0$, check the running time on all inputs of length at most $n_0$; if it is within $T$,
the machine never reads beyond position $n_0$, its running time on longer inputs is the maximum $T_w$ reached at length
$n_0$, and it remains to compare the finitely many possible values of $T_w$ with $T(n)$ for $n > n_0$.

If $T(n) \ge n + 1$ for all $n$, reduce the complement of halting of one-tape machines on the empty input: from a one-tape
machine $H$ build a multi-tape machine $\tilde{H}$ that, on input $w$, uses the input tape only to count $|w| + 1$ steps while
simulating that many steps of $H$ on the empty input, halts after exactly $|w| + 1$ steps if $H$ has not halted, and loops
forever otherwise. Then $\tilde{H}$ runs in time $T(n)$ iff it runs in time $n + 1$ iff $H$ never halts on the empty input.

## Sources

- D. Gajser, "Verifying time complexity of Turing machines", *Theoretical Computer Science* 600:86–97, 2015, doi:[10.1016/j.tcs.2015.07.028](https://doi.org/10.1016/j.tcs.2015.07.028). Numbering of the version read, arXiv:1307.3648v2 (titled "Verifying Time Complexity of Deterministic Turing Machines"): Theorem 3.3, with Lemma 3.1 (the decidable case), Lemma 3.2 (the reduction) and Lemma 2.5 (halting of one-tape machines on the empty input).
