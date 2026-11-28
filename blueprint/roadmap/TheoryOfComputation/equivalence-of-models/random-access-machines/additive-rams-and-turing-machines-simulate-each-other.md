# Cook and Reckhow: additive RAMs and multitape Turing machines simulate each other

Consider the random-access machine of Cook and Reckhow: a fixed program over registers $X_0, X_1, \ldots$ holding arbitrary integers, initially zero, with the instructions $X_i \leftarrow C$, $X_i \leftarrow X_j + X_k$, $X_i \leftarrow X_j - X_k$, $X_i \leftarrow X_{X_j}$, $X_{X_i} \leftarrow X_j$, "TRA $m$ if $X_j > 0$", READ $X_i$ and PRINT $X_i$ (no multiplication). Each instruction is charged through a cost function $l$ as in the source's Table I; for example $X_i \leftarrow X_j + X_k$ costs $l(X_j) + l(X_k)$ and $X_i \leftarrow C$ costs $1$. A string $w = \sigma_{i_1} \cdots \sigma_{i_n}$ over a finite alphabet is read as the integers $i_1, \ldots, i_n, 0$; the machine accepts by printing $1$ and halting and rejects by printing $2$ and halting, and its running time is the sum of the charges of the executed instructions. The program starts at its first instruction and halts if control reaches a line with no instruction or an indirect address is negative. The logarithmic cost function is $l(n) = \lceil \log_2 |n| \rceil$ for $|n| \ge 2$ and $l(n) = 1$ for $|n| < 2$. The base $2$ fixes a convention; changing to another fixed base changes only constants in the asymptotic bounds.

1. If a set $A$ is recognized by such a RAM within time $T(n)$, where $T(n) > n$ for all $n$, and $l$ is logarithmic, then some multitape Turing machine recognizes $A$ within time $T(n)^2$.
2. If $A$ is recognized by such a RAM within time $T(n)$, where $T(n) > n$ for all $n$, and $l$ is identically constant, then some multitape Turing machine recognizes $A$ within time $T(n)^3$.
3. Conversely, if some multitape Turing machine recognizes $A$ within time $T(n)$, where $T(n) \ge n$ for all $n$, then for every cost function $l$ that is positive, nondecreasing on the positive integers, symmetric ($l(n) = l(-n)$) and subadditive, some such RAM with cost function $l$ recognizes $A$ within time $O(T(n) \cdot l(T(n)))$.

Items 1 and 2 are exact bounds; their asymptotic forms $O(T(n)^2)$ and $O(T(n)^3)$ are what the simulation gives before linear speedup.

## Proof sketch

For (3), the RAM keeps each tape in two arrays, one per half, and a head reaches at most $T(n)$ cells, so each access costs $O(l(T(n)))$. For (1) and (2), the Turing machine keeps the registers written so far as a sorted list of binary address and content pairs. That list has $O(T(n))$ symbols under logarithmic cost, and $O(T(n)^2)$ under constant cost because register values at most double per instruction except for constant loads. Each RAM instruction is simulated by a fixed number of passes over the list, which gives $O(T(n)^2)$ or $O(T(n)^3)$ in total; linear speedup of Turing machines, applicable because $T(n)^2 > n$, removes the constant factor.

## Depends on

The source's RAM and multitape Turing-machine models, with their time measures, are statement prerequisites still to be supplied, as listed below. The repository's canonical time classes are not substituted for these models here.

## Proof depends on

The register-table bound and linear-speedup prerequisites are listed in the expansion below; canonical time-class lemmas do not by themselves supply them.

## Expansion

This page becomes ready once:

- The Cook and Reckhow RAM over integer registers with a cost function $l$, its input convention and its time measure (statement prerequisite; not yet stated)
- The source's multitape Turing machines recognizing sets of strings over a finite alphabet, with their time measure (statement prerequisite; not yet stated)
- The size bound on the sorted register table: $O(T(n))$ symbols under logarithmic cost, $O(T(n)^2)$ under constant cost (proof prerequisite; not yet stated)
- Linear speedup for multitape Turing machines, which turns the $O(T(n)^2)$ and $O(T(n)^3)$ simulations into the exact bounds of items 1 and 2 (proof prerequisite; not yet stated)
- Model scoping: the RAM of this page differs from the natural-number accumulator RAM of [Output of a RAM machine](ram-eval.md), which has natural-number registers with truncated subtraction, an accumulator, inputs placed in registers and a zero test. Relating the two machines, and either one's time to the canonical polynomial-time class, is a separate statement with its own source and is not claimed here. Likewise the Turing machines of items 1 to 3 are the source's multitape recognizers of sets of strings over a finite alphabet; identifying their time bounds with the bitstring classes of [deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md) is part of the same scoping (scoping obligation; not yet stated).

## Sources

- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 354–375, 1973: Section 1 and Table I, pp. 355 to 356 (the model, its input convention, the cost function $l$ and the standing assumptions on $l$ when it is not given explicitly), Section 4, Theorem 2, p. 361 (hypothesis $T(n) > n$ in part (a) and $T(n) \ge n$ in part (b)), and the lemma and linear-speedup step in its proof, pp. 362 to 363.
