# Hennie–Stearns: a universal multi-tape machine with O(t log t) overhead

There is a universal multi-tape Turing machine $U$ that, on input a machine description $d$ (with $k$ tapes), an input $x$ and a step count $t$ in binary, outputs the result of running $d$ on $x$ for $t$ steps, in time and space

$$
O\bigl(N+C_d\cdot(t+1)\log(t+1)\bigr),
$$

where $N$ is the input length and the factor $C_d$ depends only on the simulated machine, through its number $k$ of tapes, its alphabet size and its number of states (not on $x$ or $t$). The simulation keeps the simulated tapes in windows centred at the heads, organized in blocks of doubling sizes so that a head move costs amortized $O(\log t)$.

## Proof sketch

Hennie–Stearns block structure: each simulated tape is stored on one track in zones of sizes $2^{i}$ to both sides of the head, half full; a move shifts data between neighbouring zones, and a zone of size $2^{i}$ is reorganized only every $2^{i-1}$ steps at cost $O(2^{i})$, giving $O(\log t)$ amortized per step.

## Depends on

- [Correctness and running time of the clocked universal machine](../../turing-machines/universal-machines/clocked-universal-turing-machine/univ-run.md)
- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- F. C. Hennie and R. E. Stearns, "Two-Tape Simulation of Multitape Turing Machines", Journal of the ACM 13(4), 533–546, 1966.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
