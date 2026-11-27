# Hennie–Stearns: a universal multi-tape machine with O(t log t) overhead

There is a multi-tape Turing machine $U$ such that for every input $x$ and every description $\alpha$ of a multi-tape machine $M_\alpha$, $U(x, \alpha) = M_\alpha(x)$; furthermore, if $M_\alpha$ halts on input $x$ within $T$ steps, then $U(x, \alpha)$ halts within $C\,T \log T$ steps, where $C$ is independent of $|x|$ and depends only on the alphabet size, the number of tapes and the number of states of $M_\alpha$.

## Proof sketch

Hennie–Stearns block structure: each simulated tape is stored on one track in zones of sizes $2^{i}$ to both sides of the head, half full; a move shifts data between neighbouring zones, and a zone of size $2^{i}$ is reorganized only every $2^{i-1}$ steps at cost $O(2^{i})$, giving $O(\log T)$ amortized per step. (Derived.) Adding a binary step counter gives a clocked variant that, on input $d$, $x$ and a step count $t$ in binary, outputs the result of running $d$ on $x$ for $t$ steps in time $O(N + C\,(t+1)\log(t+1))$ with $C$ as above for the machine $d$, where $N$ is the input length.

## Depends on

- [Codes for multi-tape machines](../../turing-machines/universal-machines/codes-for-multi-tape-turing-machines/code.md)
- [Deterministic time classes on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [Correctness and running time of the clocked universal machine](../../turing-machines/universal-machines/clocked-universal-turing-machine/univ-run.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", web draft dated 2007-01-08, Theorem 1.13 (Efficient Universal Turing machine) and Appendix 1.A (published by Cambridge University Press, 2009, as Theorem 1.9).
- F. C. Hennie and R. E. Stearns, "Two-Tape Simulation of Multitape Turing Machines", Journal of the ACM 13(4), 533–546, 1966.
