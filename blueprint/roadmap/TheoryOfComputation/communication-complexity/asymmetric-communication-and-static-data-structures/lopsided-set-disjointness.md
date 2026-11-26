# Lopsided set disjointness

For integers $N, B \ge 1$, *lopsided set disjointness* $\mathrm{LSD}_{N,B}$ is the function on $X \times Y$ where the universe $[N] \times [B]$ is split into $N$ blocks of size $B$, Alice holds a set $S$ containing exactly one element of every block (so $|X| = B^N$), Bob holds an arbitrary $T \subseteq [N] \times [B]$, and $\mathrm{LSD}(S, T) = 1$ iff $S \cap T = \emptyset$. Alice's input has $N \log_2 B$ bits and Bob's has $NB$ bits.

## Depends on

- [Asymmetric $[a, b]$-protocols](asymmetric-protocol.md)
- [Set intersection function](../randomized-communication-protocols/disj-fn.md)

## Sources

- Mihai Pătraşcu, "Unifying the Landscape of Cell-Probe Lower Bounds", SIAM Journal on Computing 40(3) (2011); FOCS (2008), arXiv:1010.3783.
- Peter Bro Miltersen, Noam Nisan, Shmuel Safra, Avi Wigderson, "On Data Structures and Asymmetric Communication Complexity", Journal of Computer and System Sciences 57(1) (1998).
