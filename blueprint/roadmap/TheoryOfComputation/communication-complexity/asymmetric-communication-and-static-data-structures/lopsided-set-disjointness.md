# Lopsided set disjointness

For integers $N, B \ge 1$, *lopsided set disjointness* $\mathrm{LSD}_{N,B}$ (Pătraşcu, Section 1.2) gives Alice a set $S$ of exactly $N$ elements of the universe $[N] \times [B]$, Bob an arbitrary $T \subseteq [N] \times [B]$, and has value $1$ iff $S \cap T = \emptyset$; Alice has $\binom{NB}{N}$ possible inputs. Its restriction *blocked* $\mathrm{LSD}_{N,B}$ (Pătraşcu, Section 3) splits the universe into the $N$ blocks $\{i\} \times [B]$ and promises that $S$ contains exactly one element of every block, so Alice has $B^N$ possible inputs ($N \log_2 B$ bits) while Bob still has $2^{NB}$ ($NB$ bits). General $\mathrm{LSD}_{N,B}$ reduces to blocked $\mathrm{LSD}$ with $O(N)$ additional communication (Pătraşcu, Lemma 9).

## Sources

- Mihai Pătraşcu, "Unifying the Landscape of Cell-Probe Lower Bounds", SIAM Journal on Computing 40(3) (2011); FOCS (2008), arXiv:1010.3783.
- Peter Bro Miltersen, Noam Nisan, Shmuel Safra, Avi Wigderson, "On Data Structures and Asymmetric Communication Complexity", Journal of Computer and System Sciences 57(1) (1998).
