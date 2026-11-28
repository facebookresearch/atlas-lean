# Deadlock avoidance control for lock-sharing systems is undecidable

No algorithm decides whether a given lock-sharing system has local strategies, one per process, under which it never deadlocks,
even when the numbers of processes and locks are fixed.

**Theorem.** The deadlock avoidance control problem for arbitrary
[lock-sharing systems](lock-sharing-systems-and-deadlock-avoidance-cont.md) is undecidable, even when the number of locks and the
number of processes are fixed (Theorem 2.5 of the source).

The undecidability comes from the purely local information of the strategies: processes communicate only through the locks they
take. The problem becomes decidable when every process uses at most two locks, and when locks are used in a nested fashion
(acquired and released in stack order). The source's direct proof first
allows locks to be held initially, with at most seven locks per process, and then removes the initial locks by adding one process and
$n + 1$ locks for a system of $n$ processes; it reports a more involved proof with four locks per process, and leaves three
locks per process open.

## Depends on

- [Lock-sharing systems and deadlock avoidance control](lock-sharing-systems-and-deadlock-avoidance-cont.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The infinite Post correspondence problem is undecidable for instances of size 9](../../undecidable-problems/post-correspondence-problem/the-infinite-post-correspondence-problem-is-unde.md)

## Expansion

The proof first shows undecidability when processes may hold locks in the initial configuration, then removes initial locks by a
reduction. It reduces the question whether an instance $(\alpha_i, \beta_i)_{i=1}^m$ of the Post correspondence problem over $\{0, 1\}$
has an infinite solution. Two processes $P$ and $\bar P$ each send a sequence of bits to a third process $C$, using only seven locks:
$P$ transmits a bit $b$ by the pattern $\mathrm{acq}(s_b)\,\mathrm{rel}(p)\,\mathrm{acq}(c)\,\mathrm{rel}(s_b)\,\mathrm{acq}(p)\,\mathrm{rel}(c)$,
and symmetrically for $\bar P$. The environment tells $C$ either to check that the two bit sequences are equal or to guess indices
$i_1, i_2, \dots$ and check that the sequences are $\alpha_{i_1} \alpha_{i_2} \cdots$ and $\beta_{i_1} \beta_{i_2} \cdots$; any detected
mismatch leads to a deadlock. Since $P$ and $\bar P$ do not know which check is made, they can avoid deadlocks forever exactly when they
send an infinite solution.

## Sources

- H. Gimbert, C. Mascle, A. Muscholl and I. Walukiewicz, "Distributed controller synthesis for deadlock avoidance", *Logical Methods in Computer Science* 21(3), paper 24, 2025, doi:10.46298/lmcs-21(3:24)2025; version arXiv:2204.12409v6: Theorem 2.5, and its proof in Section 5, "Undecidability in the general case" (Theorem 5.1, for systems with an initial configuration and at most seven locks per process, and Lemma 5.4, removing initial locks); the decidable cases are Sections 3 and 4.
