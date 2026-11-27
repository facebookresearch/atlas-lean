# Slowdown lemma: NTIME(n) ⊆ DTIME(t′) removes a quantifier

If $\mathsf{NTIME}(n)\subseteq\mathsf{DTIME}(t')$, then for every time-constructible $t$, $\Sigma_2\mathsf{TIME}(t)\subseteq\mathsf{NTIME}(\tau)$ whenever $n+t(n)+t'(O(n+t(n)))=O(\tau(n))$. In polynomial form: if $t'(m)^q=O((m+1)^p)$ with $q>0$, then $\Sigma_2\mathsf{TIME}(n^a)\subseteq\mathsf{NTIME}(n^b)$ whenever $1\le a\le b$ and $ap\le bq$.

## Proof sketch

The universal block, the set of strings $\langle x,u\rangle$ for which some $v$ falsifies the verifier, is in nondeterministic linear time of its own (already padded) length, hence in $\mathsf{DTIME}(t')$ by hypothesis; a nondeterministic machine guesses $u$ and runs that deterministic algorithm.

## Depends on

- [Simultaneous time–space classes TISP and Σ₂TIME](tisp-and-sigma2-time.md)
- [Nondeterministic time classes](../../../time-and-space-complexity-classes/ntime.md)
- [Deterministic time classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Lance Fortnow, "Time-Space Tradeoffs for Satisfiability", Journal of Computer and System Sciences 60(2), 2000.
- Lance Fortnow, Richard J. Lipton, Dieter van Melkebeek and Anastasios Viglas, "Time-Space Lower Bounds for Satisfiability", Journal of the ACM 52(6), 2005.
