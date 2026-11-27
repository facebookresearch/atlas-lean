# Decisiveness of probabilistic counter machines is undecidable

No algorithm decides whether the Markov chain of a probabilistic counter machine is decisive, even when all weights are constant, or
when the machine has a single state and a single counter with counter-dependent weights.

**Theorem (Finkel, Haddad and Ye).** For [probabilistic counter machines](probabilistic-counter-machines-and-decisiveness.md):

1. decisiveness with respect to a finite target set is undecidable for static pCMs;
2. the decisiveness problem is undecidable for safe one-counter pCMs, even with a single control state.

In the second case the weights depend on the counter value; for polynomial safe one-counter pCMs, decisiveness with respect to a finite set is
decidable. The source also shows that decisiveness of probabilistic Petri nets with polynomial weights is undecidable when the target set is finite
or upward closed, whereas for constant weights Petri nets are decisive with respect to upward-closed sets.

## Depends on

- [Probabilistic counter machines and decisiveness](probabilistic-counter-machines-and-decisiveness.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Davis–Putnam–Robinson–Matiyasevich theorem](../../diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For static pCMs, the proof reduces the halting problem of normalized counter machines, which do not halt from any initial counter values when they do not halt from zero (a lemma of the source). Each non-halting instruction becomes a choice between itself, with weight $1/3$, and incrementing the first counter and restarting, with weight $2/3$. If the machine does not halt, the halting configuration is unreachable and the chain is decisive. If it halts, the halting configuration stays reachable from every reachable configuration, while the restarting first counter behaves like a random walk drifting upward, so the target is missed with positive probability and the chain is not decisive. For safe one-counter pCMs with one
state, it reduces Hilbert's tenth problem: given an integer polynomial $P$, the decrement has weight $1$ and the increment has weight
$\min\{P(n_1, \dots, n_k)^2 + 1 : n_1 + \cdots + n_k \le n\}$ at counter value $n$, so that the counter returns to its initial value almost surely, and the chain is decisive, exactly when $P$ has a root in $\mathbb{N}^k$;
otherwise the increment weight is at least twice the decrement weight everywhere and the counter escapes with positive probability.

## Sources

- A. Finkel, S. Haddad and L. Ye, "About decisiveness of dynamic probabilistic models", in *34th International Conference on Concurrency Theory (CONCUR 2023)*, LIPIcs 279, paper 14, 2023, doi:10.4230/LIPIcs.CONCUR.2023.14; read in arXiv:2305.19564v1: the theorem on static pCMs in the section "Probabilistic counter machines", the theorem on single-state safe one-counter pCMs in the section "Probabilistic safe one-counter machines" with its proof and the decidability theorem for polynomial ones after it, and the theorems of the section "Probabilistic Petri nets".
