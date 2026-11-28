# A set is in P iff its polynomial-time instance complexity is bounded

A set $A$ is polynomial-time computable exactly when, for some polynomial time bound, the instance complexity of every input is bounded by one constant (Orponen, Ko, Schöning and Watanabe). Several natural kinds of sets outside P have instances whose instance complexity matches their time-bounded Kolmogorov complexity.

**Characterization.** For every set $A$: $A\in\mathrm{P}$ if and only if there are a polynomial $p$ and a constant $c$ such that $\mathrm{ic}^p(x:A)\le c$ for all $x$.

**Hard instances.** A set $A$ has *p-hard instances* if for every polynomial $p$ there are a polynomial $q$ and a constant $c$ such that for infinitely many $x$, $\mathrm{ic}^q(x:A)\ge C^p(x)-c$. A recursive set $A\notin\mathrm{P}$ has p-hard instances if at least one of the following holds: $A$ is a tally set; $A$ is E-complete; $A$ is NP-hard under honest Turing reductions; $A$ is P-bi-immune (Orponen et al.; Fortnow and Kummer). Fortnow and Kummer also give relativized sets outside P without such hard instances, even when the instance complexity is only required to reach the CD complexity.

## Expansion

If $A\in\mathrm{P}$, one fixed decider is a consistent program that answers on every input. Conversely, if every instance has a consistent program of length at most $c$ running in time $p$, there are finitely many such programs; on input $x$ run all of them for $p(|x|)$ steps. Each is consistent with $A$, so any non-$\bot$ answer is correct, and at least one program answers on $x$; with the finite program list built in, this decides $A$ in polynomial time. Since $\mathrm{ic}\le\mathrm{CD}+O(1)$ and $\mathrm{CD}\le C+O(1)$, hard instances occur only where CD and C complexity nearly agree.

## Depends on

- [Time-bounded instance complexity](time-bounded-instance-complexity.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

None.

## Sources

- Lance Fortnow, "Kolmogorov Complexity and Computational Complexity", in *Complexity of Computations and Proofs* (J. Krajíček, ed.), Quaderni di Matematica 13, 2004, [author copy](https://lance.fortnow.com/papers/files/quaderni.pdf) (Theorem 3.6, Definition 3.7, Theorem 3.8).
