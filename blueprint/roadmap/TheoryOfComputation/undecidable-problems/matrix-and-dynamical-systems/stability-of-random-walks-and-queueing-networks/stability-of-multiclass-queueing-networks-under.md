# Stability of multiclass queueing networks under static buffer priority policies is undecidable

No algorithm decides whether a deterministic multiclass queueing network, run under a nonpreemptive static buffer priority policy from a given initial state, keeps its total number of jobs bounded.

A *multiclass queueing network* has single-server nodes $S_1,\dots,S_J$ and job classes $1,\dots,N$, each class $i$ with its own buffer at one node of capacity $B_i\in\{0,1,\dots\}\cup\{\infty\}$, deterministic rational interarrival times $a_i$ (possibly $\infty$, no external arrivals) and initial delays $b_i$, and a deterministic rational service time $m_i\ge0$. After service in class $i$ a job moves to class $l$ if $R_{i,l}=1$ for a fixed zero–one substochastic routing matrix $R$ of spectral radius less than $1$, is dropped if that buffer is full, and leaves if row $i$ of $R$ is zero. A *nonpreemptive static buffer priority policy* fixes, for each node, a permutation $\theta_j$ of its classes; whenever the server completes a service it starts the head-of-line job of the nonempty class of highest priority, never interrupting service and never idling while a job waits. With initial queue lengths $Q(0)$, the triple $(Q,\theta,Q(0))$ is *stable* if $\sup_{s\ge0}\sum_iQ_i(s)<\infty$.

**Theorem (Gamarnik–Katz).** No algorithm decides, for an arbitrary multiclass queueing network $Q$, nonpreemptive static buffer priority policy $\theta$ and vector of initial queue lengths $Q(0)$, whether $(Q,\theta,Q(0))$ is stable (Theorem 1).

The networks used have buffers of size $0$ or $\infty$ and possibly zero service times, and satisfy the load condition at every server; the source conjectures that the result also holds for networks with only infinite buffers and nonzero service times. An earlier result of Gamarnik covered generalized priority policies, which depend on the set of nonempty buffers.

## Depends on

- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from stability of counter machines, i.e. whether both counters stay bounded from a given configuration $(s^*,0,0)$, which is undecidable by a reduction from the halting problem of two-counter machines; one first passes to *simplified* counter machines, whose counter updates depend only on the new state (Proposition 1). Each counter is modeled by a Rybko–Stolyar subnetwork whose workload carries the counter's value, and further subnetworks implement the control states, the zero tests and the increments and decrements, so that the network is stable iff the simplified machine is stable (Theorem 3). A good expansion links the undecidability of stability of counter machines, by its reduction from the halting problem of two-counter machines.

## Sources

- David Gamarnik and Dmitriy Katz, "On deciding stability of multiclass queueing networks under buffer priority scheduling policies", *The Annals of Applied Probability* 19(5), 2009, pp. 2008–2037, doi:[10.1214/09-AAP597](https://doi.org/10.1214/09-AAP597); read in arXiv:0708.1034v2 ([arXiv](https://arxiv.org/abs/0708.1034v2)), the reprint of the published article, whose numbering is used here: abstract, Section 2 (the model, Definition 1 and Theorem 1), Section 3 (counter machines, Theorem 2, Definition 2, Proposition 1 and Corollary 1) and Section 5 (Theorem 3).
