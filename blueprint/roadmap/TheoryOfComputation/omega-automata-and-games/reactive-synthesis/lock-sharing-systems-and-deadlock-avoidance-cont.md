# Lock-sharing systems and deadlock avoidance control

A lock-sharing system is a parallel composition of processes that never communicate but acquire and release locks from a shared
pool; the deadlock avoidance control problem asks for local strategies, one per process, that never let the system deadlock.

**Processes.** A *process* $p$ is an automaton $\mathcal{A}_p = (S_p, \Sigma_p, T_p, \delta_p, \mathit{init}_p)$ with a set $T_p$ of locks
and a partial transition function $\delta_p : S_p \times \Sigma_p \to \mathit{Op}_{T_p} \times S_p$, where the operations are
$\mathit{Op}_{T_p} = \{\mathrm{acq}(t), \mathrm{rel}(t) : t \in T_p\} \cup \{\mathrm{nop}\}$. A *local configuration* is a pair $(s, B)$ of a
state and the set $B \subseteq T_p$ of locks the process owns, starting from $(\mathit{init}_p, \emptyset)$. A step
$(s, B) \xrightarrow{(a, op)} (s', B')$ requires $\delta_p(s, a) = (op, s')$ and: $B' = B$ if $op = \mathrm{nop}$; $t \notin B$ and
$B' = B \cup \{t\}$ if $op = \mathrm{acq}(t)$; $t \in B$ and $B' = B \setminus \{t\}$ if $op = \mathrm{rel}(t)$. Local runs are the
finite sequences of such steps from the initial configuration.

**Systems.** A *lock-sharing system* $\mathcal{S} = ((\mathcal{A}_p)_{p \in P}, \Sigma^s, \Sigma^e, T)$ consists of processes with pairwise
disjoint states and actions, a partition of all actions into *controllable* actions $\Sigma^s$ and *uncontrollable* actions
$\Sigma^e$ (the environment's), and the set $T = \bigcup_p T_p$ of locks, which processes may share. A global configuration is a tuple
of local configurations whose lock sets are pairwise disjoint, so each lock is held by at most one process; a global step is a
step of one process, and a global run is a sequence of global steps from the initial configuration.

**Strategies.** A *local strategy* for $p$ maps each local run $u$ of $p$ to a set $\sigma_p(u)$ of actions possible after $u$ that
contains every possible uncontrollable action. A *control strategy* is a tuple $\sigma = (\sigma_p)_{p \in P}$, so each process decides
only from its own local run. A global run *respects* $\sigma$ if every action of each process was allowed by its strategy at that
point. A $\sigma$-run *leads to a deadlock* if it cannot be prolonged to a longer $\sigma$-run, and $\sigma$ is *winning* if no
$\sigma$-run leads to a deadlock. The *deadlock avoidance control problem* asks whether a given system has a winning control
strategy; an instance is a system with finitely many processes, each with finite sets $S_p$, $\Sigma_p$ and $T_p$, given by the tables of the $\delta_p$ and the partition of the actions. A process that tries to acquire a lock it owns, or to release one it does not own, blocks.

The dining philosophers form such a system: forks are locks, becoming hungry is uncontrollable, and the order in which a
philosopher takes the two forks is controllable.

## Depends on

- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Sources

- H. Gimbert, C. Mascle, A. Muscholl and I. Walukiewicz, "Distributed controller synthesis for deadlock avoidance", *Logical Methods in Computer Science* 21(3), paper 24, 2025, doi:10.46298/lmcs-21(3:24)2025; the Preliminaries section of the version arXiv:2204.12409v6 (processes, local configurations and runs, lock-sharing systems, local and control strategies, the dining philosophers example, and the definition of the deadlock avoidance control problem).
