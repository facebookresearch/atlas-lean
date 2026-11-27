# Parameterized model checking of discrete timed networks with a controller is undecidable

For networks of arbitrarily many identical processes with discrete clocks plus one distinguished controller process, no algorithm decides whether
every infinite execution of a process satisfies a given LTL formula or Büchi automaton, although finite-execution specifications are decidable.

**Discrete timed networks.** A *timed-network template* is a finite labeled transition system with initial states, atomic propositions labeling its states and transitions labeled by rendezvous letters
$a_1, \dots, a_k$ for actions $a$, together with a finite set of clocks, a guard on each transition (a Boolean combination of predicates $x > c$ and $x = c$ with $c \in \mathbb{N}$) and a set of clocks reset by it. In the
network of $n$ copies, each process holds a state and a clock valuation in $\mathbb{N}$, all clocks starting at $0$. The network moves either by a *rendezvous* on an action $a$, in which $k$ distinct processes whose guards hold
simultaneously take transitions labeled $a_1, \dots, a_k$ and reset their clocks as specified, or by a *time step*, in which every clock of every process increases by $1$. With a *controller*, process $1$ runs a separate template
and the other processes run the common one.

**The problem.** An execution of a process is the sequence of labels of the states it visits along a run of the network, and the infinite executions are collected over all network sizes $n$. The *parameterized
model-checking problem* (PMCP) asks, given the templates and a specification of a set $W$ of infinite words over sets of atomic propositions, by a nondeterministic Büchi automaton or an LTL formula, whether every infinite
execution of a non-controller process, in networks of every size, belongs to $W$.

**Theorem.** The PMCP for discrete timed networks with a controller is undecidable for specifications of infinite executions given by nondeterministic Büchi automata or by LTL formulas. For specifications of finite
executions given by nondeterministic finite automata or LTL over finite traces it is decidable.

Without a controller the problem is decidable: with clock constants written in unary, it is PSPACE-complete for finite-execution specifications, and decidable in exponential time for infinite-execution specifications.

## Depends on

- [Formulas of linear temporal logic](../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)

## Proof depends on

None.

## Expansion

Discrete timed networks are polynomial-time inter-reducible with *RB-systems*, networks of identical finite processes that synchronize by $k$-wise rendezvous and by a symmetric broadcast that all processes take together, a time step
being a broadcast; the same holds with a controller on both sides. With a controller, RB-systems are in turn inter-reducible with systems using asymmetric broadcast, in which one process sends and all others receive, through a
specification transformation. For asymmetric-broadcast systems, model checking $\omega$-regular specifications is undecidable and regular specifications are decidable (Esparza, Finkel and Mayr), and both facts transfer.

## Sources

- B. Aminof, S. Rubin, F. Spegni and F. Zuleger, "Parameterized model-checking of discrete-timed networks and symmetric-broadcast systems", *Logical Methods in Computer Science* 21(2), article 27, 2025, doi:10.46298/lmcs-21(2:27)2025; read in arXiv:2310.02466v4: the theorem and corollary on RBC-systems and TNC-systems in Sections 2 and 3 with the reduction between controllers and asymmetric broadcast, the definitions of RB-systems, discrete timed networks and the PMCP, and the theorems on systems without a controller.
