# Parametric timed automata

A parametric timed automaton is a timed automaton in which unknown constants, the parameters, may replace integer
constants in guards and invariants. Each parameter valuation turns it into an ordinary timed automaton.

**Constraints.** Fix finite sets $X$ of *clocks* (real-valued variables that grow at the same rate) and $P$ of
*parameters*. A *parameter valuation* is a map $v : P \to \mathbb{Q}_{\ge 0}$; it is *integer* if all its values are in
$\mathbb{N}$. A clock valuation is a map $\mu : X \to \mathbb{R}_{\ge 0}$. A *parametric guard* is a conjunction of
inequalities $x \bowtie \sum_{p \in P} \beta_p\, p + d$ with $x \in X$, $\beta_p \in \{0, 1\}$, $d \in \mathbb{Z}$ and
${\bowtie} \in \{<, \le, \ge, >\}$ (the syntax of André, Lime and Roux, arXiv:2004.09171v4). The survey arXiv:1807.07091v3 uses instead conjunctions of atomic constraints $x \bowtie p + c$, $x \bowtie c$ and $p \bowtie c$ with $p \in P$, $c \in \mathbb{Z}$ and ${\bowtie} \in \{<, \le, =, \ge, >\}$ (Section 2.1 of that survey); the results cited from the survey are stated for that syntax.

**Automata.** A *parametric timed automaton* (PTA) is a tuple $\mathcal{A} = (\Sigma, L, \ell_0, X, P, I, E)$ with a finite
set $\Sigma$ of actions, a finite set $L$ of locations, an initial location $\ell_0$, an *invariant* $I(\ell)$ (a parametric
guard) for each location, and a finite set $E$ of edges $(\ell, g, a, R, \ell')$ with a parametric guard $g$, an action
$a \in \Sigma$ and a set $R \subseteq X$ of clocks to reset. For a parameter valuation $v$, $v(\mathcal{A})$ is the timed
automaton obtained by replacing each parameter $p$ by $v(p)$. Its *concrete states* are pairs $(\ell, \mu)$ with $\mu$
satisfying $v(I(\ell))$; from $(\ell, \mu)$ time may elapse by $d \ge 0$ while the invariant stays satisfied, and an edge
$(\ell, g, a, R, \ell')$ may be taken if $\mu$ satisfies $v(g)$, resetting the clocks in $R$ and entering a state satisfying
$I(\ell')$. A *run* starts in $(\ell_0, \mathbf{0})$ and alternates delays and edges. A run is *maximal* if it is infinite
(infinitely many edges) or cannot be extended by an edge; a finite maximal run is *deadlocked*.

**Subclasses.** A PTA is an *L/U-PTA* if its parameters are partitioned into *lower-bound* parameters, which occur only in
inequalities with ${\bowtie} \in \{\ge, >\}$, and *upper-bound* parameters, which occur only with ${\bowtie} \in \{\le, <\}$.
A *bounded* PTA comes with an interval with integer endpoints (no infinite supremum) for each parameter, and only valuations
in these intervals are considered; it is *closed bounded* if all intervals are closed and *open bounded* otherwise.

**Parametric problems.** For a set $T \subseteq L$ of target locations, the properties of a timed automaton are:
*reachability* (EF: some run visits $T$), *unavoidability* (AF: every maximal run visits $T$), *preservability* (EG: some
maximal run stays in $T$), *deadlock-existence* (ED: some maximal run is finite) and *cycle-existence* (EC: some maximal run
is infinite). For such a property $\phi$, *$\phi$-emptiness* asks, given a PTA and an instance of $\phi$, whether the set of
parameter valuations $v$ such that $v(\mathcal{A})$ satisfies $\phi$ is empty, and *$\phi$-universality* asks whether it
contains all parameter valuations.

## Depends on

- [Timed Büchi automata and timed regular languages](../timed-buchi-automata.md)

## Proof depends on

None.

## Expansion

EF-emptiness and AG-universality are dual, as are AF-emptiness and EG-universality. In L/U-PTAs, increasing upper-bound
parameters or decreasing lower-bound parameters only adds runs, which makes EF-emptiness decidable for them. Other papers
use slightly different syntax: for instance André, Lime and Markey allow atomic constraints $x \bowtie p + c$, $x \bowtie c$
and $p \bowtie c$ with ${\bowtie} \in \{<, \le, =, \ge, >\}$ and an integer $c$, with parameter valuations in
$\mathbb{Q}_{\ge 0}$, and define the language of $v(\mathcal{A})$ as the set of untimed words of its maximal runs.

## Sources

- É. André, D. Lime, O. H. Roux, "Reachability and liveness in parametric timed automata", *Logical Methods in Computer Science* 18(1), article 31, 2022, doi:[10.46298/lmcs-18(1:31)2022](https://doi.org/10.46298/lmcs-18(1:31)2022). Numbering of the version read, arXiv:2004.09171v4: Definition 2.1 (PTA), Definition 2.2 (concrete semantics), the definitions of runs and maximal runs in Section 2.2, Definition 2.4 (L/U-PTA), Definition 2.7 (bounded PTA) and Section 2.4 (decision problems).
- É. André, D. Lime, N. Markey, "Language preservation problems in parametric timed automata", *Logical Methods in Computer Science* 16(1), article 5, 2020, doi:[10.23638/LMCS-16(1:5)2020](https://doi.org/10.23638/LMCS-16(1:5)2020). Numbering of the version read, arXiv:1807.07091v3: Definition 2.3 and Section 2 (constraints, semantics, untimed languages and traces).
