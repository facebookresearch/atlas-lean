# Universality of min-plus weighted automata over the integers is undecidable

No algorithm decides, given a nondeterministic weighted automaton with integer weights under min-plus semantics and an integer threshold $v$, whether every word has value below $v$; this holds already for complete automata with transition weights in $\{-1,0,1\}$ and threshold $1$.

**Definitions.** A *$\mathbb{Z}$-weighted finite automaton* ($\mathbb{Z}$-WFA) over a finite alphabet $\Sigma$ is a nondeterministic finite automaton whose transitions carry weights in $\mathbb{Z}$, together with initial and final weights in $\mathbb{Z} \cup \{\infty\}$. The weight of a run is the sum of its initial weight, its transition weights and its final weight; the value $\mathcal{A}(w)$ of a word $w \in \Sigma^*$ is the minimum weight of an accepting run on $w$, and $\infty$ if there is none. This is a [weighted automaton](../weighted-automata-over-a-semiring.md) over the min-plus semiring $(\mathbb{Z} \cup \{\infty\}, \min, +, \infty, 0)$. The automaton is *complete* if every state has an outgoing transition on every letter. The *universality problem* asks, given a $\mathbb{Z}$-WFA $\mathcal{A}$ and a threshold $v \in \mathbb{Z}$, whether $\mathcal{A}(w) < v$ for every $w \in \Sigma^*$.

**Theorem.** The universality problem for nondeterministic $\mathbb{Z}$-WFAs is undecidable, even for complete $\mathbb{Z}$-WFAs whose transition weights lie in $\{-1, 0, 1\}$ and with the fixed threshold $v = 1$ (Theorem 4.1 of the source).

The automata produced by the reduction moreover have all initial weights in $\{0, \infty\}$ and all final weights equal to $0$. The source states the problem with the strict inequality; since the weights are integers, the variants with $\le$ reduce to it. By contrast, universality is decidable when all weights are natural numbers.

## Depends on

- [Weighted automata over a semiring](../weighted-automata-over-a-semiring.md)
- [Semirings and formal power series on a free monoid](../semirings-and-formal-power-series.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces from the *0-halting problem* for deterministic two-counter machines (does the machine halt with both counters equal to $0$?), which is undecidable because a machine can clear its counters before halting. Given a machine $M$, one computes a complete $\mathbb{Z}$-WFA $\mathcal{A}$ with transition weights in $\{-1,0,1\}$ such that $\mathcal{A}(w) \le 1$ for every word $w$, and $M$ 0-halts if and only if some word has $\mathcal{A}(w) = 1$. The letters of $\mathcal{A}$ are the commands of $M$ (with each conditional jump recorded by the branch taken), so a word is a candidate command trace of the run of $M$. The automaton is the union of five gadgets, each checking one kind of violation: a command checker for successive commands that cannot follow each other, and, for each of the two counters, a positive-jump checker (the "counter positive" branch taken when the counter is $0$) and a zero-jump checker (the "counter zero" branch taken when it is not). If the word is the command trace of the 0-halting run, every run of $\mathcal{A}$ has weight exactly $1$; otherwise the violated gadget has a run of weight at most $0$. Hence $M$ 0-halts if and only if $\mathcal{A}$ is not universal for the threshold $1$.

## Sources

- S. Almagor, U. Boker and O. Kupferman, "What's decidable about weighted automata?", *Information and Computation* 282, 2022, article 104651, doi:[10.1016/j.ic.2020.104651](https://doi.org/10.1016/j.ic.2020.104651); conference version in *Automated Technology for Verification and Analysis (ATVA 2011)*, Lecture Notes in Computer Science 6996, pp. 482–491, doi:[10.1007/978-3-642-24372-1_37](https://doi.org/10.1007/978-3-642-24372-1_37). Read in the authors' copy of the journal version at <https://faculty.runi.ac.il/udiboker/files/wajournal.pdf>, whose numbering is used here: the definitions of WFAs and of the universality problem in Section 2, Theorem 3.1 (simulation of two-counter machines) and Theorem 4.1 (undecidability of universality).
