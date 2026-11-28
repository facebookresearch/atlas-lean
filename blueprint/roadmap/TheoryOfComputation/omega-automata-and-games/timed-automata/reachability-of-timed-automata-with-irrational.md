# Reachability of timed automata with an irrational guard constant is undecidable

Reachability for timed automata is decidable when guard constants are rational, but becomes undecidable as soon as guards may compare clocks with both $1$ and $\sqrt2$; as a consequence, membership of a value in the set of good parameter values of a one-parameter timed automaton is undecidable.

Here a timed automaton has finitely many control locations and real-valued clocks that grow at rate one; each edge carries a guard, a Boolean combination of comparisons of clocks with constants from a domain $D$, and a set of clocks reset to $0$ (as in [timed automata over finite timed words](decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md), without input letters). The *reachability problem* asks whether a terminal location is reachable from the initial location with all clocks $0$.

**Theorem.** The reachability problem for timed automata whose guard constants are taken from $D=\{1,\sqrt2\}$ is undecidable (Theorem 3.1 of the source); it stays undecidable when only a single clock is ever compared with $\sqrt2$ (Lemma 3.1).

As a consequence, for a parametric timed automaton $T$ with a single parameter $p$ (each clock compared with $p$ or with integer constants), let $P(T)$ be the set of parameter values for which the terminal location is reachable; given $T$ and a value $v$ that is a rational $r$ or its square root $\sqrt r$, it is undecidable whether $v\in P(T)$ (Theorem 4.1).

For rational guard constants, reachability is PSPACE-complete (Alur and Dill).

## Depends on

- [Timed automata over finite timed words](decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)
- [Parametric timed automata](parametric-timed-automata/parametric-timed-automata.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from reachability in two-counter machines. A counter value $c$ is stored by two clocks $x,y$ as $x=e(c)=c\sqrt2 \bmod 1$ whenever $y=0$; $e$ is injective and its values are dense in $[0,1)$. Gadgets with guards using $1$ and $\sqrt2$ keep this invariant (maintain), add $\sqrt2$ modulo $1$ (increment), subtract it (decrement, enabled only for nonzero counters) and test for zero, and running the gadgets of the two counters in parallel simulates the machine, so a terminal location of the timed automaton is reachable iff the machine reaches its terminal location. Replacing $\sqrt2$ by a parameter $p$ makes reachability of the original automaton equivalent to $\sqrt2\in P(T)$.

## Sources

- Anuj Puri, "An Undecidable Problem for Timed Automata", *Discrete Event Dynamic Systems* 9(2), 1999, pp. 135–146, doi:[10.1023/A:1008319830371](https://doi.org/10.1023/A:1008319830371); read in the open-access copy of the article at https://people.irisa.fr/Nicolas.Markey/PDF/Papers/deds9(2)-Pur.pdf: Section 2 (counter machines, timed automata, Theorem 2.1), Section 3 (Theorem 3.1 and Lemma 3.1) and Section 4 (Theorem 4.1).
