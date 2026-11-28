# Reachability games on recursive stopwatch and timed automata are undecidable

No algorithm decides reachability games on recursive stopwatch automata with two stopwatches, or on glitch-free ones with three; under
bounded time, they stay undecidable for recursive timed automata with three clocks and for glitch-free recursive stopwatch automata
with four stopwatches.

**Theorem.** The reachability game problem for [recursive hybrid automata](recursive-hybrid-automata-and-their-reachability.md) is
undecidable for:

1. unrestricted recursive stopwatch automata with $2$ stopwatches;
2. glitch-free recursive stopwatch automata with $3$ stopwatches;
3. unrestricted recursive timed automata with $3$ clocks, under bounded time;
4. glitch-free recursive stopwatch automata with $4$ stopwatches, under bounded time.

All four results hold even for hierarchical automata. On the positive side, reachability games on glitch-free recursive stopwatch
automata with at most two stopwatches are decidable, because hybrid automata with two stopwatches have a finite bisimulation.

## Depends on

- [Recursive hybrid automata and their reachability games](recursive-hybrid-automata-and-their-reachability.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Each case reduces the halting problem for two-counter machines. Counter values are encoded in variable values, one main component
per instruction; for example, in the time-bounded case with three clocks $x, y, z$, the component of the $k$-th instruction is entered
with $x = 1/(2^{k+c} 3^{k+d})$, $y = 1/2^k$ and $z = 0$, where $c, d$ are the counter values. Achilles simulates the machine by choosing delays, and the tortoise may challenge a step
by entering a checking component, invoked through a box, that can reach the target exactly when the step was simulated correctly;
passing variables by value lets the check run without disturbing the simulation, and in the time-bounded cases the encoding is
arranged so that the delays of successive instructions sum to a bounded total. The machine starts at $(\ell_0, 0, 0)$, and the linked universality theorem states that halting from zero counters is undecidable; a good expansion links a page for the correctness of the checking components. The version read sketches proofs only for the bounded-time cases (Lemmas 1–3 in Section 4) and refers to the authors' full version for cases 1 and 2.

## Sources

- S. N. Krishna, L. Manasa and A. Trivedi, "Improved undecidability results for reachability games on recursive timed automata", in *GandALF 2014*, Electronic Proceedings in Theoretical Computer Science 161, pp. 245–259, 2014, doi:10.4204/EPTCS.161.21; version arXiv:1408.5968v1: Theorem 1 in Section 3.3 with its proof in Section 4 (Lemmas 1 and 2 for the time-bounded cases), and Theorem 2 for glitch-free automata with two stopwatches.
