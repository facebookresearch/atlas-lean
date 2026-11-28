# Cost-bounded reachability in priced probabilistic timed automata is undecidable

No algorithm decides whether some policy of a priced probabilistic timed automaton reaches a goal location with probability at least $p$ while accumulating cost at most $\kappa$; this holds with three clocks and stopwatch or strictly positive cost rates, and with two clocks when cost rates may be negative.

**Priced probabilistic timed automata.** A *priced probabilistic timed automaton* (PPTA) is a tuple $(L, l_{\mathrm{init}}, X, \mathit{edges}, r)$ with a finite set $L$ of locations, an initial location $l_{\mathrm{init}}$, a finite set $X$ of clocks, a finite set $\mathit{edges} \subseteq L \times \mathrm{Zones}(X) \times \mathrm{Dist}(2^X \times L)$ of edges, each with a guard (a zone) and a probability distribution, with rational probabilities, over pairs of a set of clocks to reset and a target location, and a cost-rate function $r \colon L \to \mathbb{Z}$. Its semantics is the Markov decision process whose states are triples $(l, v, c)$ of a location, a clock valuation and the accumulated cost, starting from $(l_{\mathrm{init}}, \mathbf{0}, 0)$: a time transition of duration $d > 0$ leads to $(l, v + d, c + r(l)\, d)$, and a discrete transition takes an edge whose guard holds, resetting the drawn clocks and moving to the drawn location. A *policy* maps finite runs to the next transition. The PPTA is *simple* if the clocks reset by an edge do not depend on the probabilistic outcome.

**Theorem (Berendsen, Chen and Jansen).** *Cost-bounded probabilistic reachability* asks, given a PPTA, a goal location $l_G$, a rational probability $p \in (0, 1]$ and a cost bound $\kappa \in \mathbb{N}$, whether some policy reaches a state $(l_G, v, c)$ with $c \le \kappa$ with probability at least $p$. This problem is undecidable for simple PPTA in each of the following cases:

1. three clocks and cost rates in $\{0, 1\}$ (stopwatch cost);
2. two clocks and arbitrary integer cost rates;
3. three clocks and strictly positive integer cost rates.

(Theorems 1, 2 and 3 of the source, one per case.)

The source notes that the results also hold for classes of policies that contain the deterministic policies used in the proofs.

## Depends on

- [Timed automata over finite timed words](../decision-problems-for-timed-languages/timed-automata-over-finite-timed-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Each case reduces the halting problem for two-counter Minsky machines, undecidable because two-counter machines simulate Turing machines. For a machine $M$ the construction gives a PPTA with a goal location $l_G$ such that some policy reaches $l_G$ with probability $1$ within cost $8$ if and only if $M$ does not halt (a probabilistic choice at the start gives the same for thresholds $p < 1$). The PPTA has one location per instruction and encodes the counters $a, b$ by the clock value $x = 2^{-a} 3^{-b}$; after each simulated instruction, test subautomata reach $l_G$ with probability $1$ within the cost bound only if the step was taken at the correct time. So only the policy that simulates $M$ faithfully can meet the bounds, and if $M$ halts this policy reaches the halting location with positive probability. With negative cost rates allowed, the test subautomata need fewer clocks, which gives the two-clock case.

## Sources

- J. Berendsen, T. Chen and D. N. Jansen, "Undecidability of Cost-Bounded Reachability in Priced Probabilistic Timed Automata", in *Theory and Applications of Models of Computation (TAMC 2009)*, Lecture Notes in Computer Science 5532, Springer, 2009, pp. 128–137, doi:10.1007/978-3-642-02017-9_16; read in the author copy at <https://www.eis.mdx.ac.uk/staffpages/taoluechen/pub-papers/Tamc09.pdf>: Definitions 1–5 (PPTA, Markov decision processes, PPTA semantics, cost-bounded probabilistic reachability, simple PPTA), Theorems 1, 2 and 3, the remark on policies after them, and Sections 3.1, 3.7 and 3.8 (the proofs).
