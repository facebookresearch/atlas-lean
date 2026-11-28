# State reachability for dense-choice counter machines with four bounded counters is undecidable

No algorithm decides control-state reachability for dense-choice counter machines with four purely dense-choice counters, even when
every counter stays between $0$ and $1$ and is compared only with $0$ and $1$.

**Proposition.** The state reachability problem is undecidable for bounded purely-DCMs, in the sense of
[dense-choice counter machines](dense-choice-counter-machines.md). It is undecidable already for DCMs with four purely dense-choice,
$1$-bounded, $1$-testable counters (Proposition 3.1 of the source).

For integer counters, boundedness makes a machine finite-state; dense-choice counters keep infinitely many values even when bounded, which
is why boundedness does not restore decidability. With a single bounded $k$-testable counter the binary reachability relation is
definable in a decidable logic, and the cases of two and three purely dense-choice bounded counters are open.

## Depends on

- [Dense-choice counter machines](dense-choice-counter-machines.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](two-counter-machines-are-universal.md)

## Expansion

The proof adapts the simulation of Minsky machines by four purely dense-choice counters. Two counters store a value $\delta$ chosen once at
the start of the computation, and the other two are changed only by $\pm\delta$, so an integer $k$ is encoded as $k\delta$. With $1$-bounded
counters only values up to $\lfloor 1/\delta \rfloor$ can be encoded, but $\delta$ can be chosen arbitrarily small, and a run that chooses $\delta$
too large crashes when a counter would exceed $1$. Since every halting computation of a two-counter machine uses bounded counter values,
the final state is reachable exactly when the simulated machine halts.

## Sources

- F. Bouchy, A. Finkel and P. San Pietro, "Dense-choice counter machines revisited", in *Proceedings of the International Workshop on Verification of Infinite-State Systems (INFINITY 2009)*, Electronic Proceedings in Theoretical Computer Science 10, pp. 3–22, 2009, doi:10.4204/EPTCS.10.1; journal version *Theoretical Computer Science* 542:17–31, 2014, doi:10.1016/j.tcs.2014.04.029. Read in arXiv:0911.3405v1: Proposition 3.1 in Section 3.1 with its proof, the summary table of Section 3, and Proposition 3.2 (a single bounded $k$-testable counter).
