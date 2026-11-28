# Qualitative reachability in two-dimensional VASS Markov decision processes is undecidable

No algorithm decides whether a controller can reach a target control state surely, almost surely or limit-surely in a two-dimensional VASS
Markov decision process, even when it is deadlock free or when only the random player changes the counters.

**Theorem (Abdulla, Ciobanu, Mayr, Sangnier and Sproston).** For [VASS Markov decision processes](vass-markov-decision-processes-and-qualitative-r.md):

1. the sure, almost-sure and limit-sure reachability and repeated reachability problems are undecidable for $2$-dimensional deadlock-free VASS-MDPs;
2. the sure, almost-sure and limit-sure reachability and repeated reachability problems are undecidable for $2$-dimensional P-VASS-MDPs;
3. the almost-sure and limit-sure reachability and repeated reachability problems are undecidable for $2$-dimensional deadlock-free P-VASS-MDPs.

In dimension $1$, sure and almost-sure reachability are decidable (Brázdil, Brožek, Etessami, Kučera and Wojtczak). For 1-VASS-MDPs, where only the controller changes
the counters, the source shows that the sure, almost-sure and limit-sure reachability problems and the sure and almost-sure repeated reachability problems are
decidable in every dimension.

## Depends on

- [VASS Markov decision processes and qualitative reachability](vass-markov-decision-processes-and-qualitative-r.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

For item 1, the proof reduces the reachability problem for deterministic, deadlock-free Minsky machines. The controller simulates the machine; at each zero test it chooses a
branch, and a probabilistic state then either continues the simulation or checks the claim, moving to an absorbing losing state when the claim is false. A dishonest
controller is therefore caught with positive probability at each cheat, while an honest one reaches the target exactly when the machine halts, so all three qualitative
reachability questions are equivalent to reaching the final state; since the only transition leaving the final state of the machine is a self-loop, repeated reachability follows as well. Items 2 and 3 adapt the reduction to P-VASS-MDPs, in which only the probabilistic player changes the counters; for deadlock-free P-VASS-MDPs, sure (repeated) reachability is decidable, which is why item 3 omits it.

## Sources

- P. A. Abdulla, R. Ciobanu, R. Mayr, A. Sangnier and J. Sproston, "Qualitative analysis of VASS-induced MDPs", in *Foundations of Software Science and Computation Structures (FoSSaCS 2016)*, Lecture Notes in Computer Science 9634, pp. 319–334, Springer, 2016, doi:10.1007/978-3-662-49630-5_19; read in arXiv:1512.08824v2: Theorem 1 in Section 2.4 ("Undecidability in the general case") and the remark after it, Theorems 3 and 5 for P-VASS-MDPs in Section 3, and Theorems 6–9 for 1-VASS-MDPs in Section 4, with the numbering of that version.
