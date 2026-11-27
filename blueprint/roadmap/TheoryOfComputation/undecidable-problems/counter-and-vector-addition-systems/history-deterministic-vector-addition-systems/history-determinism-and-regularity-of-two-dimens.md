# History-determinism and regularity of two-dimensional VASS are undecidable

No algorithm decides whether a two-dimensional vector addition system with states is history-deterministic, whether one history-deterministic
2-VASS includes another, whether a history-deterministic 2-VASS has a regular language, or whether a VASS has a history-deterministic equivalent.

**Theorem.** For [history-deterministic vector addition systems](history-deterministic-vector-addition-systems.md), in both the coverability and the reachability semantics unless stated otherwise:

1. it is undecidable whether a given $2$-VASS is history-deterministic;
2. language inclusion $L(\mathcal{A}) \subseteq L(\mathcal{B})$ is undecidable for history-deterministic $2$-VASS $\mathcal{A}$ and $\mathcal{B}$;
3. it is undecidable whether the language of a given history-deterministic $2$-VASS is regular;
4. it is undecidable whether a given VASS recognizes an HD-VASS recognizable language, in the coverability semantics and in the reachability semantics.

The results hold for $\varepsilon$-free systems, and so for systems with silent transitions. Dimension $2$ is the threshold in the coverability semantics: for a history-deterministic $1$-VASS $\mathcal{A}$ and any VASS $\mathcal{B}$, inclusion $L(\mathcal{B}) \subseteq L(\mathcal{A})$ is decidable, and
regularity of $L(\mathcal{A})$ is decidable in exponential space, by converting them into equivalent deterministic one-counter automata.

## Depends on

- [History-deterministic vector addition systems](history-deterministic-vector-addition-systems.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proofs reduce problems about deterministic two-counter Minsky machines, which a $2$-VASS can only weakly simulate since it cannot test for zero. For inclusion, a machine $M$ yields two
history-deterministic $2$-VASS whose languages, built from words that guess the counter operations of the run of $M$, satisfy $L(\mathcal{A}) \subseteq L(\mathcal{B})$ exactly when the run of $M$ never
reaches the halting state; history-determinism of a single $2$-VASS is reduced in the same way. For regularity, the constructed history-deterministic $2$-VASS has a regular language exactly when
the run of $M$ visits only finitely many configurations, which is undecidable. Item 4 combines a language whose last block cannot be read history-deterministically with the regularity
construction; in the reachability semantics it reduces instead from universality of VASS languages, which is undecidable.

## Sources

- S. Bose, D. Purser and P. Totzke, "History-deterministic vector addition systems", in *34th International Conference on Concurrency Theory (CONCUR 2023)*, LIPIcs 279, paper 18, 2023, doi:10.4230/LIPIcs.CONCUR.2023.18; read in arXiv:2305.01981v2: the theorems of Section 5 (Decision problems) on inclusion and history-determinism of $2$-VASS, on language history-determinism for coverability and reachability, and on regularity in dimensions $1$ and $2$.
