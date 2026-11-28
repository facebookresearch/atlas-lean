# History-deterministic vector addition systems

A vector addition system with states reads letters while changing nonnegative counters; it is history-deterministic when its nondeterminism
can be resolved on the fly, choosing each transition from the run so far and the next letter only, without losing any accepted word.

**VASS and their languages.** For $k \ge 1$, a $k$-dimensional *vector addition system with states* ($k$-VASS) $\mathcal{A} = (\Sigma, Q, \Delta, q_0, F)$ has a finite alphabet $\Sigma$, a finite set of states $Q$, transitions
$\Delta \subseteq Q \times (\Sigma \cup \{\varepsilon\}) \times \mathbb{Z}^k \times Q$, an initial state $q_0$ and final states $F$. Configurations are pairs $(q, v) \in Q \times \mathbb{N}^k$, and a transition $(q, a, e, q')$ leads from
$(q, v)$ to $(q', v + e)$ provided $v + e \in \mathbb{N}^k$, reading $a$. A run is accepting if it ends in a final configuration: under the *coverability semantics* any configuration with state in $F$, under
the *reachability semantics* only $(q, \mathbf{0})$ with $q \in F$. The language $L(\mathcal{A})$ is the set of words read by accepting runs from $(q_0, \mathbf{0})$. As an input, a VASS is given by its finite tables with integer effect vectors. $\mathcal{A}$ is *$\varepsilon$-free* if no transition reads $\varepsilon$,
and *deterministic* if it is $\varepsilon$-free and each state and letter allow at most one transition.

**History-determinism.** A *resolver* is a function that, given a finite run and a next letter $a$, returns a transition reading $a$ that can be taken from the last configuration; it determines one run on
each word. The VASS is *history-deterministic* (HD) if some resolver builds, for every word $w \in L(\mathcal{A})$, an accepting run on $w$ from $(q_0, \mathbf{0})$. A language is *HD-VASS recognizable*, in a
given semantics, if some HD VASS recognizes it. Every deterministic VASS is history-deterministic, and HD VASS can recognize languages that deterministic VASS cannot.

## Depends on

None.

## Proof depends on

None.

## Sources

- S. Bose, D. Purser and P. Totzke, "History-deterministic vector addition systems", in *34th International Conference on Concurrency Theory (CONCUR 2023)*, LIPIcs 279, paper 18, 2023, doi:10.4230/LIPIcs.CONCUR.2023.18; read in arXiv:2305.01981v2: Section 2 (vector addition systems, coverability and reachability semantics, determinism and history-determinism via resolvers) and the separation results of Section 3.1 (Theorem 1), with the numbering of that version.
