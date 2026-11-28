# Timed monitorability of timed Büchi automata properties is undecidable

For a property of infinite timed words given by a nondeterministic timed Büchi automaton, the three-valued monitoring verdict of a finite observation is not computable, and both strong and weak monitorability are undecidable.

Following the source (Section 2), a timed word, finite or infinite, has non-decreasing nonnegative timestamps (several letters may occur at the same time) and no condition that time diverges; the [linked page](../timed-buchi-automata.md) uses strictly increasing unbounded time sequences, a convention the source does not use, and the theorem is meant in the source's convention.

**Theorem.** Let $\varphi$ be a set of infinite timed words over $\Sigma$. An *observation* $(\rho, t)$ is a finite timed word $\rho$ with rational timestamps and a rational time point $t$ at least the last timestamp of $\rho$; $\rho \cdot_t \mu$ denotes the extension of $\rho$ by an infinite timed word $\mu$ shifted to start at time $t$. The *monitoring function* gives $V_\varphi(\rho, t) = \top$ if $\rho \cdot_t \mu \in \varphi$ for every infinite timed word $\mu$, $V_\varphi(\rho, t) = \bot$ if $\rho \cdot_t \mu \notin \varphi$ for every $\mu$, and $?$ otherwise; write $V_\varphi(\rho)$ for $V_\varphi(\rho, \tau(\rho))$ with $\tau(\rho)$ the last timestamp of $\rho$. The property $\varphi$ is *strongly $(\rho, t)$-monitorable* if for every finite timed word $\rho'$ there is a finite timed word $\rho''$ with $V_\varphi(\rho \cdot_t \rho' \cdot \rho'') \in \{\top, \bot\}$, and *weakly $(\rho, t)$-monitorable* if there is a finite timed word $\rho''$ with $V_\varphi(\rho \cdot_t \rho'') \in \{\top, \bot\}$; it is *strongly* (*weakly*) *monitorable* if it is so for the empty observation $(\varepsilon, 0)$. For properties given by [timed Büchi automata](../timed-buchi-automata.md) $\mathcal A$, with $\varphi = L(\mathcal A)$:

1. the function mapping $\mathcal A$ and an observation $(\rho, t)$ to $V_{L(\mathcal A)}(\rho, t)$ is not computable (Theorem 1 of the source);
2. it is undecidable, given $\mathcal A$, whether $L(\mathcal A)$ is strongly monitorable, and whether it is weakly monitorable (Theorem 2);
3. strong and weak $(\rho, t)$-monitorability remain undecidable even for a fixed observation $(\rho, t)$ (Corollary 1).

For properties given by deterministic timed Muller automata, strong and weak monitorability and their $(\rho, t)$ variants are decidable (Theorem 3 and Corollary 2), and the monitoring function is computable when automata for both the property and its complement are given (Proposition 3).

## Depends on

- [Timed Büchi automata](../timed-buchi-automata.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Universality of timed automata is undecidable](../universality-of-timed-automata-is-undecidable.md)

## Expansion

For every property, $V_\varphi(\varepsilon, 0) = \top$ iff $\varphi$ contains every infinite timed word, so computing the monitoring function would decide universality of timed Büchi automata, which is undecidable. For monitorability, the source adapts the reduction of Diekert, Muscholl and Walukiewicz for untimed Büchi automata: from a complete nondeterministic timed automaton $\mathcal A$ over finite words one builds, with a fresh letter $\#$ and three new locations, a timed Büchi automaton whose language is strongly monitorable iff $\mathcal A$ accepts every finite timed word. Weak monitorability is handled by reducing universality of timed Büchi automata to weak $\top$-monitorability, the variant that only asks for the verdict $\top$, and then to weak monitorability. A good expansion also links a page for the undecidability of universality of timed automata over finite timed words (Alur and Dill), which the strong-monitorability reduction uses; the linked page treats timed Büchi automata. The linked universality result is stated for timed words with strictly increasing, unbounded time stamps, while the source's words have non-decreasing time stamps and need not diverge, so a good expansion also adds the form of universality the source uses. One route: the words outside the linked convention, those in which two letters occur at the same time or time converges, are accepted by a timed Büchi automaton (one guessing a position followed by a letter at the same time, or a position after which a clock reset there stays below $1$), and adding it to a given automaton turns universality over the linked words into universality over all of the source's words.

## Sources

- T. M. Grosen, S. Kauffman, K. G. Larsen and M. Zimmermann, "Time for Timed Monitorability", in *36th International Conference on Concurrency Theory (CONCUR 2025)*, Leibniz International Proceedings in Informatics 348, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2025, article 19, doi:[10.4230/LIPIcs.CONCUR.2025.19](https://doi.org/10.4230/LIPIcs.CONCUR.2025.19); read as arXiv:2504.10008v3, whose numbering is used here: Definitions 1, 2 and 3, Proposition 3, Theorems 1, 2 and 3, Corollaries 1 and 2.
