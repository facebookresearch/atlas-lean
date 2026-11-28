# Full and weak timed opacity of timed automata are undecidable

Whether an attacker who observes the timed traces of a timed automaton can never tell if a secret location was visited is undecidable, already for one action without silent transitions, for one clock, and for two clocks without silent transitions.

**Theorem.** Consider timed automata $\mathcal A = (\Sigma, L, \ell_0, L_{\mathrm{priv}}, L_f, X, I, E)$ with actions $\Sigma$, locations $L$, an initial location $\ell_0$, a set $L_{\mathrm{priv}} \subseteq L$ of *private* locations, a set $L_f \subseteq L$ of final locations, clocks $X$, invariants $I$, and edges $(\ell, g, a, R, \ell')$ with a guard $g$, an action $a \in \Sigma \cup \{\varepsilon\}$ ($\varepsilon$ unobservable) and a set $R$ of reset clocks, under the usual dense-time semantics. A run starts in $\ell_0$ with all clocks $0$ and ends in a final location; it is *private* if it visits $L_{\mathrm{priv}}$ and *public* otherwise. Its *trace* is the timed word of its observable actions with their absolute times. Let $\mathrm{Tr}_{\mathrm{priv}}(\mathcal A)$ and $\mathrm{Tr}_{\mathrm{pub}}(\mathcal A)$ be the sets of traces of private and of public runs. $\mathcal A$ is *fully opaque* if $\mathrm{Tr}_{\mathrm{priv}}(\mathcal A) = \mathrm{Tr}_{\mathrm{pub}}(\mathcal A)$, and *weakly opaque* if $\mathrm{Tr}_{\mathrm{priv}}(\mathcal A) \subseteq \mathrm{Tr}_{\mathrm{pub}}(\mathcal A)$. The full opacity problem and the weak opacity problem, asking given $\mathcal A$ whether it is fully, respectively weakly, opaque, are undecidable in each of the following cases:

1. timed automata with one action and no $\varepsilon$-transition (Theorem 5.2 of the source);
2. timed automata with one clock (Theorem 5.4);
3. timed automata with at least two clocks, with or without $\varepsilon$-transitions (Theorem 5.7).

For one-clock timed automata without $\varepsilon$-transitions both problems are decidable, with non-primitive recursive complexity (Theorem 5.5); for observable event-recording automata they are [PSPACE](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)-complete (Theorem 5.16); and the weaker $\exists$-opacity problem, whether some trace is produced by both a private and a public run, is inter-reducible with reachability for timed automata (Theorem 4.6), hence decidable.

## Depends on

- [Timed automata over finite timed words](timed-automata-over-finite-timed-words.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Universality of timed automata is undecidable](../universality-of-timed-automata-is-undecidable.md)

## Expansion

All cases reduce universality of timed automata, whether a timed automaton accepts every finite timed word, which is undecidable for one-action automata (Ouaknine and Worrell), for one-clock automata with $\varepsilon$-transitions (Abdulla, Deneux, Ouaknine, Quaas and Worrell) and for automata with two or more clocks. For a one-action automaton $\mathcal A$, build $\mathcal B$ with a new initial location left urgently by two $a$-transitions: one enters a private location and then $\mathcal A$; the other reaches, after a second urgent $a$, a public location from which every timed word over $\{a\}$ can be read; both branches end with a final $a$. Then $\mathrm{Tr}_{\mathrm{priv}}(\mathcal B)$ encodes $\mathrm{Tr}(\mathcal A)$ and $\mathrm{Tr}_{\mathrm{pub}}(\mathcal B)$ encodes all timed words, so $\mathcal B$ is fully opaque iff $\mathcal A$ is universal. Full and weak opacity are inter-reducible (Theorem 4.5), by swapping the roles of private and public runs in a copy of the automaton.

## Sources

- É. André, S. Dépernet and E. Lefaucheux, "The Bright Side of Timed Opacity", *Logical Methods in Computer Science* 22(2), 2026, article 31, doi:[10.46298/lmcs-22(2:31)2026](https://doi.org/10.46298/lmcs-22(2:31)2026); read as arXiv:2408.12240v7, whose numbering is used here: Definitions 2.1, 2.3, 3.1 and 3.2 and Section 3.1 (private and public runs, traces), Theorems 4.5 and 4.6, Theorem 5.2 with its proof, Theorems 5.4, 5.5, 5.7 and 5.16.
