# Decision problems for reversible two-counter automata are not semidecidable

For real-time reversible deterministic one-way counter automata with at least two counters, emptiness, finiteness, infiniteness, inclusion, equivalence, regularity and context-freeness are undecidable, and none of them is even semidecidable.

**Definitions.** A *deterministic one-way counter automaton* with $k \ge 0$ counters, $\mathrm{DCA}(k)$, is a system $M = \langle Q, \Sigma, k, \triangleright, \triangleleft, \delta, q_0, F \rangle$ with a finite state set $Q$, an input alphabet $\Sigma$, endmarkers $\triangleright, \triangleleft \notin \Sigma$, an initial state $q_0$, accepting states $F \subseteq Q$ and a partial transition function

$$
\delta : Q \times (\Sigma \cup \{\triangleright, \triangleleft\}) \times \{+, \bot\}^k \to Q \times \{0, 1\} \times \{-1, 0, 1\}^k,
$$

which, depending on the state, the scanned symbol and which counters are zero ($\bot$) or positive ($+$), chooses the next state, whether the head stays ($0$) or moves right ($1$), and how each counter changes; a zero counter is never decremented. Configurations are $(q, w, h, c_1, \dots, c_k)$ with head position $h \in \{0, \dots, |w|+1\}$, starting from $(q_0, w, 0, 0, \dots, 0)$. The automaton halts when $\delta$ is undefined, and accepts $w$ if it halts in an accepting state. It is *reversible*, $\mathrm{REV\text{-}DCA}(k)$, if there is a reverse transition function

$$
\delta^{\leftarrow} : Q \times (\Sigma \cup \{\triangleright, \triangleleft\}) \times \{+, \bot\}^k \to Q \times \{0, -1\} \times \{-1, 0, 1\}^k
$$

that computes from each configuration its unique predecessor, so the computation can be stepped back deterministically. It works in *real time* if it halts on every accepted input $w$ within $|w| + 2$ steps. A problem is *semidecidable* if its set of yes-instances is computably enumerable.

**Theorem.** Let $k \ge 2$, and let $M$ and $M'$ range over real-time $\mathrm{REV\text{-}DCA}(k)$. None of the following questions is semidecidable: whether $L(M) = \emptyset$; whether $L(M)$ is finite; whether $L(M)$ is infinite; whether $L(M) \subseteq L(M')$; whether $L(M) = L(M')$; whether $L(M)$ is regular; whether $L(M)$ is context-free.

In particular all of them are undecidable.

## Depends on

- [Context-free languages](../../context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)
- [Recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Emptiness is not recognizable](../../computability/emptiness-and-equivalence-problems-for-programs/not-tm2-recognizable-empty.md)
- [Finiteness is not recognizable](../../computability/finiteness-problem-for-programs/not-tm2-recognizable-finite.md)
- [Finiteness is not co-recognizable](../../computability/finiteness-problem-for-programs/not-tm2-co-recognizable-finite.md)

## Expansion

The reduction is from emptiness, finiteness and infiniteness of the languages of Turing machines, none of which is semidecidable. By a result of Hartmanis and Hopcroft, which has no page here, every computably enumerable set of words over $\{1, 2\}$, suitably encoded as numbers, is the domain of a multiplying counter machine: a one-register machine that multiplies its register by one of $2, 3, 5, 7, \tfrac12, \tfrac13, \tfrac15, \tfrac17$ and branches when the product is not an integer. The set of suitably formatted valid computations of such a machine is the intersection of two languages accepted by real-time reversible one-counter automata, and running both in parallel gives a real-time $\mathrm{REV\text{-}DCA}(2)$ accepting exactly the valid computations. This language is empty, finite or infinite exactly when the Turing machine accepts the empty, a finite or an infinite set. Inclusion and equivalence follow by comparing with an automaton for the empty set, and regularity and context-freeness because the set of valid computations is regular, equivalently context-free, exactly when it is finite.

## Sources

- M. Kutrib and A. Malcher, "Reversible Computations of One-Way Counter Automata", in *Proceedings of the 12th International Workshop on Non-Classical Models of Automata and Applications (NCMA 2022)*, Electronic Proceedings in Theoretical Computer Science 367, pp. 126–142, 2022, doi:[10.4204/EPTCS.367.9](https://doi.org/10.4204/EPTCS.367.9); journal version: M. Kutrib and A. Malcher, "Reversible computations of one-way counter automata", *RAIRO – Theoretical Informatics and Applications* 58, article 5, 2024, doi:[10.1051/ita/2023011](https://doi.org/10.1051/ita/2023011) (not read). Read in the EPTCS version as posted at arXiv:2208.14720v1 ([arXiv](https://arxiv.org/abs/2208.14720v1)), whose numbering is used here: Definition 1 and the definitions of reversibility and real time in Section 2, Theorem 10 (multiplying counter machines), and Theorem 14 with its proof in Section 4.
