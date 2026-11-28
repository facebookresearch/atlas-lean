# Prioritized streaming string transducers

A prioritized streaming string transducer is a one-way automaton with string registers updated by copying assignments on its transitions, whose transitions out of a state are ordered by priority; it outputs along its highest-priority accepting run, which is how it models greedy, lazy and capturing-group regular-expression matching.

Let $\Sigma$ be a finite alphabet. For a finite set $Q$, a *priority list* over $Q$ is a finite sequence of pairwise distinct elements of $Q$. A *prioritized streaming string transducer* (PSST) is a tuple $T = (Q, \Sigma, X, \delta, \tau, E, q_0, F)$ where

- $Q$ is a finite set of states, $q_0 \in Q$ the initial state, and $X$ a finite set of string variables (registers);
- $\delta$ maps each pair $(q, a) \in Q \times \Sigma$ to a priority list, the targets of the $a$-transitions from $q$ in decreasing priority (possibly empty);
- $\tau$ maps each state $q$ to a pair $(P_1; P_2)$ of priority lists with no common element, the targets of the $\varepsilon$-transitions from $q$: those in $P_1$ have higher, and those in $P_2$ lower, priority than the letter transitions from $q$, and within each list priority decreases along the list;
- $E$ assigns to each transition $(q, a, q')$, with $a \in \Sigma$ and $q'$ in $\delta(q, a)$, or $a = \varepsilon$ and $q'$ in $\tau(q)$, an update $X \to (X \cup \Sigma)^*$;
- $F$ is a partial output function from $Q$ to $(X \cup \Sigma)^*$.

A *run* on a word $w$ is a sequence of transitions, starting in $q_0$, reading $w$, such that within every maximal block of consecutive $\varepsilon$-transitions no $\varepsilon$-transition occurs twice; so it has at most $|w|$ letter transitions and at most $(|w| + 1)$ times the number of $\varepsilon$-transitions of $T$ in total. Of two runs on the same word, one has *higher priority* if the other is a proper prefix of it (it continues by $\varepsilon$-transitions only), or if, at the first point where they choose different transitions, its choice comes first in the order given by $\delta$ and $\tau$, with $P_1$ before the letter transitions before $P_2$. The *accepting run* on $w$ is the highest-priority run ending in a state where $F$ is defined. All registers start empty; each transition replaces every register $x$ by its update evaluated at the old values; the output $T(w)$ is $F(q)$, for the last state $q$ of the accepting run, evaluated at the final values. If there is no accepting run, $T(w)$ is undefined. Thus $T$ realizes a partial function $\Sigma^* \to \Sigma^*$, with relation $R_T = \{(w, T(w)) : T(w) \text{ defined}\}$. $T$ is *copyless* if, on each transition, every register occurs at most once in all the updates together.

## Depends on

None.

## Proof depends on

None.

## Expansion

This is a definition. The priority order encodes regular-expression semantics: a greedy star tries its loop before its exit, a lazy star its exit before its loop, and a union its left branch first. For each regular expression $e$ with capturing groups and greedy and lazy operators, the source builds a PSST $T_e$ by induction on $e$ that stores in a register the match of each subexpression; to distinguish a group that did not participate in the match from a group that matched the empty word, that construction uses a special value null, which is a convention of the matcher built on top of PSSTs, not part of the definition above. The [leftmost-longest replaceAll](leftmost-longest-replaceall.md) is a different, POSIX-style matching policy.

## Sources

- T. Chen, A. Flores-Lamas, M. Hague, Z. Han, D. Hu, S. Kan, A. W. Lin, P. Rümmer and Z. Wu, "Solving string constraints with Regex-dependent functions through transducers with priorities and variables", Proceedings of the ACM on Programming Languages 6 (POPL), Article 45, 2022, doi:[10.1145/3498707](https://doi.org/10.1145/3498707); long version arXiv:2111.04298v2 (authors listed there as Alejandro Flores Lamas and Philipp Ruemmer), <https://arxiv.org/abs/2111.04298v2>: Section 4.1, Definition 4.2 with the definitions of runs, priority, accepting runs, output and copylessness, Example 4.3, and Section 4.2 (the PSST of a regular expression).
