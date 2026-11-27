# Nested words and nested word automata

A *matching relation* of length $\ell$ is a set $\leadsto \subseteq \{-\infty, 1, \dots, \ell\} \times \{1, \dots, \ell, +\infty\}$ of nesting edges that go forward, have at least one endpoint in $\{1, \dots, \ell\}$ (so $(-\infty, +\infty)$ is not an edge), share no position of $\{1, \dots, \ell\}$ and
do not cross ($i \leadsto j$ and $i' \leadsto j'$ never give $i < i' \le j < j'$); positions with an outgoing edge are *calls*, those with an incoming
edge *returns*, edges from $-\infty$ or to $+\infty$ are *pending*, and the other positions are *internal*. A *nested word* over $\Sigma$ is a word
$a_1 \cdots a_\ell$ with a matching relation of length $\ell$. Tagging each call $a$ as $\langle a$ and each return $a$ as $a\rangle$ is a bijection from
nested words over $\Sigma$ onto words over the tagged alphabet $\hat\Sigma = \Sigma \cup \langle\Sigma \cup \Sigma\rangle$, which is a pushdown alphabet.

A *nested word automaton* $A = (Q, q_0, Q_f, P, p_0, P_f, \delta_c, \delta_i, \delta_r)$ has finite sets $Q$ of linear states and $P$ of hierarchical states, $q_0 \in Q$, $Q_f \subseteq Q$, $p_0 \in P$, $P_f \subseteq P$ and transition
functions $\delta_c : Q \times \Sigma \to Q \times P$, $\delta_i : Q \times \Sigma \to Q$ and $\delta_r : Q \times P \times \Sigma \to Q$: at a call it passes a linear state forward and a
hierarchical state along the nesting edge, which the matching return consumes; a pending return reads the initial hierarchical state $p_0$. It accepts if its run ends in $Q_f$ and the hierarchical
states on pending calls are in $P_f$; a language of nested words is *regular* if some nested word automaton accepts it. On tagged words,
linearly accepting nested word automata (those with $P_f = P$, whose acceptance does not depend on pending calls) are deterministic
[visibly pushdown automata](visibly-pushdown-automata.md), and a language of tagged
words is a visibly pushdown language if and only if the corresponding language of nested words is regular.

## Depends on

- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)

## Sources

- R. Alur and P. Madhusudan, "Adding nesting structure to words", *Journal of the ACM* 56(3), 2009, author copy <https://www.cis.upenn.edu/~alur/Jacm09.pdf>: Section 2.1 (matching relations, nested sequences and nested words), Lemma 2.1 (the tagging bijection), Section 3.1 (nested word automata, runs and regularity) and Section 5.1 (visibly pushdown automata and languages as tagged-word views of nested word automata).
