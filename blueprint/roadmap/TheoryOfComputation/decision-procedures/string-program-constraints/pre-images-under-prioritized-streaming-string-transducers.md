# Pre-images of regular languages under prioritized streaming string transducers

For a prioritized streaming string transducer and a finite automaton, the set of inputs on which the transducer is defined and produces an output accepted by the automaton is a regular language, and an automaton for it can be computed in exponential time.

Let $T = (Q_T, \Sigma, X, \delta_T, \tau_T, E_T, q_{0,T}, F_T)$ be a [prioritized streaming string transducer](prioritized-streaming-string-transducers.md) and $A = (Q_A, \Sigma, \delta_A, q_{0,A}, F_A)$ a nondeterministic finite automaton over $\Sigma$. Then

$$
R_T^{-1}(L(A)) = \{ w \in \Sigma^* : T(w) \text{ is defined and } T(w) \in L(A) \}
$$

is regular, and a nondeterministic finite automaton $B$ with $L(B) = R_T^{-1}(L(A))$ can be computed in time exponential in the written sizes of $T$ and $A$.

## Depends on

- [Prioritized streaming string transducers](prioritized-streaming-string-transducers.md)

## Proof depends on

None.

## Expansion

This node still needs its proof, and the construction printed in the source does not establish it as written. The source sketches the following proof (long version, Appendix A.3). Dropping the priorities of $T$ and intersecting with $A$ is wrong: it accepts $w$ when some run of $T$, not necessarily the highest-priority accepting one, outputs a word of $L(A)$. Instead $B$ simulates the accepting run of $T$. A state of $B$ records the current state of $T$; for each register $x$, its $A$-abstraction, the set of pairs $(p, q)$ of states of $A$ such that $A$ can go from $p$ to $q$ reading the word stored in $x$, updated along each transition by composing abstractions; the set of $\varepsilon$-transitions of $T$ taken since the last letter, to forbid repeating one; and the set of states of $T$ reachable by runs of higher priority on the same input, intended to certify that no higher-priority run is accepting. By the printed conditions, a state $(q, \rho, \Lambda, S)$ of $B$ is accepting when all three hold: (1) $F_T(q)$ is defined; (2) $F_T(q')$ is undefined for every $q' \in S$; and (3) the output $F_T(q)$, abstracted through the registers, leads from $q_{0,A}$ to a final state of $A$. The number of states is exponential in $|T|$ and $|A|$.

Proof obligations. As printed, the acceptance conditions of $B$ are wrong at the end of the input in two ways; the counterexamples below refute the printed construction, not the published lemma.

1. They do not exclude a higher-priority run that extends the current run by $\varepsilon$-transitions after the last letter. Example: let $F(q_0) = a$, $\tau(q_0) = ((q_1); ())$, $F(q_1) = b$, no letter transitions, and let $A$ accept only $a$. The run $q_0 \to q_1$ has priority over its prefix $q_0$, so $T(\varepsilon) = b \notin L(A)$; but the initial state $(q_0, \rho_\varepsilon, \emptyset, \emptyset)$ of $B$ meets all three acceptance conditions, so $B$ accepts $\varepsilon$.
2. Through condition (2), they count as competitors states that the rule for a lower-priority $\varepsilon$-transition from $q$ puts into $S$ only because the letter transitions out of $q$ have higher priority; at the end of the input no letter follows, and the run stopping at $q$ is a proper prefix of the current run, so it has lower priority. Example: let $F(q_0) = a$, $\tau(q_0) = ((); (q_1))$, $F(q_1) = b$, no letter transitions, and let $A$ accept only $b$. Then $T(\varepsilon) = b \in L(A)$, but $B$ rejects $\varepsilon$: its initial state fails the output condition, and the only other reachable state, $(q_1, \rho', \{(q_0, q_1)\}, \{q_0\})$, fails the condition that no state of $S$ has a defined output.

An expansion must repair both, for instance by recording separately the states owed to pending letter transitions and checking $\varepsilon$-only extensions of the current run at acceptance, and then prove the repaired construction correct and of exponential size. (The printed rules already saturate the higher-priority states collected at a divergence while avoiding the $\varepsilon$-transitions used in the current block, so that part needs no change.)

This lemma is what makes backward propagation of regular constraints possible for string functions defined by PSSTs, such as capture-group extraction and replaceAll under regular-expression semantics.

## Sources

- T. Chen, A. Flores-Lamas, M. Hague, Z. Han, D. Hu, S. Kan, A. W. Lin, P. Rümmer and Z. Wu, "Solving string constraints with Regex-dependent functions through transducers with priorities and variables", Proceedings of the ACM on Programming Languages 6 (POPL), Article 45, 2022, doi:[10.1145/3498707](https://doi.org/10.1145/3498707); long version arXiv:2111.04298v2 (authors listed there as Alejandro Flores Lamas and Philipp Ruemmer), <https://arxiv.org/abs/2111.04298v2>: Definition 5.4 and Lemma 5.5 (statement in Section 5.2), and Appendix A.3 (proof of Lemma 5.5).
