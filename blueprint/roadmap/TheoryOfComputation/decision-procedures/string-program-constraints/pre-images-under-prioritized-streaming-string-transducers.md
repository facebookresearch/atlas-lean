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

This node still needs its proof, and the construction printed in the source does not establish it as written. The source sketches the following proof (long version, Appendix A.3). Dropping the priorities of $T$ and intersecting with $A$ is wrong: it accepts $w$ when some run of $T$, not necessarily the highest-priority accepting one, outputs a word of $L(A)$. Instead $B$ simulates the accepting run of $T$. A state of $B$ records the current state of $T$; for each register $x$, its $A$-abstraction, the set of pairs $(p, q)$ of states of $A$ such that $A$ can go from $p$ to $q$ reading the word stored in $x$, updated along each transition by composing abstractions; the set of $\varepsilon$-transitions of $T$ taken since the last letter, to forbid repeating one; and the set of states of $T$ reachable by runs of higher priority on the same input, intended to certify that no higher-priority run is accepting. $B$ accepts, by the printed conditions, when the final output $F_T(q)$, abstracted through the registers, leads from $q_{0,A}$ to a final state of $A$. The number of states is exponential in $|T|$ and $|A|$.

Proof obligation. As printed, the final-state conditions of $B$ do not exclude a higher-priority run that is a proper extension by $\varepsilon$-transitions at the end of the input. Example: let $q_0$ have $F(q_0) = a$, a single $\varepsilon$-transition $q_0 \to q_1$, and $F(q_1) = b$, and let $A$ accept only $a$. By the definition, the run $q_0 \to q_1$ has priority over its prefix $q_0$, so $T(\varepsilon) = b \notin L(A)$; but the initial state of $B$, with empty sets of used $\varepsilon$-transitions and higher-priority states, meets the written acceptance conditions, so $B$ accepts $\varepsilon$. The counterexample refutes the printed construction, not the published lemma. An expansion must (i) at acceptance, also rule out accepting $\varepsilon$-only proper extensions of the current run, and (ii) when collecting higher-priority states at a divergence, respect the $\varepsilon$-transitions already used in the current $\varepsilon$-block, and then prove the construction correct.

This lemma is what makes backward propagation of regular constraints possible for string functions defined by PSSTs, such as capture-group extraction and replaceAll under regular-expression semantics.

## Sources

- T. Chen, A. Flores-Lamas, M. Hague, Z. Han, D. Hu, S. Kan, A. W. Lin, P. Rümmer and Z. Wu, "Solving string constraints with Regex-dependent functions through transducers with priorities and variables", Proceedings of the ACM on Programming Languages 6 (POPL), Article 45, 2022, doi:[10.1145/3498707](https://doi.org/10.1145/3498707); long version arXiv:2111.04298v2 (authors listed there as Alejandro Flores Lamas and Philipp Ruemmer), <https://arxiv.org/abs/2111.04298v2>: Definition 5.4 and Lemma 5.5 (statement in Section 5.2), and Appendix A.3 (proof of Lemma 5.5).
