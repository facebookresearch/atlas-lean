# Regular languages are preserved under forward sequential transduction

A sequential transducer $S$ with state set $Q$, input alphabet $\Sigma$ and output alphabet $\Gamma$ consists of a step function $Q \times \Sigma \to Q \times \Gamma^*$ (successor state and emitted output word), a start state $q_0$, a set $F \subseteq Q$ of accepting states, an initial output word $u \in \Gamma^*$ and a final output function $f : Q \to \Gamma^*$. It translates an input word $x \in \Sigma^*$ into $y \in \Gamma^*$ when the run from $q_0$ on $x$ ends in a state $q \in F$ and

$$y = u \cdot v \cdot f(q),$$

where $v$ is the concatenation of the output words emitted along the run.

Statement: let $Q$ and $\Sigma$ be finite and $\Gamma$ arbitrary. For every regular language $L \subseteq \Sigma^*$, the image

$$\{\, y \in \Gamma^* : \exists x \in L,\ S \text{ translates } x \text{ into } y \,\}$$

is a regular language over $\Gamma$.

The finiteness of the input alphabet is needed: without it, for any nonregular $K \subseteq \Gamma^*$ the one-state transducer on the input alphabet $K$ that emits each letter's underlying word maps the regular language of one-letter words onto $K$.

## Sources

- J. Berstel, Transductions and Context-Free Languages, 1979, Chapter II, Theorem 2.1.
- J. Sakarovitch, Elements of Automata Theory, 2009, Chapter IV, Proposition IV.2.5.
