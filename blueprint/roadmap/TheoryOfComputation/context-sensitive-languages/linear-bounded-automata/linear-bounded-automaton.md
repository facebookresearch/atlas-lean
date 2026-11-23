# Linear bounded automaton

Let $Q$ and $\Gamma$ be sets. A linear bounded automaton with state set $Q$ and tape alphabet $\Gamma$
consists of an initial state $q_0 \in Q$, an accepting state $q_{\mathrm{acc}} \in Q$, and a transition
function $\delta$ that assigns to each state $q$, each tape symbol $x$ (a letter of $\Gamma$ or the blank)
and each boundary tag $\beta$ (middle, left, right or both) a finite set $\delta(q, x, \beta)$ of triples
$(q', x', d)$ of a next state, a symbol to write (a letter or the blank) and a head move (left, stay or
right).

It is a nondeterministic Turing machine whose tape is the input word: the boundary tag of the head
position lets it detect the ends of its tape, and a move that would take the head off the tape is not a
step.
