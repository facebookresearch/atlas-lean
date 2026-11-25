# Simulation up to a state relabelling

Let $M$ and $M'$ be deterministic machines with $k$
work tapes over the same alphabet, with state sets $Q$ and $Q'$, and let $f : Q \to Q'$. Then $M'$
simulates $M$ up to the relabelling $f$ when the initial state of $M'$ is $f(q_0)$, where $q_0$ is
the initial state of $M$, and for every state $q \in Q$, every possibly blank symbol $a$ under the
input head and every tuple $w$ of possibly blank symbols under the work heads, the action of $M'$
in state $f(q)$ reading $a$ and $w$ is the action of $M$ in state $q$ reading $a$ and $w$ with its
successor state relabelled by $f$ (a successor state $q'$ becomes $f(q')$, and halting stays
halting).

Nothing is required of $M'$ in states outside the range of $f$, and $f$ need not be injective.
