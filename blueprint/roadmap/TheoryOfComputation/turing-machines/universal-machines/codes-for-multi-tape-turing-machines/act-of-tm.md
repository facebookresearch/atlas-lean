# The code of a machine takes its coded actions

Let $M$ be a binary multi-tape machine
with $k$ work tapes and a finite set of states $Q$, and let $e : Q \to \mathbb{N}$ be injective.
For every state $q \in Q$, every symbol $a$ under the input head and every tuple $w$ of symbols
under the $k$ work heads (each a bit or blank), the coded action of the code of $M$ under $e$ at
state $e(q)$ and symbols $a$, $w$ is the coding, with successor states numbered by $e$, of the
action of $M$ in state $q$ on $a$ and $w$.
