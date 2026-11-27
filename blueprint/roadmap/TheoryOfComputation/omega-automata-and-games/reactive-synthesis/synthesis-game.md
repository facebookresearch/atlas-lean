# The synthesis parity game of a specification

Let $(q_0, \delta, \Omega)$ be a deterministic parity specification over states $Q$, inputs $I$ and outputs $O$, with $I$ and $O$ nonempty. Its synthesis parity game has positions $Q \sqcup (Q \times I)$:

- a position $q \in Q$ belongs to the odd player (the environment), who moves to any $(q, i)$ with $i \in I$;
- a position $(q, i)$ belongs to the even player (the controller), who moves to any $\delta(q, i, o)$ with $o \in O$;
- there are no other moves;
- both $q$ and $(q, i)$ have priority $\Omega(q)$.

Every position has a move because $I$ and $O$ are nonempty. Plays are won under the max-parity condition: the even player wins a play when the largest priority occurring infinitely often is even.
