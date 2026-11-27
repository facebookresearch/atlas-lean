# Church's synthesis problem: realizability via parity games

Statement: let $Q$, $I$, $O$ be finite types with $I$ and $O$ nonempty, and let $(q_0, \delta, \Omega)$ be a deterministic parity specification over states $Q$, inputs $I$ and outputs $O$. Then there is a transducer $T : I^* \to O$ realizing the specification (for every input word, the run on the input word paired with the outputs $T(w(0), \dots, w(k))$ satisfies the even max-parity condition) if and only if the initial state $q_0$, as a position of the environment in the synthesis parity game of the specification, lies in the winning region of the even player, the set of positions from which the even player has a winning positional strategy.

The transducer $T$ ranges over all functions from finite input words to output letters, not only finite-state ones.

## Sources

- A. Church, "Logic, arithmetic, and automata", Proceedings of the International Congress of Mathematicians 1962, 23-35 (the synthesis problem).
- J. R. Büchi and L. H. Landweber, "Solving sequential conditions by finite-state strategies", Transactions of the AMS 138 (1969), 295-311 (decidability via parity games).
