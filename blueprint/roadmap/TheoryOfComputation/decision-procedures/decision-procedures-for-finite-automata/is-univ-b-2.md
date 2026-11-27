# Universality test for encoded DFAs

For an encoded DFA $D$ over an alphabet $\alpha$ with
decidable equality, the universality test is the Boolean that is true exactly when every entry of
the list of reachable states of $D$ is in the accepting list of $D$.

It returns true exactly when the language of $D$ contains every word over $\alpha$.
