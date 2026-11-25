# Infiniteness test for encoded regular expressions

Let $e$ be an encoded regular
expression with nodes $n_0, \dots, n_{m-1}$, and let $f_0, \dots, f_{m-1}$ be the flags of all
nodes of $e$, the triples of Booleans computed in one left-to-right pass over the nodes. The
infiniteness test of $e$ is the third component of $f_{m-1}$, the flag triple of the last node
(the root); when $e$ has no nodes it is false.

The three flags of a node say whether its language is nonempty, contains a nonempty word and is
infinite, so the test returns true exactly when the language of $e$ is infinite.
