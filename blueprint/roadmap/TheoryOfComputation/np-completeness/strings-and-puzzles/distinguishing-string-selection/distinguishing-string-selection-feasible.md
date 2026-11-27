# Feasible DISTINGUISHING STRING SELECTION instances

A witness $t$ that is itself a [word](is-word.md) of length $L$ over the alphabet $\{0, \dots, q-1\}$, within Hamming distance $k_b$ of every bad input row and at Hamming distance at least $k_g$ from every good input row. Each input row is compared on its first $L$ positions only, with missing positions read as $0$ ([as-word](as-word.md)): at $q = L = 1$ the empty bad row is at distance zero from $[0]$. Raw feasibility does not reject input rows of unequal lengths.
