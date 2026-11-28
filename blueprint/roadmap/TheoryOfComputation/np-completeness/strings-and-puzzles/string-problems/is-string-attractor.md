# String attractors

A set $\Gamma$ of natural numbers is a string attractor of a text $T$ when every element of $\Gamma$ is a position of $T$, below its length $|T|$, and for all $i \le j < |T|$ there are $i' \le j' < |T|$ with $T[i'..j'] = T[i..j]$ and some element of $\Gamma$ in $[i', j']$. Only nonempty, in-bounds substrings are tested, so the empty set is a string attractor of the empty text.

## Sources

- D. Kempa and N. Prezza, "At the roots of dictionary compression: string attractors", Proceedings of the 50th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2018), arXiv:1710.10964, Definition 3.1.
