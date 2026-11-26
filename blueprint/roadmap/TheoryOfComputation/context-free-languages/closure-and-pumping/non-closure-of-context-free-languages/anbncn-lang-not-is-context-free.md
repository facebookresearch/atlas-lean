# The language $a^n b^n c^n$ is not context-free

Over the three-letter alphabet $\{a, b, c\}$
(the letters $0, 1, 2$), the language of the words $a^n b^n c^n$ for $n \in \mathbb{N}$ is not
context-free.

Proof idea: by the pumping lemma, pumping $a^n b^n c^n$ down would keep the three letter counts
equal, so the pumped factor has equal counts of all letters, but a short factor misses $a$ or $c$,
forcing the factor to be empty.
