# LTL satisfiability as a decision problem

LTL satisfiability is the decision problem that accepts a bitstring $x$ exactly when $x$ decodes,
under the canonical bitstring encoding of lists of natural numbers, to a token list that decodes
to an LTL formula $\varphi$ with atoms in $\mathbb{N}$, and some infinite word over the alphabet
of sets of atoms satisfies $\varphi$, an atom $a$ holding at a letter $s$ when $a \in s$.
Bitstrings that do not decode in this way are rejected.
