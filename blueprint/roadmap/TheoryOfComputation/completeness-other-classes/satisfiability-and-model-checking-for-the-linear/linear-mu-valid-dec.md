# Linear μ-calculus validity as a decision problem

Linear μ-calculus validity is the decision problem that accepts a bitstring $x$ exactly when $x$
decodes, under the canonical bitstring encoding of lists of natural numbers, to a token list that
decodes to a linear μ-calculus formula $\varphi$ with atoms in $\mathbb{N}$ (one token per
connective), and $\varphi$ is closed and [valid](linear-mu-valid.md). Bitstrings that do not
decode in this way are rejected.
