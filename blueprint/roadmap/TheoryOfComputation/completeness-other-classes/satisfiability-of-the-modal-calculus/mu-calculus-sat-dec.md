# Modal μ-calculus satisfiability as a decision problem

Modal μ-calculus satisfiability is the decision problem that accepts a bitstring $x$ exactly when
$x$ decodes, under the canonical bitstring encoding of lists of natural numbers, to a token list
that decodes to a modal μ-calculus formula $\varphi$ with atoms in $\mathbb{N}$ (one token per
connective), and $\varphi$ is closed and [satisfiable](mu-sat.md). Bitstrings that do not decode
in this way are rejected.
