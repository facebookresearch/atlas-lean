# Instances of AC-MATCHING

An instance of AC-MATCHING is a tuple $(a, A, m, s, t)$: a list $a$ of arities of the function symbols, a list $A$ of indices of the symbols declared associative-commutative, the number $m$ of pattern variables, and the token lists of the pattern $s$ and of the subject $t$.

These are raw data: the arities and the AC indices are natural lists, $m$ is a natural number, and the two token lists need not parse, may refer to undeclared symbols and may be empty. AC-UNIFICATION uses the same tuples. That the subject $t$ represents a ground term is required only by AC-MATCHING's validation; neither raw type requires it.
