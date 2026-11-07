# Context-sensitive grammar

A grammar is context-sensitive when every production has a
nonterminal on its left side (so the left side is nonempty and not
terminal-only) and no production shrinks. The standard `S → ε`
exception is not used here: the `aⁿbⁿcⁿ` grammar has `n ≥ 1`.
