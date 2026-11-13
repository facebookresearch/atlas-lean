# EQ_REX is decidable

Let $\alpha$ be a finite alphabet with a primitive recursive
encoding. Then equivalence of encoded regular expressions over $\alpha$ is decidable by a
multi-stack machine: some multi-stack machine decides, for a pair $(e_1, e_2)$ of encoded
regular expressions over $\alpha$, whether the regular expressions that $e_1$ and $e_2$ denote
have the same language.

This is the regular-expression analogue of Sipser, Theorem 4.5 (EQ_DFA). It is proved by
bounded search: the membership decider is run on both expressions for every word shorter than
a bound computed from them, and the answers are compared.
