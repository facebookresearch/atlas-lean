# Costed strict truncated comparison

For a threshold $p$ and tuples $a, b$ of $d + 1$ natural numbers (indices $0, \dots, d$, a higher index being more significant), the costed strict truncated comparison is the costed disjunction over all indices $j$ of the costed conjunction of the checks $p \le j$ and $b_j < a_j$ with the costed check, over all indices $i$, that $i \le j$ or $a_i = b_i$. Each atomic comparison costs $1$, and its result says whether $a$ exceeds $b$ in the lexicographic order truncated to the indices at least $p$.

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", Proceedings of STACS 2000, LNCS 1770, 290-301 (background: the paper defines progress measures and the lifting algorithm; the verifier and its comparison counts here are not the paper's algorithm or bound).
