# Literals of a clause kind at given positions

Let $c$ be a clause kind with $n$ literals
($n = 3$ for an in-range shift clause, $n = 2$ for an overflow-fill or pushed-fill clause) and let
$\mathrm{pos} : \mathbb{N} \to \mathbb{N}$. The literals of $c$ at positions $\mathrm{pos}$ are the
list $(\mathrm{pos}(0), b_0), \dots, (\mathrm{pos}(n - 1), b_{n - 1})$ of variable-sign pairs,
where the sign $b_l$ is true (a positive literal) exactly when $l = n - 1$.
