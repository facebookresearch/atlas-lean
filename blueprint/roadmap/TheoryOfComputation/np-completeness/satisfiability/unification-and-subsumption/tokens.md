# Token list of a term

For a map $f$ from the variables of a term to natural numbers, the token list of the term is its prefix encoding with the token $(0, f(v))$ for each occurrence of a variable $v$ and $(1, s)$ for each function symbol $s$. Variables enter only through $f$, so a non-injective $f$ can give different variables the same token; the instances use $f$ equal to the numbering of the variables $0, \dots, v - 1$.
