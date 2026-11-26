# Instances of NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES

An instance of NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES is a tuple $(|F|, |P|, |X|, S)$ of the numbers of function symbols, predicate symbols and variables (the symbols and variables are $0, \dots, |F| - 1$, $0, \dots, |P| - 1$ and $0, \dots, |X| - 1$) and the instruction list $S = I_1, \dots, I_m$ of the scheme. Each instruction is a tuple of five numbers: $(0, x, f, y, 0)$ for $x \leftarrow f(y)$, $(1, p, x, j, k)$ for "if $p(x)$ then goto $I_j$ else goto $I_k$", and $(2, 0, 0, 0, 0)$ for halt.
