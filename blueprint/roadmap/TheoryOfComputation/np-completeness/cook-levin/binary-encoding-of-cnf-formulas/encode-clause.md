# Length-prefixed binary code of a clause

Writing $1$ for true and $0$ for false, the code
of a clause $C = (\ell_1, \dots, \ell_k)$ is $1^k 0$ ($k$ ones followed by a zero) followed by the
binary codes of $\ell_1, \dots, \ell_k$ in order, where a literal $(x, b)$ with variable index $x$
and polarity $b$ is coded by the prefix-free code of $x$ followed by the bit $b$.
