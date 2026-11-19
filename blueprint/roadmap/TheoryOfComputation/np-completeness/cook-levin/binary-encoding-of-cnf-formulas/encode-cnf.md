# Length-prefixed binary code of a CNF formula

Writing $1$ for true and $0$ for false, the
code of a CNF formula $\varphi = (C_1, \dots, C_m)$ is $1^m 0$ ($m$ ones followed by a zero)
followed by the length-prefixed binary codes of the clauses $C_1, \dots, C_m$ in order.
