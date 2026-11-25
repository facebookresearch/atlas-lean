# MV-term of a postfix token list

Read tokens onto a stack: $0$ pushes the negation; a binary code pops two terms and pushes their combination; $6$ and $7$ push the constants $0$ and $1$; $k + 8$ pushes $x_k$. The result is the single remaining term, or nothing on a missing operand or a leftover stack.
