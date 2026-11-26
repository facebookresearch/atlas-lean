# LTL formula of a postfix token list

Read tokens onto a stack: $0$ pops $g, f$ and pushes $f \wedge g$; $1$ pushes the negation; $2$ pushes $\mathbf{F} f$; $k + 3$ pushes the atomic proposition $P_k$. The result is the single remaining formula, or nothing on a missing operand or a leftover stack.
