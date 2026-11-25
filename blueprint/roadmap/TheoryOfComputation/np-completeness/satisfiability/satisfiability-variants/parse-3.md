# Modal formula of a postfix token list

Read tokens onto a stack: $0$ pops $\psi, \varphi$ and pushes $\varphi \wedge \psi$; $1$ pushes the negation; $2$ pushes $\Box\varphi$; $k + 3$ pushes the variable $u_k$. The result is the single remaining formula, or nothing on a missing operand or a leftover stack.
