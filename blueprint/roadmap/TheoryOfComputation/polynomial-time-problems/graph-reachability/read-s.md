# The unary read instruction

Given a stack $d$, an encoding $g$ of bits as symbols of $d$,
a list $ps$ of stack–symbol pairs and labels $\ell$ and $\ell'$, the instruction of the marking
machine that jumps to `bad` if $X$ is empty, and otherwise pops the top of $X$ as a bit $b$ (a
symbol that is not a bit counts as false) and pushes $g(b)$ on $d$; then, if $b$ is true, it
pushes $a$ on $q$ for each pair $(q, a)$ of $ps$, in order, and jumps to $\ell$, and if $b$ is
false it jumps to $\ell'$. Run at its own label $\ell$, it reads a unary number off $X$.
