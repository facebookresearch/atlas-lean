# First copy loop of the composite machine

Consider the composite program of machines $M_1$
and $M_2$ with symbol translation $\varphi$. Suppose it is at the label that pops $M_1$'s output
stack, with state $(v_1, v_2, o)$, with $M_1$'s stacks holding $S_1$, $M_2$'s stacks holding $S_2$,
the scratch stack holding $t$, and $M_1$'s output stack holding the list $y$. Then after exactly
$2|y| + 1$ steps it is at the label that pops the scratch stack, with state
$(v_1, v_2, \mathrm{none})$, $M_1$'s output stack empty and its other stacks unchanged, $M_2$'s
stacks still $S_2$, and the scratch stack holding the reverse of the list obtained by applying
$\varphi$ to each symbol of $y$, followed by $t$.
