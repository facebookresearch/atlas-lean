# Second copy loop of the composite machine

Consider the composite program of finite multi-stack Turing machines $M_1$ and $M_2$ with symbol
translation $\varphi$, whose internal states are triples $(v_1, v_2, o)$ with $o$ a symbol of
$M_2$'s input alphabet or the empty value $\bot$. Suppose it is at the label that pops the scratch
stack, with state $(v_1, v_2, o)$, with $M_1$'s stacks holding $S_1$, $M_2$'s stacks holding
$S_2$, and the scratch stack holding the list $t$. Then after exactly $2|t| + 1$ steps it is at
the copy of the main label of $M_2$, with state $(v_1, v_2, \bot)$, $M_1$'s stacks still $S_1$,
$M_2$'s input stack holding the reverse of $t$ followed by its previous contents, $M_2$'s other
stacks unchanged, and the scratch stack empty.
