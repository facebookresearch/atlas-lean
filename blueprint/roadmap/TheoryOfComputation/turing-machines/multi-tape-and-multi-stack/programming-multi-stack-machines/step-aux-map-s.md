# Executing a translated statement

Let $E$ be a stack embedding with stack renaming $e$, and
let $\varphi$ map sub-machine labels to host labels. Let $q$ be a sub-machine statement, $v$ a
state, $S$ sub-machine stacks and $S'$ host stacks that agree with $S$. Let executing $q$ from
state $v$ and stacks $S$ yield the next label $\ell$ (possibly none), state $w$ and stacks $T$.
Then there are host stacks $T'$ such that executing the translation of $q$ along $E$ and
$\varphi$ from state $v$ and stacks $S'$ yields the next label $\varphi(\ell)$ (none if $\ell$ is
none), state $w$ and stacks $T'$. Moreover $T'$ agrees with $T$, and $S'$, $T'$ satisfy the frame
condition.
