# The output phase of the HAMPATH emitter

Let $s$ be a quiescent state of the emitter
whose variable stack $V$ is empty, with clause count $C = c$, diamond-top counter $P = p$, edge
bits $q$ and output stack $o$. Then for every internal bit $v$ there are an internal bit $v'$ and
stacks $S'$ such that the emitter goes in exactly $|q| + 4p + 2c + 11$ steps from label
$\mathsf{h0}$ with bit $v$ and the stacks of $s$ to label $\mathsf{done}$ with bit $v'$ and stacks
$S'$, and the output stack of $S'$ is $1^c 0 1^p 0 1^{p+1} 0$ followed by $q$ and then $o$.
