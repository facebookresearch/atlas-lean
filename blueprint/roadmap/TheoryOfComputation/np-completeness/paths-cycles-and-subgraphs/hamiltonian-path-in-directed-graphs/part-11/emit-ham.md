# The HAMPATH emitter

The emitter whose stacks, alphabets, labels, program and start label
are those of the HAMPATH emitter machine, which exits at the machine's label $\mathsf{done}$,
reads the tokens of a CNF formula from stack $T$ and writes its output bits on stack $O$ (both
symbol maps being the identity), and has step bound $B(n) = 2000 (n + 1)^5$ for $n$ tokens. Its
output for a CNF formula $\varphi$ is Sipser's HAMPATH instance of $\varphi$, and for an
undecodable input the fixed HAMPATH no-instance (two vertices, no arcs, source and target $0$).
