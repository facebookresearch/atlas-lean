# The 3-COLOR emitter machine

The TM2 program, with the stacks, stack alphabets and
labels of the emitter and a Boolean local state, that builds the 3-COLOR instance of a CNF
formula from its token stack. It first pushes the palette triangle on the output stack and
adds $3$ to the next free vertex $N$. It then reads the clauses one at a time. For each
literal occurrence it pushes the occurrence triangle, walks the earlier occurrences comparing
variable names, and for each one with the same variable pushes the consistency edges for
equal or opposite polarity; it then records the occurrence. After the first literal of a
clause it adds $N$ to the current OR output $R$ and adds $2$ to $N$; after a later literal it
pushes an OR gadget with inputs $N$ and $R$, sets $R$ to $N + 4$ and adds $5$ to $N$. At the
end of a clause it joins $R$ to the vertices $1$ and $2$ and clears $R$; an empty clause gets
the vertex $N$ joined to $0$, $1$ and $2$, and $N$ is increased by $1$. When the tokens run
out it pushes the vertex count $N$ and halts. Apart from the palette, every edge is pushed by
copy sites, each of which pushes a constant block of bits and then the value of a counter in
ones, restoring the counter through a scratch stack.
