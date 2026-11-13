# The SAT-to-3SAT emitter

The emitter whose stacks, stack alphabets, labels, program, start
label and exit label are those of the 3SAT emitter machine, with that machine's token stack as its
token stack and its bit-valued output stack as its output stack. Its output on a CNF formula
$\varphi$ is the binary encoding of the SAT-to-3SAT translation of $\varphi$, its output on a bit
string that encodes no CNF formula is the empty bit string, and its step bound is
$B(n) = 8(n+1)^2$: started at its start label with the reversed token sequence of $\varphi$ on the
token stack and every other stack empty, it reaches its exit label within $B(n)$ steps, where $n$
is the number of tokens of $\varphi$, with the output for $\varphi$ on the output stack.
