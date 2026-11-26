# The SAT-to-3SAT emitter writes the encoded translation in quadratic time

Let $\varphi$ be
a CNF formula, $o$ a list of bits and $T$ the token sequence of $\varphi$. Start the emitter
machine at its start label, with any internal state, with the token stack holding $T$ reversed
(so that the first token of $T$ is at the bottom), the output stack holding $o$, and every other
stack empty. Then after at most $8(|T| + 1)^2$ steps the machine reaches its label
$\mathrm{done}$, with some internal state and stack contents in which the output stack, read from
the top, holds the binary code of the SAT-to-3SAT translation of $\varphi$ followed by $o$.
