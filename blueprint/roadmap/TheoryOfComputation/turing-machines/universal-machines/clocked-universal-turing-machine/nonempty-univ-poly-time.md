# The clocked universal function is polynomial-time computable

There are a multi-stack
Turing machine with finitely many stacks, labels and internal states, whose input and output
alphabets are in bijection with the bits, and a polynomial $p$ with natural-number coefficients,
such that for every code $c$, list of bits $x$ and clock $T \in \mathbb{N}$ the following holds.
Let $n$ be the length of the input encoding of $(c, x, T)$. Started at its main label in its
initial internal state, with the input encoding of $(c, x, T)$ on its input stack and every other
stack empty, the machine halts within $p(n)$ steps, with its internal state again the initial
one, the output encoding of the result of the clocked evaluator on $c$, $x$ and $T$ on its output
stack, and every other stack empty; both encodings are translated letter by letter through the
inverses of the bijections.

In the proof, $p$ has degree $2$: the clocked universal machine itself takes at most
$18 (n + 1)^2$ steps, and running it as a component of the reduction host keeps the degree.
