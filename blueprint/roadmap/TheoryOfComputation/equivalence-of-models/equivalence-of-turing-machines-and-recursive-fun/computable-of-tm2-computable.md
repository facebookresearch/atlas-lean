# Turing-computable functions are recursive

Let $f : \mathbb{N} \to \mathbb{N}$ and suppose
that some finite multi-stack Turing machine (finitely many stacks, labels and internal states,
and a finite input alphabet), together with identifications of its input and output stack
alphabets with the booleans, computes $f$ under the binary encoding of natural numbers (least
significant bit first, with $0$ encoded as the empty list): for every $n$, the machine started
at its main label in its initial internal state, with the encoding of $n$ on its input stack and
all other stacks empty, eventually reaches the halted configuration whose output stack holds the
encoding of $f(n)$, whose other stacks are empty and whose internal state is the initial one.
Then $f$ is computable (recursive).
