# The CLIQUE emitter

The emitter given by the CLIQUE emitter machine, run from its start
label to its exit label, with token stack $T$ and output stack $O$. Its output on a CNF formula
$\varphi$ is Karp's CLIQUE instance of $\varphi$, its output on undecodable input is the string
$100$, and its step bound on $m$ tokens is $8(m + 1)^3$. Let $\varphi$ be a CNF formula with $m$
tokens. Started with the tokens of $\varphi$ on $T$, last token on top, and all other stacks
empty, the machine reaches its exit label within $8(m + 1)^3$ steps, with Karp's CLIQUE instance
of $\varphi$ on $O$, first bit on top.
