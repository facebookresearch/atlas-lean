# Polynomial-time conversion from the separator form to the canonical pair encoding

The identity map on pairs $(x, w)$ of bit strings is computable in polynomial time by the [converter to the
canonical pair encoding](tm.md), from the verifier's separator form $x \# w$ (the bits of $x$ tagged left, the
separator, then the bits of $w$ tagged right, over the verifier's alphabet) to the canonical bit-string encoding
of $(x, w)$ (each bit $b$ of $x$ written as $1, 1, 1, b, 1, 0$, then a single $0$, then each bit $b$ of $w$
written as $1, b, 0$), with time bound $2n + 3$. Here the input alphabet is the verifier's alphabet, the output
alphabet is the bits, and $n = |x| + |w| + 1$ is the length of $x \# w$: started on $x \# w$, the converter halts
after exactly $2|x| + 2|w| + 5 = 2n + 3$ steps with the canonical encoding of $(x, w)$ on its output stack.
