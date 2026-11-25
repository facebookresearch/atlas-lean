# The diagonal language

For $f : \mathbb{N} \to \mathbb{N}$, the diagonal language of $f$
holds at a bit list $x$ iff $x$ encodes a code $c$ and the clocked evaluator, running $c$ on $x$
for at most $f(|x|)$ steps, does not return the output $[2]$, the symbol of the answer true:
either $c$ does not halt on $x$ within $f(|x|)$ steps, or it halts with another output. Bit lists
that encode no code are not in the language. This is the diagonal language of the proof of
Sipser's Theorem 9.10.
