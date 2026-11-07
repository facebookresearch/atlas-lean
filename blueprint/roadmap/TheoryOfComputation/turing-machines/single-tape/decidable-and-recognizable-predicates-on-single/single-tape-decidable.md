# Predicates decidable by a single-tape Turing machine

Let $\alpha$ be a type with a
primitive recursive encoding into $\mathbb{N}$. A predicate $p$ on $\alpha$ is decidable by a
single-tape machine when there are a finite, nonempty tape alphabet $\Sigma$, an injective map
$\iota$ from the bits $\{0, 1\}$ to $\Sigma$ and a single-tape Turing machine $M$ over $\Sigma$
such that for every $a \in \alpha$ there is a bit $b$ for which $M$ outputs the one-symbol word
$\iota(b)$ on the input word obtained by writing the binary encoding of the code of $a$ in
$\mathbb{N}$ letter by letter through $\iota$, and $b = 1$ exactly when $p(a)$ holds. Here $M$
outputs a word $w$ on an input when its run from the input halts with exactly $w$ on the tape,
every other cell blank and the head on the first symbol of $w$.
