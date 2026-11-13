# Decidability by multi-tape machines

Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is decidable by a multi-tape machine when there are a number $k$ and a
deterministic Turing machine $M$ with finitely many states, a read-only input tape, $k$ work tapes
and a write-only output tape, all over the Boolean alphabet, such that for every $a \in \alpha$
there is a Boolean $b$ for which $M$ computes the one-letter word $b$ on the binary word of
$\mathrm{encode}(a)$ (least significant bit first), and $b$ is true exactly when $p(a)$ holds.
Here $M$ computes a word $v$ on an input word $w$ when its run started on $w$ halts with $v$ on
its output tape.
