# Recognizability by multi-tape machines

Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is recognizable by a multi-tape machine when there are a number $k$ and
a deterministic Turing machine $M$ with finitely many states, a read-only input tape, $k$ work
tapes and a write-only output tape, all over the Boolean alphabet, such that for every
$a \in \alpha$, the run of $M$ started on the binary word of $\mathrm{encode}(a)$ (least
significant bit first) halts if and only if $p(a)$ holds.
