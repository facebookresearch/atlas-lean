# Recognizability by multi-stack machines

Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is recognizable by a multi-stack machine when there are a multi-stack
Turing machine $M$ and an identification of its input alphabet with the Booleans such that for
every $a \in \alpha$, $p(a)$ holds if and only if $M$ halts when started on the binary word of
$\mathrm{encode}(a)$.
