# Decidability by multi-stack machines

Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is decidable by a multi-stack machine when there is a function
$f : \mathbb{N} \to \mathbb{N}$ computed by a multi-stack Turing machine, with input and output
numbers written in binary, such that for every $a \in \alpha$, $f(\mathrm{encode}(a)) = 1$ if and
only if $p(a)$.
