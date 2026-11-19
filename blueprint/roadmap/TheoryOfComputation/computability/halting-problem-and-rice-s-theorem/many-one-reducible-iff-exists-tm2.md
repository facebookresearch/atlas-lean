# Mapping reductions are computed by multi-stack machines

Let $p$ and $q$ be predicates on
primitive recursively encodable types $\alpha$ and $\beta$, and write $\langle x \rangle \in
\mathbb{N}$ for the code of $x$. Then $p$ is many-one reducible to $q$ if and only if there is a
function $f : \alpha \to \beta$ with $p(a) \iff q(f(a))$ for all $a \in \alpha$, together with a
function $F : \mathbb{N} \to \mathbb{N}$ that a multi-stack machine computes on binary
representations and that satisfies $F(\langle a \rangle) = \langle f(a) \rangle$ for all
$a \in \alpha$.
