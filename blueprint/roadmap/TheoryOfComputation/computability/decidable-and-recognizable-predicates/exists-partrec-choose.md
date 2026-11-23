# Selection for r.e. relations

Let $\alpha$ and $\beta$ be types with primitive recursive
encodings into $\mathbb{N}$, and let $R$ be a relation between $\alpha$ and $\beta$ that is
recursively enumerable as a predicate on pairs $(a, b)$. Then there is a partial recursive
function $g$ from $\alpha$ to $\beta$ such that, for every $a \in \alpha$, if $g(a)$ is defined
then its value $b$ satisfies $R(a, b)$, and $g(a)$ is defined whenever some $b \in \beta$
satisfies $R(a, b)$.

The proof searches over pairs of a candidate $b$ and a step bound by dovetailing with the
step-bounded simulation of the semi-decision procedure for $R$.
