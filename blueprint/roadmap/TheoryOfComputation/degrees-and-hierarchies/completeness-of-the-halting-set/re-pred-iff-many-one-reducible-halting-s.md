# A predicate is recognizable iff it many-one reduces to the halting set

Let $\alpha$ be a
type with a primitive recursive encoding into $\mathbb{N}$ and let $p$ be a predicate on $\alpha$.
Here the halting set is the set of $n \in \mathbb{N}$ such that the partial recursive function
with code number $n$ halts on input $0$. Then $p$ is recognizable (recursively enumerable: the
domain of a partial computable function on $\alpha$) if and only if there is a computable function
$f : \alpha \to \mathbb{N}$ such that for every $a \in \alpha$, $p(a)$ holds if and only if $f(a)$
lies in the halting set.
