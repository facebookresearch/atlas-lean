# Every recognizable predicate one-one reduces to the halting set

Let $\alpha$ be a type
with a primitive recursive encoding into $\mathbb{N}$, and let $p$ be a recognizable (recursively
enumerable) predicate on $\alpha$, that is, the domain of a partial computable function on
$\alpha$. Here the halting set is the set of $n \in \mathbb{N}$ such that the partial recursive
function with code number $n$ halts on input $0$. Then there is an injective computable function
$f : \alpha \to \mathbb{N}$ such that for every $a \in \alpha$, $p(a)$ holds if and only if $f(a)$
lies in the halting set.

The proof takes for $f(a)$ the number of the code that ignores its input and runs a code for $p$
on the number encoding $a$; distinct $a$ give distinct codes.
