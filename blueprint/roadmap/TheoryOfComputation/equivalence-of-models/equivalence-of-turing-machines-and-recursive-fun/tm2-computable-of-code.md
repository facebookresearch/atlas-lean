# The wrapped machine computes the function a code evaluates

Let $c$ be a code and
$f : \mathbb{N} \to \mathbb{N}$ a function such that, for every $n$, evaluating $c$ on the
one-element list $[n]$ returns $[f(n)]$. Then the wrapped machine of $c$, with input and output
alphabet the booleans, computes $f$ under the binary encoding of natural numbers (least
significant bit first): for every $n$, started with the encoding of $n$ on its input stack and
all other stacks empty, it eventually halts in its initial internal state with the encoding of
$f(n)$ on its output stack and all other stacks empty.
