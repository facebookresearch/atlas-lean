# A predicate decided by a single-tape machine is computable

Let $\alpha$ be a type with a primitive recursive encoding into $\mathbb{N}$, and let $p$ be a
predicate on $\alpha$ that is decidable by a single-tape Turing machine: for some nonempty finite
alphabet $\Sigma$, injective map $\iota : \{0, 1\} \to \Sigma$ and single-tape machine $M$ over
$\Sigma$, on the input word obtained by applying $\iota$ to the binary expansion of the code of each
$a \in \alpha$, $M$ halts with the one-symbol output $\iota(b)$, where $b = 1$ exactly when $p(a)$
holds. Then $p$ is computable.

The decider's answer is the symbol under the head of its final tape.
