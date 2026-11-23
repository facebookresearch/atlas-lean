# Searching a computable list with a computable test is computable

Let $\gamma$ and
$\beta$ be types with primitive recursive encodings into $\mathbb{N}$, let $l$ be a computable
function sending each $x \in \gamma$ to a finite list $l(x)$ of elements of $\beta$, and let $g$
be a computable Boolean-valued function of $x \in \gamma$ and $b \in \beta$. Then the
Boolean-valued function that sends $x$ to true exactly when $g(x, b)$ is true for some $b$ in
$l(x)$ is computable.

The proof scans the indices of $l(x)$ by primitive recursion.
