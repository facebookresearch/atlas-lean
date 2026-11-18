# Valid gates of a succinct 3SAT descriptor

Let $C$ be a list of gates encoded as
(kind, references) pairs and let $n$ and $j$ be natural numbers. Gate $j$ of $C$ is valid when
$C$ has more than $j$ entries and its entry $j$ (counting from $0$) is one of: $(0, [i])$ with
$i < n + 2$ (an input gate); $(1, [b])$ with $b \le 1$ (a constant gate); $(2, [a])$ with
$a < j$ (a negation gate); or $(3, r)$ or $(4, r)$ where every entry $a$ of $r$ satisfies
$a < j$ (a conjunction or disjunction gate). Every other entry is invalid.
