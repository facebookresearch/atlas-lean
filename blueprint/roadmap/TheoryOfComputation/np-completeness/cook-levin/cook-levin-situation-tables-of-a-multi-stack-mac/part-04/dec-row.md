# C1 decoder (decoding a row)

Let $E$ be an encoding of a machine $M$, let
$H, n \in \mathbb{N}$, and let $w : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$. The decoded
configuration has the label and the state that the inverse (label, state) numbering of $E$
assigns to $n$. For each stack $k$ of $M$, with stack number $\kappa$, the decoded stack $k$
lists, from the top, the symbols of stack $k$ with codes $w(\kappa, 0), w(\kappa, 1), \dots$,
stopping before the first $j$ at which $w(\kappa, j)$ is $0$ or is not a valid code of stack
$k$, and taking at most $H$ symbols. The valid codes of stack $k$ are $1, \dots, s$, where $s$ is
the size of its effective alphabet, and code $i + 1$ stands for symbol number $i$ of that
alphabet, counting from $0$.
