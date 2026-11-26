# Bounding variable images by the target loses no pattern matches

Let $\alpha$ be an alphabet, $n \in \mathbb{N}$, and let the variables be $x_0, \dots, x_{n-1}$; a pattern is a finite word over $\alpha \cup \{x_0, \dots, x_{n-1}\}$, and for a substitution $\sigma$ of words over $\alpha$ for the variables, $\sigma(w)$ is the word obtained from a pattern $w$ by replacing each $x_i$ by $\sigma(x_i)$. For every pattern $w$ and every word $t$ over $\alpha$, there is a substitution $\sigma$ with
$\sigma(w) = t$ if and only if there is such a substitution with moreover $|\sigma(x_i)| \le |t|$ for all
$i < n$.

A solution need not obey the bound on variables not occurring in $w$; sending those to the empty word gives
one that does.
