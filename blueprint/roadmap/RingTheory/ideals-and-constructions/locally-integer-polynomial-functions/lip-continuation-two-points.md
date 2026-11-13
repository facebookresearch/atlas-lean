# LIP continuation at two points

Let $f : \mathbb{Z} \to \mathbb{Z}$, and for a finite set
$Y \subseteq \mathbb{Z}$ write $f_Y \in \mathbb{Q}[x]$ for the interpolation polynomial of $f$ on
$Y$. For $S \subseteq \mathbb{Z}$ write $\mathrm{LIP}(S)$ for the ring of locally integer
polynomial functions on $S$: the functions $S \to \mathbb{Z}$ whose restriction to every finite
subset of $S$ agrees with a polynomial with integer coefficients. Let $X \subseteq \mathbb{Z}$ be
finite and $a, b \in \mathbb{Z}$ such that $f_{X \cup \{a, b\}}$ does not have integer
coefficients, while $f_{X \cup \{a\}}$ and $f_{X \cup \{b\}}$ both do (this forces $a \ne b$ and
$a, b \notin X$). Put $V = \{x \in \mathbb{Z} : \gcd(x - a, a - b) = 1\}$. Then $|a - b| \ge 2$,
and there is a function $g : \mathbb{Z} \to \mathbb{Z}$ with $g(x) = f(x)$ for all
$x \in X \cup \{a, b\}$ whose restriction to $X \cup V \cup \{a\}$ lies in
$\mathrm{LIP}(X \cup V \cup \{a\})$ and whose restriction to $X \cup V \cup \{b\}$ lies in
$\mathrm{LIP}(X \cup V \cup \{b\})$.

This is the form of Theorem 8 established in its proof in the source.

## Sources

- Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025), Article A41, Theorem 8.
