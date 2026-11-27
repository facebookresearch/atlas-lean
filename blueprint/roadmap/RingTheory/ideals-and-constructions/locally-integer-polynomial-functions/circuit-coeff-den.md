# Denominator of the top coefficient on a circuit

Let $f : \mathbb{Z} \to \mathbb{Z}$, and
for a finite set $Y \subseteq \mathbb{Z}$ write $f_Y \in \mathbb{Q}[x]$ for the interpolation
polynomial of $f$ on $Y$. Let $X \subseteq \mathbb{Z}$ be a finite circuit for $f$: $f_X$ does not
have integer coefficients, but $f_{X \setminus \{a\}}$ has integer coefficients for every
$a \in X$. Let $c$ be the coefficient of $x^{|X|-1}$ in $f_X$ and let $q \ge 1$ be the denominator
of $c$ in lowest terms. Then $q \ne 1$, so $c$ is not an integer, and $q$ divides $a - b$ for all
$a, b \in X$.

## Sources

- Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025), Article A41, Lemma 7, with the circuit definition preceding it.
