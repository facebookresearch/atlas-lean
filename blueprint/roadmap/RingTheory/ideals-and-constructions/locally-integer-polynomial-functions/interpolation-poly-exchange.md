# Exchange formula for interpolation polynomials

Let $f : \mathbb{Z} \to \mathbb{Z}$, and for
a finite set $Y \subseteq \mathbb{Z}$ write $f_Y \in \mathbb{Q}[x]$ for the interpolation polynomial
of $f$ on $Y$. Let $X \subseteq \mathbb{Z}$ be finite and $a, b \in \mathbb{Z} \setminus X$, and let
$c$ be the coefficient of $x^{|X|+1}$ in $f_{X \cup \{a, b\}}$. Then

$$f_{X \cup \{a\}} = f_{X \cup \{b\}} + c\,(a - b) \prod_{z \in X} (x - z).$$

## Sources

- Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025), Article A41, Lemma 6 (`integers-2025-A41-lem-6`).
