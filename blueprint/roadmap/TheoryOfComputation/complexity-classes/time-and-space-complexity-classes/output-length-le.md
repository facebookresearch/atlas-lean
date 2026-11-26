# Polynomial-time machines have polynomially bounded output

Let $e_\alpha$ and $e_\beta$ encode the elements of sets $\alpha$ and $\beta$ as words over finite
alphabets, and let $M$ be a multi-stack Turing machine that computes a map $f : \alpha \to \beta$
with respect to these encodings within $p(|e_\alpha(a)|)$ steps on every input $a$, for a polynomial
$p$ with natural-number coefficients. Let $c$ be the total number of push instructions in the
statements of $M$, summed over its labels. Then for every $a \in \alpha$,

$$
|e_\beta(f(a))| \le |e_\alpha(a)| + c \cdot p(|e_\alpha(a)|).
$$
