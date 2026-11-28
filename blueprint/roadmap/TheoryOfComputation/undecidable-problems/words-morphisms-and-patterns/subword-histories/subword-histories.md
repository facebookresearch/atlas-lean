# Subword histories

A subword history over an alphabet is a formal expression built from words by negation, sum and product. Its value in a
word replaces each word $u$ by the number of occurrences of $u$ as a scattered subword and evaluates the arithmetic.

Let $\Sigma$ be a finite alphabet and $\Sigma^*$ the set of words over $\Sigma$, including the empty word $\lambda$. For words
$w = w_1 \cdots w_n$ and $u = u_1 \cdots u_k$, the number $|w|_u$ of occurrences of $u$ as a *scattered subword* of $w$ is the
number of index sequences $1 \le i_1 < \cdots < i_k \le n$ with $w_{i_j} = u_j$ for all $j$; by convention $|w|_\lambda = 1$
for every $w$. For example $|aab|_{ab} = 2$.

*Subword histories* in $\Sigma$ and their values in a word $w \in \Sigma^*$ are defined recursively:

- every word $u \in \Sigma^*$ is a subword history (a *monomial*), with value $|w|_u$ in $w$;
- if $SH_1$ and $SH_2$ are subword histories with values $\alpha_1$ and $\alpha_2$ in $w$, then $-(SH_1)$, $(SH_1) + (SH_2)$
  and $(SH_1) \times (SH_2)$ are subword histories with values $-\alpha_1$, $\alpha_1 + \alpha_2$ and $\alpha_1 \alpha_2$.

The value of $SH$ in $w$ is written $|w|_{SH}$; it is an integer. For an integer $c$ and $e \ge 0$, the expressions
$c(SH)$ and $\prod^e SH$ (the $e$-fold product, with $\prod^0 SH = \lambda$) are again subword histories, with values
$c\,|w|_{SH}$ and $|w|_{SH}^e$. Two subword histories are *equivalent* if they take the same value in every word of
$\Sigma^*$; for instance, for distinct letters $a \ne b$, $a \times b$ and $ab + ba$ are equivalent. A subword history is *letter-restricted* if each of its
monomials is a single letter of $\Sigma$ or $\lambda$.

## Depends on

None.

## Proof depends on

None.

## Expansion

The value of a letter $a$ in $w$ is the number of occurrences of $a$, so letter-restricted subword histories evaluate
integer polynomials at the Parikh vector of $w$; general monomials count scattered occurrences of longer words and see the
order of letters. Mateescu, Salomaa and Yu showed that every subword history is equivalent to a linear one (built without
$\times$), from which equivalence of subword histories is decidable.

## Sources

- S. Seki, "Absoluteness of subword inequality is undecidable", *Theoretical Computer Science* 418:116–120, 2012, doi:[10.1016/j.tcs.2011.10.017](https://doi.org/10.1016/j.tcs.2011.10.017). Numbering of the version read, arXiv:1108.2758v1: Definition 1 (stated after Mateescu, Salomaa and Yu) and Proposition 1, the decidability of equivalence recalled from them in Section 1, and the definitions of equivalence and letter-restricted subword histories in Sections 1 and 2.
