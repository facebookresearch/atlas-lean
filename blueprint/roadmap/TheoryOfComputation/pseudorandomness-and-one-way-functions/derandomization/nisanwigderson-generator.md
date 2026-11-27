# Nisan–Wigderson generator

Let $S_1, \dots, S_m \subseteq \{1, \dots, \ell\}$ be an $(\ell, n, a)$-design and let $f : \{0,1\}^n \to \{0,1\}$ be such that every circuit of size at most $s$ agrees with $f$ on at most a $\tfrac12 + \tfrac{\varepsilon}{m}$ fraction of inputs. Define $\mathrm{NW}^f : \{0,1\}^\ell \to \{0,1\}^m$ by $\mathrm{NW}^f(z) = (f(z|_{S_1}), \dots, f(z|_{S_m}))$, where $z|_{S}$ is the restriction of $z$ to the coordinates in $S$. Then every circuit of size at most $s - c\, m\, a\, 2^{a}$, for an absolute constant $c$, distinguishes $\mathrm{NW}^f(U_\ell)$ from $U_m$ with advantage at most $\varepsilon$.

## Depends on

- [Combinatorial designs for the Nisan–Wigderson generator](combinatorial-designs-for-the-nisanwigderson.md)
- [Pseudorandom generators against circuits](pseudorandom-generators-against-circuits.md)

## Expansion

This page becomes ready once:

- The circuit-size loss $c\,m\,a\,2^{a}$ must be checked against the original article; the cited textbook proves the construction with different parameters

## Sources

- N. Nisan and A. Wigderson, "Hardness vs randomness", *Journal of Computer and System Sciences* 49(2):149–167, 1994
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2006-09-28, Section 17.2.2 (Definition 17.17 and Lemmas 17.18 and 17.19); published by Cambridge University Press, 2009
