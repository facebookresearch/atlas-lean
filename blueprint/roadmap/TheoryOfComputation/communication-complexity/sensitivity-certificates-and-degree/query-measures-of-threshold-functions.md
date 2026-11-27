# Query measures of threshold functions

For $1 \le j \le n$ let $\mathrm{Th}^n_j(x) = [|x| \ge j]$ on $\{0,1\}^n$. Then

$$C(\mathrm{Th}^n_j) = s(\mathrm{Th}^n_j) = bs(\mathrm{Th}^n_j),$$

since every threshold function is monotone (setting more bits to $1$ cannot decrease its value). For majority, $\mathrm{MAJ}_n(x) = [|x| > n/2] = \mathrm{Th}^n_{\lfloor n/2 \rfloor + 1}(x)$, the sensitivity is $s(\mathrm{MAJ}_n) = \lceil (n+1)/2 \rceil$.

## Proof sketch

The equality is Nisan's theorem for monotone functions, and the value for majority is Turán's lower bound $s(f) \ge \lceil (n+1)/2 \rceil$ for nonconstant symmetric $f$, which majority attains.

Derived here (not stated in the cited source): a coordinate is sensitive at $x$ iff $|x| = j$ and $x_i = 1$, or $|x| = j - 1$ and $x_i = 0$, so $s(\mathrm{Th}^n_j) = \max(j, n + 1 - j)$, and by the equality all three measures take this value; for majority it is $\lfloor n/2 \rfloor + 1$. Every nonconstant symmetric function is evasive, so $D(\mathrm{Th}^n_j) = n$, and parity has $s = bs = C = D = n$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [For monotone functions, sensitivity, block sensitivity and certificate complexity coincide](monotone-functions-s-bs-c-coincide.md)
- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)
- [Nonconstant symmetric functions are evasive](../decision-tree-structure/nonconstant-symmetric-functions-are-evasive.md)

## Sources

- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002, Section 2.1 (the definitions of $\mathrm{MAJ}_n$ and of monotone functions), Section 6.1, Proposition 2 and the sentence after it ($s(\mathrm{MAJ}_n) = \lceil (n+1)/2 \rceil$), and Section 6.2, Proposition 3 (Nisan: $C(f) = s(f) = bs(f)$ for monotone $f$).
