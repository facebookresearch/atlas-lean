# Adding one true point raises B2 and U2 circuit complexity by at most n

Let $\Omega$ be the full binary basis $B_2$ or the basis $U_2$, with $C_\Omega$ the corresponding circuit complexity (every gate charged). Let $f:\{0,1\}^n\to\{0,1\}$ and $a\in\{0,1\}^n$ with $f(a)=0$, and let $g$ agree with $f$ except that $g(a)=1$. Then $g=f\vee m_a$, where $m_a$ is the minterm of $a$, and

$$C_\Omega(g)\le C_\Omega(f)+n.$$

## Proof sketch

The minterm $m_a$ is a conjunction of $n$ literals, computed by $n-1$ polarized conjunction gates of $U_2$ (negations of inputs are absorbed into the gates), and one further disjunction gate gives $f\vee m_a$; $m_a(x)=1$ exactly when $x=a$. This is the step $f_k=f_{k-1}\vee m_k$ of Wegener's chain argument. (Derived, not stated by the sources: for De Morgan circuits with every gate charged, the minterm costs at most $2n-1$ gates including negations; if $f(a)=1$ then $g=f\wedge\neg m_a$ costs two further gates, so any two functions differing on exactly one input satisfy $|C(f)-C(g)|\le 2n+1\le 2n+3$; walking from a constant to $f$ one point at a time gives $C(f)\le 2^n(2n+3)+1$ for every $f$, and a constant function has complexity exactly $1$.)

## Depends on

- [Circuit complexity, binary cost and formula leaf size](circuit-complexity-and-formula-leaf-size.md)
- [The full binary basis B2 and the basis U2](full-binary-basis-b2-and-u2.md)

## Sources

- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987, Section 10.1, proof of Theorem 1.1: equations (1.9) (the minterm $m_k$) and (1.12) ($f_k=f_{k-1}\vee m_k$ raises the circuit size by at most $n$, for $\Omega\in\{B_2,U_2\}$ and the monotone basis).
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
