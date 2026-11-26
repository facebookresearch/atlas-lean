# Minions, minion homomorphisms and pp-constructions

A **minion** $\mathscr{M}$ is a family of sets $\mathscr{M}^{(n)}$, $n\ge 1$, together with **minor maps**: for every map $\pi:[n]\to[m]$ a function $f\mapsto f^{\pi}$ from $\mathscr{M}^{(n)}$ to $\mathscr{M}^{(m)}$ with $(f^{\pi})^{\sigma}=f^{\sigma\circ\pi}$ and $f^{\mathrm{id}}=f$. For a clone of operations the minor is $f^{\pi}(x_1,\dots,x_m)=f(x_{\pi(1)},\dots,x_{\pi(n)})$; thus $\mathrm{Pol}(\mathbb{A})$ is a minion. A **minion homomorphism** $\xi:\mathscr{M}\to\mathscr{N}$ preserves arities and commutes with all minor maps; for clones this is the same as an **h1 clone homomorphism**, a map preserving all identities of **height 1**, i.e. identities $f(x_{i_1},\dots,x_{i_n})\approx g(x_{j_1},\dots,x_{j_m})$ with exactly one function symbol on each side.

A structure $\mathbb{B}$ is a **pp-power** of $\mathbb{A}$ if its domain is $A^k$ for some $k$ and each relation of $\mathbb{B}$, viewed as a relation on $A$ of $k$ times the arity, is pp-definable in $\mathbb{A}$. $\mathbb{B}$ is **pp-constructible** from $\mathbb{A}$ if $\mathbb{B}$ is homomorphically equivalent to a pp-power of $\mathbb{A}$.

## Depends on

- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](polymorphism-clone-of-a-finite-structure.md)
- [Cores of finite relational structures](cores-of-finite-relational-structures.md)

## Sources

- Libor Barto, Jakub Opršal and Michael Pinsker, "The wonderland of reflections", Israel Journal of Mathematics 223 (2018), arXiv:1510.04521.
- Libor Barto, Jakub Bulín, Andrei Krokhin and Jakub Opršal, "Algebraic approach to promise constraint satisfaction", Journal of the ACM 68(4) (2021), arXiv:1811.00970.
