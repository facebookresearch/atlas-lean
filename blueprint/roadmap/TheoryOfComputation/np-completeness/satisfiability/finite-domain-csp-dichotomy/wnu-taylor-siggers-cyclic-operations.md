# Weak near-unanimity, Taylor, Siggers and cyclic operations on a finite set

Let $A$ be a finite set and $f:A^n\to A$.

- $f$ is a **weak near-unanimity (WNU)** operation, $n\ge 2$, if for all $x,y\in A$: $f(y,x,\dots,x)=f(x,y,x,\dots,x)=\dots=f(x,\dots,x,y)$.
- $f$ is a **Taylor** operation if $f$ is idempotent and for every coordinate $i\le n$ it satisfies some identity $f(u_1,\dots,u_n)\approx f(v_1,\dots,v_n)$ with $u_j,v_j\in\{x,y\}$ and $u_i=x\ne y=v_i$.
- A 6-ary $s$ is a **Siggers** operation if for all $x,y,z\in A$:

$$
s(x,y,x,z,y,z)=s(y,x,z,x,z,y).
$$

- $f$ is **cyclic** if $f(x_1,x_2,\dots,x_n)=f(x_2,\dots,x_n,x_1)$ for all arguments.

The WNU, Siggers and cyclic conditions are systems of height-1 identities (idempotency is not required), so their satisfaction by $\mathrm{Pol}(\mathbb{A})$ is preserved by minion homomorphisms. An idempotent WNU, Siggers or cyclic operation (of arity at least 2) is Taylor.

## Depends on

- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](polymorphism-clone-of-a-finite-structure.md)
- [Minions, minion homomorphisms and pp-constructions](minions-minion-homomorphisms-pp-constructions.md)

## Sources

- Miklós Maróti and Ralph McKenzie, "Existence theorems for weakly symmetric operations", Algebra Universalis 59 (2008).
- Mark H. Siggers, "A strong Mal'cev condition for locally finite varieties omitting the unary type", Algebra Universalis 64 (2010).
- Libor Barto and Marcin Kozik, "Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem", Logical Methods in Computer Science 8(1:07) (2012).
