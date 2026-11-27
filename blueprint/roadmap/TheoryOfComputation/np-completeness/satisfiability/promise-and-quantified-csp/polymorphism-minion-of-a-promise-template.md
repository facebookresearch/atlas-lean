# The polymorphism minion Pol(A,B) of a promise template

For finite similar structures $\mathbb{A}\to\mathbb{B}$, an $n$-ary **polymorphism** of the pair is a homomorphism $f:\mathbb{A}^n\to\mathbb{B}$, i.e. a map $f:A^n\to B$ such that for each relation symbol $R$ of arity $r$ and all $\bar a^1,\dots,\bar a^n\in R^{\mathbb{A}}$ the coordinatewise image lies in $R^{\mathbb{B}}$. The set $\mathrm{Pol}(\mathbb{A},\mathbb{B})$ is generally not closed under composition (the output lives in $B$, inputs in $A$) and is not a clone, but it is closed under minors $f\mapsto f(x_{\pi(1)},\dots,x_{\pi(n)})$ for all $\pi:[n]\to[m]$, so it is a **minion**. Examples: the Boolean pair $(\text{1-in-3},\text{NAE})$ has an alternating threshold polymorphism of every odd arity, and $\mathrm{Pol}(\mathbb{K}_k,\mathbb{K}_c)$ consists of the maps $[k]^n\to[c]$ sending tuples that differ in every coordinate to distinct colours.

## Depends on

- [Promise constraint satisfaction PCSP(A,B) for a pair of finite templates](promise-csp-of-a-template-pair.md)
- [Minions, minion homomorphisms and pp-constructions](../finite-domain-csp-dichotomy/minions-minion-homomorphisms-pp-constructions.md)

## Sources

- Libor Barto, Jakub Bulín, Andrei Krokhin and Jakub Opršal, "Algebraic approach to promise constraint satisfaction", Journal of the ACM 68(4) (2021), arXiv:1811.00970.
- Joshua Brakensiek and Venkatesan Guruswami, "Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy", ECCC TR16-183 (2016), arXiv:1704.01937.
