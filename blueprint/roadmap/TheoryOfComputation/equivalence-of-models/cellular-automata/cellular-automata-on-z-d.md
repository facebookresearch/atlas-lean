# Cellular automata on $\mathbb{Z}^d$

A $d$-dimensional *cellular automaton* is a triple $(S, N, f)$ of a finite set $S$ of states, a *neighborhood vector*
$N = (\vec{x}_1, \dots, \vec{x}_n)$ of $n$ distinct elements of $\mathbb{Z}^d$ and a *local rule* $f : S^n \to S$. A
*configuration* is a map $c : \mathbb{Z}^d \to S$, and the *global transition function* $G : S^{\mathbb{Z}^d} \to S^{\mathbb{Z}^d}$
sends $c$ to the configuration $e$ with
$e(\vec{x}) = f(c(\vec{x} + \vec{x}_1), \dots, c(\vec{x} + \vec{x}_n))$ for every $\vec{x} \in \mathbb{Z}^d$.
The automaton is identified with $G$, while algorithms receive $S$, $N$ and $f$.
It is *injective*, *surjective* or *bijective* when $G$ is; it is *reversible* when some cellular automaton $G'$ with the
same states and dimension satisfies $G \circ G' = G' \circ G = \mathrm{id}$; and it is *nilpotent* when $G^n$ is constant
for some $n \ge 1$. The *shift* $\sigma_i$, for $i = 1, \dots, d$, is the cellular automaton with neighborhood
$(\vec{e}_i)$ and the identity as local rule, where $\vec{e}_i$ is the $i$-th unit vector.

The configuration space $S^{\mathbb{Z}^d}$ carries the product of the discrete topologies, which is compact; global
transition functions are continuous and commute with the shifts.

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Sections 2.1 (definition), 2.3 (shifts), 2.4 (nilpotency and reversibility), 2.7 (topology) and 3 (injective, surjective and bijective automata).
