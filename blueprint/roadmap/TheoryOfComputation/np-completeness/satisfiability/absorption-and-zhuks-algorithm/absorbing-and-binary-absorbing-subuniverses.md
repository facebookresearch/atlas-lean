# Absorbing and binary absorbing subuniverses of a finite algebra

Let $\mathbf{A}=(A;F)$ be a finite algebra and $B\subseteq A$ a subuniverse (closed under all operations of $F$). $B$ **absorbs** $\mathbf{A}$, written $B\trianglelefteq\mathbf{A}$, if there is a term operation $t$ of $\mathbf{A}$, of some arity $n$, such that

$$
t(B,\dots,B,A,B,\dots,B)\subseteq B
$$

for every position of the single argument $A$; i.e. $t(b_1,\dots,b_{i-1},a,b_{i+1},\dots,b_n)\in B$ whenever all $b_j\in B$ and $a\in A$. If $t$ can be chosen binary, $B$ is a **binary absorbing subuniverse** ($t(B,A)\cup t(A,B)\subseteq B$). $B$ is **proper** (nontrivial) if $\emptyset\ne B\subsetneq A$. Examples: in a semilattice $(A;\wedge)$ every down-set closed under $\wedge$ absorbs via $\wedge$; if $\mathbf{A}$ has a near-unanimity term of arity $n$ then every singleton subuniverse absorbs via that term. Absorption is transitive and is preserved by intersections and by pp-definitions with absorbing parameters.

## Depends on

- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](../finite-domain-csp-dichotomy/polymorphism-clone-of-a-finite-structure.md)

## Sources

- Libor Barto and Marcin Kozik, "Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem", Logical Methods in Computer Science 8(1:07) (2012).
- Dmitriy Zhuk, "A Proof of the CSP Dichotomy Conjecture", FOCS (2017); Journal of the ACM (2020), arXiv:1704.01914.
