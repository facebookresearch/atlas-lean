# Finite, periodic and Garden-of-Eden configurations

Let $G$ be a $d$-dimensional [cellular automaton](cellular-automata-on-z-d.md) with states $S$ and local rule $f$.
A state $q$ is *quiescent* if $f(q, \dots, q) = q$. Given a quiescent state, a configuration is *finite* if only finitely
many cells are in a state other than $q$; finite configurations form a set $C_F$ that $G$ maps into itself, and $G_F$
denotes the restriction $C_F \to C_F$. A configuration $c$ is *(spatially) periodic* if there are positive integers
$t_1, \dots, t_d$ with $c(\vec{x} + t_i \vec{e}_i) = c(\vec{x})$ for all $\vec{x}$ and $i$; periodic configurations form a set
$C_P$ that $G$ maps into itself, with restriction $G_P : C_P \to C_P$. A *Garden-of-Eden configuration* is a
configuration with no preimage under $G$; one exists exactly when $G$ is not surjective.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Section 2.3 (quiescent states, finite and periodic configurations, $G_F$ and $G_P$) and Section 3 (Garden-of-Eden configurations).
