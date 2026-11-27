# Properties of limit set dynamics that force stability or a unique subshift attractor are undecidable

Every nonempty property of the dynamics of a one-dimensional cellular automaton on its limit set is undecidable when it implies that the automaton reaches its limit set in finitely many steps, or that the limit set is its only subshift attractor; this covers injectivity, closingness, expansivity and transitivity of the limit set dynamics.

**Theorem.** Let $(A^{\mathbb Z}, F)$ range over one-dimensional [cellular automata](../cellular-automata-on-z-d.md), and let $\Omega_F = \bigcap_{i \ge 0} F^i(A^{\mathbb Z})$ be the *limit set* of $F$. $F$ is *stable* if $F^n(A^{\mathbb Z}) = \Omega_F$ for some $n$. A nonempty closed set $Y$ with $F(Y) = Y$ is an *attractor* if $Y = \bigcap_{n > 0} \bigcup_{m > n} F^m(U)$ for some clopen set $U$ with $F(U) \subseteq U$, and a *subshift attractor* if moreover $\sigma(Y) = Y$ for the shift $\sigma$. A property $P$ of cellular automata is a *property of limit set dynamics* if $(A^{\mathbb Z}, F) \in P$, $\Omega_G = \Omega_F$ and $G|_{\Omega_G} = F|_{\Omega_F}$ imply $(B^{\mathbb Z}, G) \in P$. Then:

1. every nonempty property of limit set dynamics all of whose members are stable is undecidable (Theorem 3.4 of the source);
2. every nonempty property of limit set dynamics all of whose members have $\Omega_F$ as their unique subshift attractor is undecidable (Theorem 3.5).

Consequently there is no algorithm that decides, given $F$, whether $F$ restricted to $\Omega_F$ is transitive, closing, injective, the identity, expansive or positively expansive (Corollary 3.7). These results extend Kari's theorem that every nontrivial property of limit sets alone is undecidable, which does not apply to properties of the dynamics on the limit set; some properties of limit set dynamics, such as having a point of period $n$, are decidable.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md)

## Proof depends on

- [Nilpotency of cellular automata is undecidable](../nilpotency-of-cellular-automata-is-undecidable.md)

## Expansion

Both parts reduce nilpotency of cellular automata with a spreading state $s$, a state such that the local rule outputs $s$ whenever $s$ occurs in its neighborhood. First, such an automaton can be modified, with a new spreading state, so that it is stable iff it is nilpotent (Lemma 3.3). Given a member $(A^{\mathbb Z}, F)$ of $P$ and an automaton $(B^{\mathbb Z}, G)$ with a spreading state, a product construction gives $(C^{\mathbb Z}, H)$ with $\Omega_H = \Omega_F$ and $H|_{\Omega_H} = F|_{\Omega_F}$ iff $G$ is nilpotent; if $G$ is not nilpotent, $H$ is unstable, respectively has two distinct subshift attractors, so it is not in $P$. Hence $H \in P$ iff $G$ is nilpotent.

## Sources

- P. Di Lena and L. Margara, "Undecidable Properties of Limit Set Dynamics of Cellular Automata", in *26th International Symposium on Theoretical Aspects of Computer Science (STACS 2009)*, Leibniz International Proceedings in Informatics 3, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2009, pp. 337–348, doi:[10.4230/LIPIcs.STACS.2009.1819](https://doi.org/10.4230/LIPIcs.STACS.2009.1819); read as arXiv:0902.1441v1, whose numbering is used here: Definitions 1.2, 1.5, 1.9, 2.4, 3.1 and 3.2, Theorem 2.3, Lemma 3.3, Theorems 3.4 and 3.5 with their proofs, and Corollary 3.7.
