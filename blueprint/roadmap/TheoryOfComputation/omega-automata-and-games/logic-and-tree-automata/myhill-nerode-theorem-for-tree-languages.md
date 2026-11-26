# Myhill–Nerode theorem for tree languages

Let $\mathcal{F}$ be a ranked alphabet. An equivalence relation $\equiv$ on the set $T(\mathcal{F})$ of ground terms is a
*congruence* if $u_i \equiv v_i$ for $1 \le i \le n$ implies $f(u_1, \dots, u_n) \equiv f(v_1, \dots, v_n)$ for every $f$ of arity
$n$, and it has *finite index* if it has finitely many classes. For $L \subseteq T(\mathcal{F})$, let $u \equiv_L v$ hold when
$C[u] \in L \iff C[v] \in L$ for every context $C$ (a term with one occurrence of a variable). The following are equivalent:

1. $L$ is recognizable, in the sense of [bottom-up finite tree automata](bottom-up-finite-tree-automata.md);
2. $L$ is a union of classes of some congruence of finite index;
3. $\equiv_L$ is a congruence of finite index.

Equivalently, $L$ is recognizable if and only if $L = \varphi^{-1}(A')$ for a homomorphism $\varphi$ from the term algebra
$T(\mathcal{F})$ to a finite $\mathcal{F}$-algebra $A$ and a subset $A'$ of its carrier.

## Depends on

- [Bottom-up finite tree automata](bottom-up-finite-tree-automata.md)

## Proof depends on

- [Determinization, closure and decision properties of regular tree languages](determinization-closure-and-decision-properties.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Section 1.5, the Myhill–Nerode Theorem with its proof, and the algebraic characterization stated after it.
- F. Gécseg and M. Steinby, *Tree Automata*, Akadémiai Kiadó, Budapest, 1984; reissued with a preface to the second edition as arXiv:1509.06233, 2015, with the original numbering: Section 2.7, Theorem 2.7.1 and Corollary 2.7.2.
