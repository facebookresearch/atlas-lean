# Analytical hierarchy

The analytical hierarchy classifies sets of natural numbers by definitions that quantify over functions from ℕ to ℕ as
well as over numbers: $\Sigma^1_n$ and $\Pi^1_n$ count the alternations of function quantifiers in front of an arithmetical
matrix.

Let $\mathcal{F}$ be the set of functions $\mathbb{N} \to \mathbb{N}$. A relation $S \subseteq \mathcal{F}^m \times \mathbb{N}^k$
is *computable* if its characteristic function is computed by an oracle Turing machine with the functions as oracles. A set
$R \subseteq \mathbb{N}^l$ is *analytical* if it is computable or has a *predicate form*

$$
R = \{(x_1, \dots, x_l) \mid (Q_1 s_1) \cdots (Q_r s_r)\, S(f_1, \dots, f_m, x_1, \dots, x_k)\}
$$

with $S$ computable, each $Q_i \in \{\forall, \exists\}$, and $s_1, \dots, s_r$ the variables $f_1, \dots, f_m,
x_{l+1}, \dots, x_k$ in some order. A quantifier over a function variable has *type 1*, over a number variable *type 0*; the
*reduced prefix* keeps only the type-1 quantifiers. For $n \ge 1$, $R$ is in $\Sigma^1_n$ (resp. $\Pi^1_n$) if it has a
predicate form whose reduced prefix begins with $\exists^1$ (resp. $\forall^1$) and has $n - 1$ alternations;
$\Sigma^1_0 = \Pi^1_0$ is the class of arithmetical sets.

A set $A \subseteq \mathbb{N}$ is *1-reducible* to $B \subseteq \mathbb{N}$, written $A \le_1 B$, if $A = f^{-1}[B]$ for a
total computable injective $f$. A set is *$\Sigma^1_n$-complete* (resp. *$\Pi^1_n$-complete*) if it belongs to $\Sigma^1_n$
(resp. $\Pi^1_n$) and every set of that class is 1-reducible to it; it is *hard* if it satisfies the second condition. Sets of
tuples, and sets of finite objects such as automata, are identified with sets of naturals through computable codings.

## Depends on

- [The arithmetical class $\Sigma_n$](../arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../arithmetical-hierarchy/is-pi.md)

## Proof depends on

None.

## Expansion

For each $n \ge 1$: $\Sigma^1_n \cup \Pi^1_n \subsetneq \Sigma^1_{n+1} \cap \Pi^1_{n+1}$, a set is in $\Sigma^1_n$ iff its
complement is in $\Pi^1_n$, and both $\Sigma^1_n \setminus \Pi^1_n$ and $\Pi^1_n \setminus \Sigma^1_n$ are nonempty.
Adjacent quantifiers of the same kind and type merge, a number quantifier can be replaced by a function quantifier of the
same kind, and $\exists^0 \forall^1$ can be swapped to $\forall^1 \exists^0$ (dually $\forall^0 \exists^1$ to
$\exists^1 \forall^0$). Every arithmetical set, in particular every recursively enumerable set, lies in
$\Delta^1_1 = \Sigma^1_1 \cap \Pi^1_1$, so a $\Sigma^1_1$-hard or $\Pi^1_1$-hard set is not arithmetical and a fortiori
undecidable. A typical $\Sigma^1_1$-complete set (Harel) is the set of nondeterministic Turing machines that, started on the
blank tape, have an infinite computation entering the initial state infinitely often.

## Sources

- O. Finkel, "Three applications to rational relations of the high undecidability of the infinite Post correspondence problem in a regular ω-language", *International Journal of Foundations of Computer Science* 23(7):1481–1497, 2012, doi:[10.1142/S0129054112400606](https://doi.org/10.1142/S0129054112400606). Numbering of the version read, arXiv:1107.5886v1: Definitions 2.2–2.5, Proposition 2.6, Theorems 2.7 and 2.8, the definitions of 1-reduction and completeness in Section 2, and Theorem 2.10 (Harel).
