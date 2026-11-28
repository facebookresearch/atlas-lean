# The KPT witnessing theorem

If a universal theory proves a $\forall\exists\forall$ sentence with an open matrix, then finitely many terms witness it interactively: the $i$-th term proposes a witness from the counterexamples to the earlier proposals, and one of the proposals is always correct.

Let $T$ be a universal theory over a language $\mathcal{L}$ containing at least one constant or function symbol, let $\varphi(x, y, z)$ be an open $\mathcal{L}$-formula, and suppose $T \vdash \forall x\, \exists y\, \forall z\, \varphi(x, y, z)$. Then there are finitely many $\mathcal{L}$-terms $t_1(x), t_2(x, z_1), \dots, t_l(x, z_1, \dots, z_{l-1})$, containing only the displayed variables, such that

$$
T \vdash \forall x, z_1, \dots, z_l\ \big(\varphi(x, t_1(x), z_1) \vee \varphi(x, t_2(x, z_1), z_2) \vee \dots \vee \varphi(x, t_l(x, z_1, \dots, z_{l-1}), z_l)\big).
$$

For $T = \mathsf{T}_{\mathsf{PV}}$ (or $\mathsf{PV}$) the terms are polynomial-time functions. For $\mathsf{T}_{\mathsf{APC}_1}$ there are a constant $l$ and randomized polynomial-time functions $f_1, \dots, f_l$ such that for every $x, z_1, \dots, z_l$ the disjunction holds with probability at least $1/\mathrm{poly}(|x|, |z_1|, \dots, |z_{l-1}|)$ over their internal randomness, and for $\mathsf{T}'_{\mathsf{APC}_1}$ there are a constant $l'$ and polynomial-size circuits $f'_1, \dots, f'_{l'}$ such that it holds for every $x, z_1, \dots, z_{l'}$.

## Proof sketch

The disjunction is a student–teacher protocol: the student proposes $t_1(x)$; if it fails, the teacher returns a counterexample $z_1$ with $\neg\varphi(x, t_1(x), z_1)$, the student proposes $t_2(x, z_1)$, and so on, and the student succeeds within $l$ rounds. Pich and Santhanam describe the theorem as "a form of Herbrand's theorem". For the $\mathsf{APC}_1$ variants one first Skolemizes the dual weak pigeonhole principle and then replaces queries to the Skolem function by random strings, or, without parameters, by polynomially many non-uniform advice strings outside the range.

## Depends on

- [Cook's theory PV of polynomial-time reasoning](cooks-theory-pv.md)
- [Jeřábek's theory APC1 and the dual weak pigeonhole principle](theory-apc1.md)

## Proof depends on

None.

## Informally uses

- [Herbrand's theorem](../../../../Logic/first-order-logic/herbrand-s-theorem.md)

## Sources

- Ján Pich and Rahul Santhanam, "Strong Co-Nondeterministic Lower Bounds for NP Cannot be Proved Feasibly", *STOC* 2021, DOI 10.1145/3406325.3451117 (Theorems 3 and 4, Section 3.1, in the authors' full version of March 2021, <https://users.ox.ac.uk/~coml0742/papers/stoc-final.pdf>).
- Igor C. Oliveira, "SIGACT News Complexity Theory Column 124: Meta-Mathematics of Computational Complexity Theory", *ACM SIGACT News* 56(1), 2025, DOI 10.1145/3726856.3726862, arXiv:2504.04416v1 (Theorem 3.2, Section 3.1).
