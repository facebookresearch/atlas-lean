# The Post correspondence problem is undecidable for Claus instances of size 7

The Post correspondence problem stays undecidable for Claus instances with seven pairs, whose solutions must start with the first pair and end with the last; even six of the seven pairs and one word of the first pair can be fixed.

An instance of the [Post correspondence problem](pcp.md) is given here by two morphisms $h, g \colon \Sigma^* \to \Gamma^*$, and asks for a nonempty word $w$ with $h(w) = g(w)$; its *size* is $\lvert\Sigma\rvert$. Let $\Gamma = \{a, b\}$, $d = aba$ and $A = ab^2 b^* a$. An instance with $\Sigma = \{b_1, \dots, b_n\}$, $n \geq 3$, and $h, g \colon \Sigma^* \to (abb^*a)^*$ is a *Claus instance* if

$$
h(b_i) \in (dA)^* \ (i < n), \qquad h(b_n) = dd, \qquad g(b_1) = d, \qquad g(b_i) \in (Ad)^* \ (1 < i < n), \qquad g(b_n) \in (Ad)^+ d .
$$

Every nonempty solution of a Claus instance has the form $b_1 u b_n$ with $u$ a word over $\{b_2, \dots, b_{n-1}\}$ (Lemma 1 of the source).

**Theorem (Halava, Harju and Hirvensalo, after Claus).**

1. If some semi-Thue system with $n$ rules has an undecidable individual word problem, then the Post correspondence problem is undecidable for Claus instances of size $n + 4$ (Theorem 4 of the source).
2. The Post correspondence problem is undecidable for Claus instances of size $7$ (Theorem 5).
3. There are a word $v_1 \in \Gamma^*$ and six pairs $(u_2, v_2), \dots, (u_7, v_7) \in \Gamma^* \times \Gamma^*$ such that it is undecidable, for a given word $u_1 \in \Gamma^*$, whether $u_1 u_{i_2} \cdots u_{i_m} u_7 = v_1 v_{i_2} \cdots v_{i_m} v_7$ for some $i_2, \dots, i_m \in \{2, \dots, 6\}$; for every $u_1$ the instance with $h(b_i) = u_i$ and $g(b_i) = v_i$ is a Claus instance (Theorem 6).

Item 2 follows from item 1 and the three-rule semi-Thue system of Matiyasevich and Sénizergues. By the form of the solutions, these instances are also instances of the restricted Post correspondence problem, in which a solution must start with the first pair, end with the last and use only the others in between.

## Depends on

- [The Post correspondence problem](pcp.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [A three-rule semi-Thue system has an undecidable individual word problem](../string-rewriting-systems/a-three-rule-semi-thue-system-has-undecidable.md)

## Expansion

A good expansion links pages for Lemma 1 of the source (the form of the solutions of a Claus instance) and for Claus's construction behind item 1. From a semi-Thue system $T = (\{a, b\}, R)$ whose rules are encoded in $A^*$, an input word $w$ and the fixed word $w_0$, with the marker $f = aa$ and the morphisms $\ell_d(x) = dx$ and $r_d(x) = xd$, it sets $h(x) = \ell_d(x)$ and $g(x) = r_d(x)$ for the letters $x$, $h(t_i) = \ell_d(v_i)$ and $g(t_i) = r_d(u_i)$ for the rules $t_i = (u_i, v_i)$, $h(c) = \ell_d(wf)$ and $g(c) = d$, and $h(e) = dd$ and $g(e) = r_d(f w_0) d$ (Equation (2.1) of the source). The solutions are the words $c\, w_1 f w_2 f \cdots f w_m\, e$ that spell a derivation $w = w_1 \to_T^* \cdots \to_T^* w_m = w_0$, and only $h(c)$ depends on the input $w$, which gives item 3.

## Sources

- V. Halava, T. Harju and M. Hirvensalo, "Undecidability Bounds for Integer Matrices Using Claus Instances", *International Journal of Foundations of Computer Science* 18(5) (2007), pp. 931–948, doi:10.1142/S0129054107005066; read in the authors' copy at <https://users.utu.fi/harju/articles/HHH_ClausInst.pdf>: the definition of Claus instances, Lemma 1, Theorems 4, 5 and 6 and the construction (2.1) in Section 2, in the numbering of that copy. The definition there writes "$h(b_i) \in (dA)^*$ with $h(b_n) = dd$" and "$g(b_i) \in (Ad)^*$ with $g(b_1) = d$"; since every block of $dA$ and of $Ad$ has length at least $7$, the membership conditions apply to the other letters, as above.
