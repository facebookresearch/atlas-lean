# A three-rule semi-Thue system has an undecidable individual word problem

There are a semi-Thue system with three rules and a fixed word $w_0$ such that no algorithm decides, for an input word $w$, whether $w$ rewrites to $w_0$; through Claus's construction, the Post correspondence problem is undecidable for Claus instances with seven pairs.

**Semi-Thue systems.** A *semi-Thue system* $T = (\Sigma, R)$ has an alphabet $\Sigma$ and a set $R \subseteq \Sigma^* \times \Sigma^*$ of rules. One writes $u \to_T v$ if $u = u_1 x u_2$ and $v = u_1 y u_2$ for some rule $(x, y) \in R$, and $\to_T^*$ for the reflexive and transitive closure. For a fixed system $T$ and a fixed word $w_0$, the *individual word problem* asks, for an input word $w$, whether $w \to_T^* w_0$.

**Theorem (Matiyasevich and Sénizergues).** There exist a semi-Thue system with three rules and a word $w_0$ for which the individual word problem is undecidable.

**Claus instances.** An instance of the Post correspondence problem is given by two morphisms $h, g \colon \Sigma^* \to \Gamma^*$ and asks for a nonempty word $w$ with $h(w) = g(w)$; its *size* is $|\Sigma|$. Let $\Gamma = \{a, b\}$, $d = aba$ and $A = ab^2 b^* a$. An instance with $\Sigma = \{b_1, \dots, b_n\}$ is a *Claus instance* if $h(b_i) \in (dA)^*$ for all $i$ with $h(b_n) = dd$, and $g(b_i) \in (Ad)^*$ for all $i$ with $g(b_1) = d$ and $g(b_n) \in (Ad)^+ d$; every nonempty solution of a Claus instance has the form $b_1 u b_n$ with $u$ over $\{b_2, \dots, b_{n-1}\}$. If some semi-Thue system with $n$ rules has an undecidable individual word problem, then the Post correspondence problem is undecidable for Claus instances of size $n + 4$ (Claus). With the theorem above, the Post correspondence problem is undecidable for Claus instances of size $7$; moreover, there are a word $v_1$ and six pairs $(u_2, v_2), \dots, (u_7, v_7)$ over $\{a, b\}$ such that it is undecidable, for a given word $u_1$, whether $u_1 u_{i_2} \cdots u_{i_m} u_7 = v_1 v_{i_2} \cdots v_{i_m} v_7$ for some indices $i_2, \dots, i_m \in \{2, \dots, 6\}$.

The general Post correspondence problem is now known to be undecidable already for five pairs of words (Neary).

## Depends on

- [The Post correspondence problem](../post-correspondence-problem/pcp.md)
- [Derivations in a string rewriting system](derives.md)

## Proof depends on

None.

## Expansion

The proof of the three-rule theorem is in the paper of Matiyasevich and Sénizergues and is not reproduced in the copy read; it has no page here. Claus's reduction, for a rewriting system $T$ over $\{a, b\}$ with rules encoded in $A^*$, an input word $w$ and the fixed word $w_0$, uses letters $a, b$, one letter per rule, a first letter $c$ with $h(c) = \ell_d(w\,aa)$ and $g(c) = d$, and a last letter $e$ with $h(e) = dd$ and $g(e) = r_d(aa\,w_0)\,d$, where $\ell_d(x) = dx$ and $r_d(x) = xd$ letterwise; its solutions spell derivations $w \to_T^* w_0$ separated by the marker $aa$.

## Sources

- V. Halava, T. Harju and M. Hirvensalo, "Undecidability Bounds for Integer Matrices Using Claus Instances", *International Journal of Foundations of Computer Science* 18(5) (2007), pp. 931–948, doi:10.1142/S0129054107005066; read in the authors' copy at <https://users.utu.fi/harju/articles/HHH_ClausInst.pdf>: Theorem 3 (the three-rule semi-Thue system, credited to Matiyasevich and Sénizergues), the definition of semi-Thue systems and the individual word problem in Section 2, Theorem 4 (Claus's reduction), Theorems 5 and 6 (Claus instances of size 7) and Problem 2 (the morphism form of the Post correspondence problem), in the numbering of that copy.
- Yu. Matiyasevich and G. Sénizergues, "Decision problems for semi-Thue systems with a few rules", *Theoretical Computer Science* 330(1) (2005), pp. 145–169, doi:10.1016/j.tcs.2004.09.016 (original source, cited beside the copy read).
- T. Neary, "Undecidability in binary tag systems and the Post correspondence problem for five pairs of words", in *32nd International Symposium on Theoretical Aspects of Computer Science (STACS 2015)*, Leibniz International Proceedings in Informatics 30, 2015, pp. 649–661, doi:10.4230/LIPIcs.STACS.2015.649; read in the open-access publisher copy at <https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf>: Theorem 11 (five pairs).
