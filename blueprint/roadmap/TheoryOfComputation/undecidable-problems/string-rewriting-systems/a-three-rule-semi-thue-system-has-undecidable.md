# A three-rule semi-Thue system has an undecidable individual word problem

There are a semi-Thue system with three rules and a fixed word $w_0$ such that no algorithm decides, for an input word $w$, whether $w$ rewrites to $w_0$.

**Semi-Thue systems.** A *semi-Thue system* $T = (\Sigma, R)$ has a finite alphabet $\Sigma$ and a finite set $R \subseteq \Sigma^* \times \Sigma^*$ of rules. One writes $u \to_T v$ if $u = u_1 x u_2$ and $v = u_1 y u_2$ for some rule $(x, y) \in R$, and $\to_T^*$ for the reflexive and transitive closure. For a fixed system $T$ and a fixed word $w_0$, the *individual word problem* asks, for an input word $w$, whether $w \to_T^* w_0$.

**Theorem (Matiyasevich and Sénizergues).** There exist a semi-Thue system with three rules and a word $w_0$ for which the individual word problem is undecidable.

Through Claus's reduction of semi-Thue systems to the Post correspondence problem, this theorem gives the undecidability of the Post correspondence problem for instances of size $7$ of a special form ([mortality and freeness bounds from Claus instances](../matrix-and-dynamical-systems/matrix-mortality-and-freeness/mortality-and-freeness-bounds-from-claus.md)).

## Depends on

- [Derivations in a string rewriting system](derives.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof of the three-rule theorem is in the paper of Matiyasevich and Sénizergues and is not reproduced in the copy read; a good expansion adds and links a page for that proof.

## Sources

- V. Halava, T. Harju and M. Hirvensalo, "Undecidability Bounds for Integer Matrices Using Claus Instances", *International Journal of Foundations of Computer Science* 18(5) (2007), pp. 931–948, doi:10.1142/S0129054107005066; read in the authors' copy at <https://users.utu.fi/harju/articles/HHH_ClausInst.pdf>: Theorem 3 (the three-rule semi-Thue system, credited to Matiyasevich and Sénizergues) and the definition of semi-Thue systems and the individual word problem in Section 2, in the numbering of that copy.
- Yu. Matiyasevich and G. Sénizergues, "Decision problems for semi-Thue systems with a few rules", *Theoretical Computer Science* 330(1) (2005), pp. 145–169, doi:10.1016/j.tcs.2004.09.016 (original source, cited beside the copy read).
