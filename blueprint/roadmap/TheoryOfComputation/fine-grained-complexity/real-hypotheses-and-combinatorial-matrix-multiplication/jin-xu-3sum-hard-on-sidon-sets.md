# Jin–Xu: 3SUM remains n^{2-o(1)}-hard on Sidon sets

A set $S$ of integers is a **Sidon set** if it has no nontrivial solutions to $a+b=c+d$, i.e. $a+b=c+d$ with $a,b,c,d\in S$ implies $\{a,b\}=\{c,d\}$. Assuming the (integer) 3SUM hypothesis, solving 3SUM on an $n$-element Sidon set of integers (deciding whether it contains $a,b,c$ with $a+b+c=0$) still requires $n^{2-o(1)}$ time. A slight generalization gives 3SUM-hardness of every nontrivial 4-variate linear degeneracy testing problem (4-LDT), extending a result of Dudek, Gawrychowski and Starikovskaya for 3-LDTs.

## Proof sketch

Starting from a hard 3SUM instance, one removes additive structure by a structure-versus-randomness argument: if the set has many additive quadruples, the Balog–Szemerédi–Gowers theorem yields a large subset with small doubling, on which 3SUM is solved quickly by sparse convolution; otherwise one hashes with a new almost-linear, almost 3-universal hash family (for integers without small-coefficient linear relations) to split the instance into Sidon-like pieces.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [Fine-grained reductions](../fine-grained-hypotheses/fine-grained-reductions.md)

## Sources

- Ce Jin and Yinzhan Xu, "Removing Additive Structure in 3SUM-Based Reductions", STOC (2023), arXiv:2211.07048.
