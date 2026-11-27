# Invariants of DPLL modulo theories

If $\emptyset \parallel F \Longrightarrow^*_{\mathcal{FT}} M \parallel G$ in the [full DPLL modulo theories system](dpll-modulo-theories-transition-system.md), then:

1. all atoms of $M$ and of $G$ are atoms of $F$;
2. $M$ contains no literal twice and no complementary pair, so it is an assignment;
3. $G$ is $T$-equivalent to $F$;
4. if $M = M_0\, l_1\, M_1 \dots l_n\, M_n$ with $l_1, \dots, l_n$ all its decision literals, then $F, l_1, \dots, l_i \models_T M_i$ for every $i \le n$.

## Depends on

- [DPLL modulo theories transition system](dpll-modulo-theories-transition-system.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 3.4, Lemma 3.6 and its proof.
