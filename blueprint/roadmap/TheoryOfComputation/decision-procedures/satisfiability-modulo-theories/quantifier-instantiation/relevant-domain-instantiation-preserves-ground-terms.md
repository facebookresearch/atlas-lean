# Projection models agree with models of the instantiation

Let $F$ be an [essentially uninterpreted](essentially-uninterpreted-formulas.md) set of clauses with instantiation $F^*$, and let $M$ be a model of $F^*$ modulo $T$. Choose projections $\pi_{f,j}$ of the domain onto the values $M(A_{f,j})$ of the relevant terms, fixing those values, with $\pi_{k,i} = \pi_{f,j}$ whenever $S_{k,i} = A_{f,j}$ is a constraint. The *$\pi$-extension* $M^\pi$ has the domain and interpreted symbols of $M$ and interprets each uninterpreted $f$ by $M^\pi(f)(v_1, \dots, v_n) = M(f)(\pi_{f,1}(v_1), \dots, \pi_{f,n}(v_n))$.

1. Every ground argument $t_j$ of an uninterpreted $f$ in $F^*$ lies in $A_{f,j}$.
2. $M^\pi[\![t]\!] = M[\![t]\!]$ for every ground term $t$ of $F^*$.
3. For every non-variable term $t[\vec x]$ of a clause $C_k$ and every tuple $\vec v$, $M^\pi\{\vec x \mapsto \vec v\}[\![t]\!] = M\{\vec x \mapsto \pi_k(\vec v)\}[\![t]\!]$, where $\pi_k(\vec v) = (\pi_{k,1}(v_1), \dots, \pi_{k,n_k}(v_{n_k}))$ for the $n_k$ variables of $C_k$.

## Depends on

- [Essentially uninterpreted formulas](essentially-uninterpreted-formulas.md)

## Sources

- Y. Ge and L. de Moura, "Complete instantiation for quantified formulas in satisfiability modulo theories", in *Computer Aided Verification (CAV 2009)*, LNCS 5643, Springer, 2009, pp. 306–320, <https://leodemoura.github.io/files/ci.pdf>, Section 3: Proposition 1, the projection functions and $\pi$-extensions, Lemma 1 and Lemma 2 with their proof sketches.
