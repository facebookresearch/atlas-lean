# Bottom-up register automata over an algebra

A bottom-up register automaton over an algebra runs on ranked trees with finitely many states and registers holding elements of the algebra; each transition combines the children's registers by a polynomial function, and an output polynomial maps the root's registers to a value.

An *algebra* $\mathcal A=(A,o_1,\dots,o_n)$ is a set $A$ with finitely many operations $o_i:A^{k_i}\to A$. A *polynomial function* of $\mathcal A$ is a function $A^k\to A$ induced by a term over $A\cup\{x_1,\dots,x_k\}$ built with the operations (constants from $A$ allowed); a function $A^k\to A^m$ is polynomial when each of its components is.

A *bottom-up register automaton over $\mathcal A$* is a tuple $M=(\Sigma,n,Q,\Delta,\mathrm{out})$ where $\Sigma$ is a finite ranked alphabet, $n\ge 0$ is the number of registers, $Q$ is a finite set of states, $\Delta$ is a finite set of transitions $a(q_1,\dots,q_k)\to q,f$ with $a\in\Sigma$ of rank $k$, $q,q_1,\dots,q_k\in Q$ and $f:A^{n\times k}\to A^n$ a polynomial function, and $\mathrm{out}$ is a partial map giving for some states $q$ a polynomial function $f_q:A^n\to A$. A tree reaches configurations inductively: if $a(q_1,\dots,q_k)\to q,f$ is in $\Delta$ and each subtree $t_i$ reaches $(q_i,\bar r_i)$, then $a(t_1,\dots,t_k)$ reaches $(q,f(\bar r_1,\dots,\bar r_k))$ (for $k=0$, $f$ is a constant tuple). The relation $[\![M]\!]$ relates a tree $t$ to every $f_q(\bar r)$ with $t$ reaching $(q,\bar r)$ and $\mathrm{out}(q)=f_q$.

$M$ is *functional* when $[\![M]\!]$ is a partial function, and *deterministic* when for each $a$ and $q_1,\dots,q_k$ there is at most one transition $a(q_1,\dots,q_k)\to q,f$; deterministic automata are functional. The *functionality problem* asks whether a given automaton is functional; the *equivalence problem* for functional automata asks whether two of them define the same partial function. The input is *monadic* when every symbol of $\Sigma$ has rank at most $1$, so that trees are words.

**The composition algebra of polynomials.** $\mathcal C=(\mathbb Q[x],+,\times,\circ)$ is the algebra of univariate polynomials with rational coefficients, with addition, multiplication and composition $P\circ Q=P[x:=Q]$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Register automata over $(\Sigma^*,\cdot)$ model streaming string transducers, and register automata over tree contexts with substitution are macro tree transducers. Functionality and equivalence of functional automata are decidable over $(\mathbb Q[X],+,\times)$ by the Hilbert method (Hilbert's basis theorem and Gröbner bases), and the decidability transfers to every algebra that the polynomial ring simulates.

## Sources

- Adrien Boiret, Radosław Piórkowski and Janusz Schmude, "Reducing Transducer Equivalence to Register Automata Problems Solved by \"Hilbert Method\"", in *FSTTCS 2018*, LIPIcs 122, 2018, pp. 48:1–48:16, doi:[10.4230/LIPIcs.FSTTCS.2018.48](https://doi.org/10.4230/LIPIcs.FSTTCS.2018.48); numbering of arXiv:1806.04361v2 ([arXiv](https://arxiv.org/abs/1806.04361v2)): Section 2, the definitions of algebras, polynomial functions and composition algebras and the definition of bottom-up register automata; Section 4, the algebra of polynomials with composition.
