# Williams's faster-than-brute-force algorithm for ACC0-SAT

For every depth $d\ge2$ and modulus $m\ge2$ there are constants $0<\varepsilon<\delta<1$ and $c_0>0$ such that satisfiability of single-output $\mathsf{ACC}^0[m]$ circuits of depth at most $d$ and size at most $2^{n^\varepsilon}$ on $n$ inputs is decidable deterministically in time $O\bigl(2^{\,n-c_0 n^{\delta}}\bigr)$, that is, $2^{n-\Omega(n^\delta)}$ (Williams notes that the choice of standard machine model, for example a multi-tape Turing machine, is not crucial).

## Proof sketch

Fix the first $\ell=n^\delta$ inputs in all $2^\ell$ ways and take the OR of the resulting circuits (an $\mathsf{ACC}^0$ circuit of size $2^\ell 2^{n^\varepsilon}$ on $n-\ell$ inputs). Convert this depth-$(d+1)$ circuit to a $\mathrm{SYM}\circ\mathrm{AND}$ circuit of size $s^{e(\ell\log s)^{e}}\le 2^{O(n^{(2e+1)\delta})}\le 2^{0.1(n-\ell)}$, where $s=2^{\ell}2^{n^\varepsilon}$ and $e$ depends only on $d$ and $m$ (choose $\delta<1/(2e+1)$) and evaluate it on all $2^{n-\ell}$ remaining inputs with the evaluation lemma, in time $2^{n-\ell}\mathrm{poly}(n)$.

## Depends on

- [SYM ∘ AND circuits](sym-and-circuits.md)
- [The class $\mathsf{ACC}^0$](../../../complexity-classes/time-and-space-complexity-classes/acc0.md)
- [Deterministic time classes on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dtime.md)

## Proof depends on

- [Yao and Beigel–Tarui: ACC0 circuits are quasi-polynomial SYM ∘ AND circuits](beigel-tarui-acc0-to-sym-and.md)
- [Williams's evaluation lemma for SYM ∘ AND circuits](williams-evaluation-lemma.md)

## Sources

- Ryan Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM 61(1), Article 2, 2014 (Theorem 4.1).
