# Nondeterministic space hierarchy theorem

Let $g$ be space-constructible with $\lfloor\log_2 n\rfloor\le g(n)$, and let $f$ satisfy: for every constant $c$, eventually $c\,f(n)+c< g(n)$. Then

$$
\mathsf{NSPACE}(f)\subsetneq\mathsf{NSPACE}(g)
$$

on binary words. In particular $\mathsf{NL}\subsetneq\mathsf{NSPACE}(\log^2 n)$.

## Proof sketch

Diagonalize against nondeterministic machines: on input $x=\langle M,\text{pad}\rangle$, simulate $M$ on $x$ within space $g$ and accept iff $M$ does **not** accept. Complementing a nondeterministic space-bounded computation within the same space is possible by the Immerman–Szelepcsényi theorem, so the diagonal language lies in $\mathsf{NSPACE}(g)$ yet differs from every language of $\mathsf{NSPACE}(f)$.

## Depends on

- [Nondeterministic space classes](../../../time-and-space-complexity-classes/nspace.md)

## Proof depends on

- [Immerman–Szelepcsényi: NSPACE(s) = coNSPACE(s)](nspace-closed-under-complement.md)
- [Space hierarchy theorem for space-constructible bounds](../../../../hierarchy-theorems-and-barriers/space-hierarchy-theorem/space-hierarchy-theorem-for-space-constructible.md)

## Sources

- Neil Immerman, "Nondeterministic Space Is Closed under Complementation", SIAM Journal on Computing 17(5), 1988, Corollary 4.
- Michael Sipser, "Introduction to the Theory of Computation", Cengage Learning, 2013.
