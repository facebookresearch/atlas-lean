# Kolaitis–Vardi: the 0-1 law for finite-variable infinitary logic $L^k_{\infty\omega}$

Fix $k \in \mathbb{N}$ and $0 < p < 1$. For every sentence $\varphi$ of the infinitary $k$-variable logic $L^k_{\infty\omega}$ in the language of graphs (of any quantifier depth), $\Pr[G(n,p) \models \varphi]$ converges to $0$ or to $1$, with limit $1$ iff the Rado graph satisfies $\varphi$. The same holds for uniform random structures over any finite relational vocabulary without nullary symbols. Consequently every query definable in fixed-point logics (which embed into $\bigcup_k L^k_{\infty\omega}$), such as transitive closure or least-fixed-point logic without order, has a 0-1 law, so EVEN is not expressible in them.

## Proof sketch

In a graph satisfying the extension axioms with at most $k$ parameters, the partial isomorphisms of size at most $k$ form a pebble back-and-forth system with the Rado graph; hence such a graph agrees with the Rado graph on all $L^k_{\infty\omega}$ sentences, and these finitely many extension axioms hold almost surely.

## Depends on

- [Finite-variable logics $\mathrm{FO}^k$ and $L^k_{\infty\omega}$](../finite-variable-logics/finite-variable-logics.md)
- [The uniform random graph $G(n, 1/2)$ and $G(n, p)$](uniform-random-graph.md)
- [The Rado graph is the countable random graph](rado-graph-countable-random-graph.md)

## Proof depends on

- [Pebble games characterize $\mathrm{FO}^k$ and $L^k_{\infty\omega}$](../finite-variable-logics/pebble-games-characterize-finite-variable-logic.md)
- [Extension axioms hold almost surely](extension-axioms-hold-almost-surely.md)

## Sources

- Ph. G. Kolaitis and M. Y. Vardi, "Infinitary Logics and 0-1 Laws", Information and Computation 98(2), 258–294, 1992.
