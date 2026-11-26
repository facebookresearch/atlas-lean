# Promise class PCP(r, q)

A promise problem $\Pi = (\Pi_{\mathrm{yes}}, \Pi_{\mathrm{no}})$ over binary strings, $\Pi_{\mathrm{yes}} \cap \Pi_{\mathrm{no}} = \emptyset$, belongs to $\mathrm{PromisePCP}(r(n), q(n))$ if there is a nonadaptive verifier $V$ computable in polynomial time that, on input $x$ of length $n$ and random string $\rho \in \{0,1\}^{O(r(n))}$, computes at most $O(q(n))$ proof positions and a verdict on the bits read, such that:
- (completeness) for every $x \in \Pi_{\mathrm{yes}}$ some proof $\pi$ is accepted with probability $1$;
- (soundness) for every $x \in \Pi_{\mathrm{no}}$ every proof $\pi$ is accepted with probability at most $1/2$.

No condition is imposed on inputs outside $\Pi_{\mathrm{yes}} \cup \Pi_{\mathrm{no}}$. For a language $L$ (the promise $\Pi_{\mathrm{no}} = \overline{L}$) this is the class $\mathrm{PCP}(r, q)$ with perfect completeness.

## Depends on

- [Probabilistically checkable proofs](../../complexity-classes/time-and-space-complexity-classes/pcp.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
