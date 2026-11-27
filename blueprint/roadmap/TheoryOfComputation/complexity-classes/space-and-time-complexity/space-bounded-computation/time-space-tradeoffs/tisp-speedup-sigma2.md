# Kannan's speedup: TISP(t, s) ⊆ Σ₂TIME

Simultaneously time- and space-bounded computation is sped up by two quantifier alternations: whenever $(\sqrt{t}+1)\cdot\bigl(s+(n+1)\log^2 n+\log^2 t\bigr)=O(\tau)$,

$$
\mathsf{TISP}(t,s)\subseteq\Sigma_2\mathsf{TIME}(\tau).
$$

In particular $\mathsf{TISP}(n^{12},n^{2})\subseteq\Sigma_2\mathsf{TIME}(n^{8})$. (The classical sharper form of the lemma gives $\Sigma_2\mathsf{TIME}(\sqrt{t s})$.)

## Proof sketch

The existential player writes $\lfloor\sqrt{t}\rfloor+1$ configurations at distance $\sqrt{t}$ steps; the universal player picks one block; the verifier recomputes that block from its start configuration and compares with the next guess.

## Depends on

- [Simultaneous time–space classes TISP and Σ₂TIME](tisp-and-sigma2-time.md)

## Sources

- Ravi Kannan, "Towards Separating Nondeterminism from Determinism", Mathematical Systems Theory 17(1), 1984.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Lance Fortnow, Richard J. Lipton, Dieter van Melkebeek and Anastasios Viglas, "Time-Space Lower Bounds for Satisfiability", Journal of the ACM 52(6), 2005, Lemma 3.1.
