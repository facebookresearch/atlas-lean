# Semi-ultrafilter covers characterize conondeterministic AND complexity

Call a semifilter $F$ over $U$ a *semi-ultrafilter* if for every set $A\subseteq U$ at least one of $A$ and $U\setminus A$ belongs to $F$. For a Boolean function $f$, let $\rho_{\mathrm{ultra}}(f)$ be the least number of pairs of subsets of $f^{-1}(0)$ covering every semi-ultrafilter over $f^{-1}(0)$ that is above an input in $f^{-1}(1)$ (with the literal sets as supplied sets), and let $\mathrm{coAND}(f)$ be the least number of fan-in-two AND gates of a circuit $V(x,r)$ (negations only on inputs) with $f(x)=1\iff\forall r\,V(x,r)=1$. Then there is an absolute constant $c\ge1$ with

$$
\rho_{\mathrm{ultra}}(f)\le\mathrm{coAND}(f)\le c\cdot\rho_{\mathrm{ultra}}(f).
$$

Equivalently $\mathrm{coAND}(f)$ is the nondeterministic OR complexity of $\neg f$.

## Proof sketch

Both inequalities are due to Karchmer: the lower bound adapts the fusion argument of the deterministic case to circuits with universally quantified auxiliary inputs, and the upper bound turns a cover into a conondeterministic circuit. Cavalar and Oliveira restate the characterization in the set-theoretic cover framework.

## Depends on

- [Semifilters and semifilter (fusion) covers](semifilters-and-fusion-covers.md)
- [Nondeterministic and conondeterministic circuits](../../circuit-models-and-classes/simulations-between-circuit-bases/nondeterministic-and-conondeterministic-circuits.md)

## Proof depends on

- [Semifilter covers lower-bound the AND count of monotone circuits](fusion-covers-lower-bound-and-gates.md)

## Sources

- Mauricio Karchmer, "On Proving Lower Bounds for Circuit Size", Proceedings of the 8th Annual Structure in Complexity Theory Conference, 112–118, 1993.
- Bruno P. Cavalar, Igor C. Oliveira, "Boolean Circuit Complexity and Two-Dimensional Cover Problems", ACM Transactions on Computation Theory, 2025 (Definition 44 and Theorem 45).
