# Simultaneous time–space classes TISP and Σ₂TIME

For bounds $t,s$, $\mathsf{TISP}(t,s)$ is the class of languages decided by a deterministic multi-tape machine that halts within $O(t(n))$ steps **and** uses $O(s(n))$ work cells on every input of length $n$; thus $\mathsf{TISP}(t,s)\subseteq\mathsf{DTIME}(t)\cap\mathsf{DSPACE}(s)$ and $\mathsf{TISP}(t,t)=\mathsf{DTIME}(t)$. $\Sigma_2\mathsf{TIME}(t)$ is the class of $L$ for which there is a linear-time (in its whole input) deterministic predicate $V$ and constant $c$ with $x\in L\iff\exists u\,\forall v\; V(x,u,v)=1$, $|u|,|v|\le c\,t(|x|)$.

## Depends on

- [Deterministic time classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dtime.md)
- [Deterministic space classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dspace.md)
- [The class $\Sigma_k^p$](../../../time-and-space-complexity-classes/sigma-k.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Lance Fortnow, Richard J. Lipton, Dieter van Melkebeek and Anastasios Viglas, "Time-Space Lower Bounds for Satisfiability", Journal of the ACM 52(6), 2005.
