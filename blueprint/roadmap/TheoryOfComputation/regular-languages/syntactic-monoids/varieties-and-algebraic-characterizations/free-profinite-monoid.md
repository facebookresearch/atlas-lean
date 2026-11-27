# The profinite metric and the free profinite monoid

Let $A$ be a finite alphabet. A monoid $M$ *separates* words $u, v \in A^*$ if some morphism from $A^*$ onto $M$ takes different values on them; any two distinct
words are separated by some finite monoid. Put $r(u, v) = \min\{|M| : M \text{ separates } u \text{ and } v\}$ and $d(u, v) = 2^{-r(u, v)}$ (with $2^{-\infty} = 0$). Then $d$ is an
ultrametric on $A^*$ with $d(uw, vw) \le d(u, v)$ and $d(wu, wv) \le d(u, v)$, and $(A^*, d)$ is totally bounded. Its completion $\widehat{A^*}$ is the set of *profinite
words* on $A$; it is compact, and the product of $A^*$, being uniformly continuous, extends to a continuous product on $\widehat{A^*}$, making it the *free
profinite monoid* on $A$.

## Sources

- J.-É. Pin, *Mathematical Foundations of Automata Theory*, lecture notes, version of March 24, 2025, <https://www.irif.fr/~jep/PDF/MPRI/MPRI.pdf>: Section X.2.1 (separation, Proposition X.2.2, the definition of $r$ and $d$, Propositions X.2.3 and X.2.6) and Section X.2.2 (the completion, Theorem X.2.8 and Proposition X.2.9).
