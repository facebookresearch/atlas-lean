# Naturality of the connecting homomorphism

Let $G$ be a profinite group and let

$$
\begin{array}{ccccccccc}
0 & \to & A & \xrightarrow{i} & B & \xrightarrow{j} & C & \to & 0 \\
  &     & \downarrow f & & \downarrow h & & \downarrow g & & \\
0 & \to & A' & \xrightarrow{i'} & B' & \xrightarrow{j'} & C' & \to & 0
\end{array}
$$

be a commutative diagram of discrete $G$-modules with exact rows. Then for every $n \ge 0$ the connecting
homomorphisms of the [long exact cohomology sequences](long-exact-cohomology-sequence.md) of the two rows satisfy

$$
\delta \circ g_* = f_* \circ \delta \colon H^n(G, C) \longrightarrow H^{n+1}(G, A').
$$

Together with the long exact sequence, this makes $(H^n(G, -))_{n \ge 0}$ an exact $\delta$-functor on discrete
$G$-modules.

## Depends on

- [The long exact cohomology sequence](long-exact-cohomology-sequence.md), for the connecting homomorphisms
  $\delta$

## Proof depends on

- [The long exact cohomology sequence](long-exact-cohomology-sequence.md), for the cochain-level description of
  $\delta$, from which the identity follows directly

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter I, §3, Proposition (1.3.3) and its
  proof, and the definition of an exact $\delta$-functor that follows it, pp. 28–29.
