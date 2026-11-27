# Ground-state condensation for the dilute hard-sphere gas

There are absolute $\epsilon_0,c_0>0$ such that for any exclusion distance $a>0$ and density $\rho>0$ with $\rho a^3<\epsilon_0$, the following holds. Let $N_k\geq1$, $L_k>0$, $N_k,L_k\to\infty$ and $N_k/L_k^3\to\rho$. In the $N$-particle torus of side $L$, use the open region of pair distances strictly larger than $a$, with each squared distance the sum of squared circle distances. The Dirichlet form domain is the closure of the jets of smooth periodic functions supported inside that allowed region in $L^2$ together with the $3N$ coordinate derivatives. The energy is the sum of squared derivative norms. A pure ground vector is a norm-one bosonic (permutation invariant almost everywhere) element of the domain minimizing this energy within that class.

Let $A\psi(Y)=L^{-3/2}\int\psi(x,Y)\,dx$ be the partial inner product with the constant orbital for the first particle, with Lebesgue torus measure. For every sequence of pure ground vectors the lower limit of $\|A\psi\|^2$ is at least $c_0$. For every sequence of positive trace-one operators $T$ on the spatial $L^2$ whose unit vectors in $(\ker T)^\perp$ have ground-vector lifts, the lower limit of $\operatorname{tr}(ATA^*)$ is also at least $c_0$. Ground states and operators are inputs to these implications. No positive-temperature Gibbs or depletion assertion is made.

## Depends on
Jet closure for the hard-core Dirichlet form, the bosonic symmetry constraint, partial inner product with the constant orbital, and the compression trace of a positive trace-one operator (the sum of diagonal entries in a Hilbert basis).

## Proof depends on
The dilute uniform pure-state estimate and passage to the mixed trace using support in the minimizing sector.

## Expansion
Build the torus form and distributional derivative bridge, verify the contraction $A$ and the normalized trace in the comparator model, and isolate the energy and occupation estimates uniform over ground-space vectors and thermodynamic sequences. Do not use an unproved ground-state existence assertion to apply this implication.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HardSphere.lean#L372-L385) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/267.md).
