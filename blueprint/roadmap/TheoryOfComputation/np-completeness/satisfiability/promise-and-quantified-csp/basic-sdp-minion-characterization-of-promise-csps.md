# Minion characterization of promise CSPs decided by the basic SDP

The basic SDP decides a promise CSP exactly when there is a minion homomorphism from the SDP minion, made of orthogonal vector families summing to a unit vector, to the polymorphism minion of the template; this holds for Boolean and non-Boolean templates.

For a promise template $\Gamma$, the basic SDP decides $\mathrm{PCSP}(\Gamma)$ if every instance on which the basic SDP relaxation is feasible has an assignment weakly satisfying all its constraints.

Let $\mathbb{R}^{\omega}$ be the space of real sequences indexed by $\mathbb{N}$ that are eventually $0$, with $\langle x,y\rangle=\sum_i x_iy_i$. The minion $\mathcal{M}_{\mathrm{SDP}}$ assigns to each non-empty finite set $A$ the set $\mathcal{M}^A_{\mathrm{SDP}}$ of functions $w:A\to\mathbb{R}^{\omega}$ with

$$
\langle w(a),w(a')\rangle=0\ \text{for distinct }a,a'\in A,\qquad\sum_{a\in A}\|w(a)\|_2^2=1,
$$

and to each map $\tau:A\to B$ the minor $(\tau\oslash w)(b)=\sum_{a\in\tau^{-1}(b)}w(a)$, the empty sum being $0$.

**Theorem.** For every promise template $\Gamma$, the basic SDP decides $\mathrm{PCSP}(\Gamma)$ if and only if there is a minion homomorphism $\mathcal{M}_{\mathrm{SDP}}\to\mathrm{Pol}(\Gamma)$.

A similar minion was found concurrently and independently by Ciardo and Živný.

## Expansion

If $\psi:\mathcal{M}_{\mathrm{SDP}}\to\mathrm{Pol}(\Gamma)$ exists, a feasible SDP solution assigns each variable an element of $\mathcal{M}_{\mathrm{SDP}}$ (its orthogonal family of value vectors), and $\psi$ maps these to polymorphisms whose minors behave like sums of orthogonal vectors, which turns the solution into a weakly satisfying assignment. Conversely, by the Barto–Bulín–Krokhin–Opršal theory, a homomorphism exists iff the free structure of $\mathcal{M}_{\mathrm{SDP}}$ for $\Gamma$ admits a weakly satisfying assignment; this free structure is the infinite instance whose variables are unit vectors and whose constraints are vector families meeting the SDP constraints. Feasibility of the SDP on its finite subinstances, after showing that constraint vectors can always be added to a basic SDP solution, and the De Bruijn–Erdős compactness theorem give the assignment. Infinite-dimensional vectors are needed because SDP solutions may require arbitrarily large dimension. For a Boolean folded idempotent template, Lemma 5.6 of the source gives a geometric counterpart: the basic SDP decides $\mathrm{fiPCSP}(\Gamma)$ if and only if for every $n\ge 1$ there is a folded idempotent coloring $f^{(n)}:S^n\to\mathbb{B}$ of the sphere that respects $\Gamma$ with respect to a fixed vector $v_0$.

## Depends on

- [Minions, minion homomorphisms and pp-constructions](../finite-domain-csp-dichotomy/minions-minion-homomorphisms-pp-constructions.md)
- [The polymorphism minion Pol(A,B) of a promise template](polymorphism-minion-of-a-promise-template.md)
- [The basic SDP relaxation of a generalized CSP](../../../pcp-and-inapproximability/sdp-optimality-and-approximation-resistance/basic-sdp-relaxation.md)

## Proof depends on

- [Barto–Bulín–Krokhin–Opršal: minion homomorphisms between polymorphism minions give log-space PCSP reductions](bbko-minion-homomorphism-log-space-reduction.md)

## Sources

- Joshua Brakensiek, Venkatesan Guruswami and Sai Sandeep, "SDPs and Robust Satisfiability of Promise CSP", *Discrete Analysis* 2025:14, https://doi.org/10.19086/da.143808 (expanded version of the STOC 2023 paper), arXiv:2211.08373v5 (Theorem 1.6, Definition 2.15, Lemma 5.6, Definitions 6.1 and 6.3, Lemma 6.6, Theorems 6.7, 6.14 and 6.15).
