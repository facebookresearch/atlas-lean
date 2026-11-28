# Levin reductions (witness-preserving many-one reductions)

A Levin reduction is a Karp reduction that also maps witnesses efficiently in both directions: witnesses of the source instance go forward, and witnesses of the image are pulled back; for promise problems the backward map only needs no-side witnesses.

For a relation $R\subseteq\{0,1\}^*\times\{0,1\}^*$ let $L(R)=\{x:\exists w,\ (x,w)\in R\}$. A triple $(f,g,h)$ of efficiently computable functions is a **Levin reduction** from $R_1$ to $R_2$ if

- for every $(x,w)\in R_1$, $(f(x),g(x,w))\in R_2$, and
- if $(f(x),w)\in R_2$ then $(x,h(x,w))\in R_1$.

Then $f$ is a Karp reduction from $L(R_1)$ to $L(R_2)$. The reduction is **honest** if there is $\delta>0$ with $|f(x)|\ge|x|^{\delta}$ for all large $|x|$. A language is NP-hard under Levin reductions if SAT, with canonical relation $R_{\mathrm{SAT}}=\{(\phi,v):\phi[v]=1\}$, Levin-reduces to it.

A promise problem $(\mathcal Y,\mathcal N)$ comes with relations $R_Y\subseteq R_N$ with $\mathcal Y=L(R_Y)$ and $\mathcal N=L(R_N)$ read as the set of non-no instances. A Levin reduction from $(R^1_Y,R^1_N)$ to $(R^2_Y,R^2_N)$ requires $(f(x),g(x,w))\in R^2_Y$ for $(x,w)\in R^1_Y$, and $(x,h(x,w))\in R^1_N$ whenever $(f(x),w)\in R^2_N$. A **randomized Levin reduction with $\epsilon$-error** lets $f(x;r_1)$ use randomness $r_1\in\{0,1\}^{\ell(|x|)}$ for a polynomial $\ell$, with $g$ and $h$ seeing $r_1$ and $h$ extra randomness $r_2$, such that: for every $(x,w)\in R^1_Y$, with probability at least $1-\epsilon$ over $r_1$, both $(f(x;r_1),g(x,w;r_1))\in R^2_Y$ and, for every $w'$ with $(f(x;r_1),w')\in R^2_N$, $\Pr_{r_2}[(x,h(x,w';r_1,r_2))\in R^1_N]\ge 1-\epsilon$; and for every $x\notin L(R^1_N)$, $\Pr_{r_1}[f(x;r_1)\in L(R^2_N)]\le\epsilon$.

## Expansion

Cook reductions use an oracle, Karp reductions map instances, and Levin's original notion additionally maps witnesses; most natural NP-completeness proofs, including the PCP theorem, are Levin reductions, and constructive applications such as zero-knowledge proofs of knowledge for all of NP need the witness maps. For a gap problem like GapMCSP the natural relations are: $R_Y$ pairs a truth table with a circuit of size at most the yes-threshold computing it, and $R_N$ pairs it with a circuit of size at most the no-threshold.

## Depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Proof depends on

None.

## Sources

- Noam Mazor and Rafael Pass, "Gap MCSP is not (Levin) NP-complete in Obfustopia", *39th Computational Complexity Conference (CCC 2024)*, LIPIcs, 2024, https://doi.org/10.4230/LIPIcs.CCC.2024.36 (Definitions 7, 9 and 10, Remark 8).
