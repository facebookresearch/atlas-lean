# The long exact sequence of continuous cohomology

Let $G$ be a profinite group and let

$$
0 \longrightarrow A \xrightarrow{\ \alpha\ } B \xrightarrow{\ \beta\ } C \longrightarrow 0
$$

be a short exact sequence of topological $G$-modules such that the topology of $A$ is induced by that of $B$ and
$\beta$ has a continuous section, a continuous map $s \colon C \to B$ with $\beta \circ s = \mathrm{id}_C$, not
necessarily a homomorphism. Then there are canonical connecting homomorphisms
$\delta \colon H^n_{\mathrm{cts}}(G, C) \to H^{n+1}_{\mathrm{cts}}(G, A)$ of
[continuous cohomology](continuous-cohomology.md), and the sequence

$$
0 \to A^G \to B^G \to C^G \xrightarrow{\delta} H^1_{\mathrm{cts}}(G, A) \to \cdots \to H^n_{\mathrm{cts}}(G, A)
\to H^n_{\mathrm{cts}}(G, B) \to H^n_{\mathrm{cts}}(G, C) \xrightarrow{\delta} H^{n+1}_{\mathrm{cts}}(G, A) \to \cdots
$$

is exact. This applies in particular when $A$ is an open submodule of $B$ and $C = B/A$ carries the quotient
topology, which is discrete.

## Depends on

- [Continuous cohomology](continuous-cohomology.md), for $H^n_{\mathrm{cts}}(G, -)$

## Proof depends on

- [Continuous cohomology](continuous-cohomology.md), for the cochain complexes: the hypotheses make
  $0 \to C^\bullet_{\mathrm{cts}}(G, A) \to C^\bullet_{\mathrm{cts}}(G, B) \to C^\bullet_{\mathrm{cts}}(G, C) \to 0$ exact,
  the section lifting continuous cochains, and the snake lemma applies as for discrete modules

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition, version 2.3
  (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, Lemma (2.7.2) and the note
  after it, p. 137.
