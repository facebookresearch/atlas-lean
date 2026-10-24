---
article_id: af_90e149d069f1416d95575bff
declaration: theorem
origin: cited
statement: formalized
lean: ContinuousRep.derivedRep_bracket
---

# Proposition 4.13

Let $(V, \pi)$ be a continuous representation of a Lie group $G$ with $\mathfrak{g}=\operatorname{Lie}(G)$. Let $v \in V^{\infty}$. Then we have a linear map $\pi_{*, v}: \mathfrak{g} \rightarrow V^{\infty}$ given by $\pi_{*, v}(b)=\left.\frac{d}{d t}\right|_{t=0} \pi\left(e^{t b}\right) v$. This defines a Lie algebra homomorphism $\pi_{*}: \mathfrak{g} \rightarrow \operatorname{End}_{\mathbb{C}}\left(V^{\infty}\right)$ given by $\pi_{*}(b) v:=\pi_{*, v}(b)$.

## Depends on

- [Definition 1.2](../section-1/001-definition-1-2.md)
- [Definition 4.11](021-definition-4-11.md)

## Sources

- [MIT 18.757 Representations of Lie Groups (Fall 2023), Section 4.4](../../../../../sources/v1/LieGroups.md)
