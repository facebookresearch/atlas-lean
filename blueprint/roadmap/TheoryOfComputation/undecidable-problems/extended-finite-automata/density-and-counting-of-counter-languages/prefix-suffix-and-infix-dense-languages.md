# Prefix-dense, suffix-dense and infix-dense languages

A language over $\Sigma$ is dense if every word of $\Sigma^*$ is an infix of one of its words; prefix-density and suffix-density ask the same of prefixes and suffixes.

**Definition.** For $L \subseteq \Sigma^*$ let

$$
\mathrm{pref}(L) = \{ w : wx \in L \text{ for some } x \in \Sigma^* \}, \qquad \mathrm{suff}(L) = \{ w : xw \in L \text{ for some } x \in \Sigma^* \},
$$

$$
\mathrm{inf}(L) = \{ w : xwy \in L \text{ for some } x, y \in \Sigma^* \}.
$$

For an operation $\varrho$ on languages over $\Sigma$, the language $L$ is *$\varrho$-dense* if $\varrho(L) = \Sigma^*$. Thus $L$ is *prefix-dense* if $\mathrm{pref}(L) = \Sigma^*$, *suffix-dense* if $\mathrm{suff}(L) = \Sigma^*$, and *infix-dense*, or simply *dense*, if $\mathrm{inf}(L) = \Sigma^*$.

Density is a notion from the theory of codes. With $\varrho$ the identity, $\varrho$-density is universality.

## Depends on

None.

## Proof depends on

None.

## Sources

- J. Eremondi, O. H. Ibarra and I. McQuillan, "On the Density of Context-Free and Counter Languages", *International Journal of Foundations of Computer Science* 29(2):233–250, 2018, doi:[10.1142/S0129054118400051](https://doi.org/10.1142/S0129054118400051); numbering of arXiv:1903.03001v1: the prefix, suffix, infix and outfix operations and the definition of $\varrho$-density in Sections 1 and 2.
