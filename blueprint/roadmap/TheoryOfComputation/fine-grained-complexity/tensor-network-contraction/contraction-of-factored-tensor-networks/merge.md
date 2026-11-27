# Merging vertices of a factored tensor network

Let $N$ be a factored tensor network on a finite linearly ordered vertex set $J$ with states in
$\sigma$ and labels in $\tau$, let $\chi : J \to J'$ be a map to a linear order $J'$ (its fibres
are the classes), and let $s_0 \in \sigma$ and $t_0 \in \tau$ be defaults. The merged network on
$J'$ has states the maps $z : J \to \sigma$ and labels the maps $t : J \times J \to \tau$, with:

- allowed states at $G$: the maps $z$ with $z(a) \in S_a$ when $\chi(a) = G$ and $z(a) = s_0$
  otherwise;
- weight $W_G(z) = \prod_{\chi(a) = G} W_a(z(a)) \cdot \prod I_{a,b}(z(a), z(b))$, the second
  product over $a < b$ with $\chi(a) = \chi(b) = G$, where $I$ is the interaction of $N$;
- label set at $(G, G')$: the maps $t$ with $t(a, b)$ in the label set of $\{a, b\}$ when
  $\chi(a) = G$ and $\chi(b) = G'$, and $t(a, b) = t_0$ otherwise;
- factor $f_{G,G'}(z, t) = \prod f_{a,b}(z(a), t(p))$ over pairs $(a, b)$ with $\chi(a) = G$ and
  $\chi(b) = G'$, where $p = (a, b)$ if $G < G'$ and $p = (b, a)$ otherwise;
- capacity $c_{G,G'} = \sum c_{a,b}$ over pairs $(a, b)$ with $\chi(a) = G$ and $\chi(b) = G'$.
