# Upper Minkowski dimension

Let $X$ be a metric space and $E \subseteq X$. For $\varepsilon > 0$ let $N_\varepsilon(E) \in \mathbb{N} \cup \{\infty\}$ be the internal covering number: the least cardinality of a set $C \subseteq E$ such that every point of $E$ lies within distance at most $\varepsilon$ of some point of $C$ (so $N_\varepsilon(E) = 0$ exactly when $E$ is empty, and $N_\varepsilon(E) = \infty$ when no finite such $C$ exists). For $0 < \varepsilon < 1$ put

$$q(\varepsilon) = \frac{\log N_\varepsilon(E)}{\log(1/\varepsilon)} \in [0,\infty],$$

with $q(\varepsilon) = 0$ when $E$ is empty and $q(\varepsilon) = \infty$ when $N_\varepsilon(E) = \infty$. The upper Minkowski (box-counting) dimension of $E$ is

$$\overline{\dim}_M E = \limsup_{\varepsilon \to 0^+} q(\varepsilon) \in [0,\infty].$$

## Sources

- "Minkowski–Bouligand dimension", Wikipedia (https://en.wikipedia.org/wiki/Minkowski%E2%80%93Bouligand_dimension).
