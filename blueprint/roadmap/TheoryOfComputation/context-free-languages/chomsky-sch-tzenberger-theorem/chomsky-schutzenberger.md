# The Chomsky–Schützenberger theorem

The following holds. Let $T$ be an alphabet and $L \subseteq T^*$ a context-free language. Then there are $k \in \mathbb{N}$, a regular language $R$ over the alphabet of $k$ bracket pairs, and a map $\varphi$ sending each bracket letter to a word over $T$, such that

$$L = \{\, \varphi(x_1) \varphi(x_2) \cdots \varphi(x_m) : x_1 x_2 \cdots x_m \in D_k \cap R \,\},$$

where $D_k$ is the Dyck language over $k$ bracket pairs. In other words, $L$ is the image of $D_k \cap R$ under the word homomorphism extending $\varphi$.

## Sources

- N. Chomsky and M. P. Schützenberger, "The algebraic theory of context-free languages", in *Computer Programming and Formal Systems*, North-Holland, 1963, 118-161.
