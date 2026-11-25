# Multigraded base change data

Let $K$ be a field, let $R = K[x_1, \dots, x_n]$,
and let $M$ be a $\mathbb{Z}^n$-graded $R$-module with a multigraded free resolution
$P_\bullet \to M$. Write $K \otimes_R P_\bullet$ for its base change along the
augmentation $R \to K$ and $(K \otimes_R P_i)_\beta$ for the degree-$\beta$ piece of its
$i$th term. Multigraded base change data for $P_\bullet$ consist of: for each
$i \in \mathbb{N}$, a decomposition of $K \otimes_R P_i$ as the internal direct sum of the
pieces $(K \otimes_R P_i)_\beta$ over $\beta \in \mathbb{Z}^n$, such that for all $i$ and
$\beta$ the differential $K \otimes_R P_{i+1} \to K \otimes_R P_i$ maps
$(K \otimes_R P_{i+1})_\beta$ into $(K \otimes_R P_i)_\beta$; and, for each
$\alpha \in \mathbb{Z}^n$, an $\mathbb{N}$-indexed chain complex $C^\alpha$ of
$K$-vector spaces with a chain map $C^\alpha \to K \otimes_R P_\bullet$ whose $i$th
component is injective with image $(K \otimes_R P_i)_\alpha$ for every $i$, such that
every homology $H_i(C^\alpha)$ exists and is finite-dimensional over $K$.
