# Kaslasi et al.: Approximate Injectivity is NISZK-complete

For $\delta\in[0,1]$, **Approximate Injectivity** $\mathrm{AI}_\delta$ is the promise problem on circuits $C:\{0,1\}^n\to\{0,1\}^m$ with $m\ge n$:

$$
\mathrm{AI}_{\delta,\mathrm{yes}}=\{C:\Pr_x[|C^{-1}(C(x))|>1]<\delta\},\qquad \mathrm{AI}_{\delta,\mathrm{no}}=\{C:\Pr_x[|C^{-1}(C(x))|=1]<\delta\}.
$$

YES instances are injective on all but a $\delta$ fraction of inputs; NO instances have a collision for all but a $\delta$ fraction of inputs. The two cases are disjoint only for small $\delta$: for $\delta>1/2$ a circuit on two input bits mapping $00,01$ to one output and $10,11$ to two other distinct outputs satisfies both. **Theorem (Kaslasi et al., Corollary 4.6).** For every non-increasing $\delta:\mathbb{N}\to[0,1]$ with $2^{-o(n^{1/4})}<\delta(n)<1/(n+1)-1/\mathrm{poly}(n)$, for example $\delta(n)=1/(n+2)^2$, $\mathrm{AI}_\delta$ is $\mathsf{NISZK}$-complete under Karp reductions.

## Proof sketch

Hardness (Lemma 4.4, for non-increasing $\delta(n)>2^{-o(n^{1/4})}$) is shown by reducing Entropy Approximation to $\mathrm{AI}_\delta$: after flattening, the entropy of a circuit's output determines the typical number of preimages of a sample, and composing the circuit with a many-wise independent hash of appropriate output length makes it nearly injective when the entropy is high and highly non-injective when it is low. Membership (Lemma 4.5, for $\delta(n)<1/(n+1)-1/\mathrm{poly}(n)$): $\mathrm{AI}_\delta$ Karp-reduces back to Entropy Approximation, which is in $\mathsf{NISZK}$.

## Depends on

- [Non-interactive statistical zero knowledge NISZK in the common random string model](niszk-common-random-string.md)

## Proof depends on

- [Goldreich–Sahai–Vadhan: Statistical Difference from Uniform and Entropy Approximation are NISZK-complete](sdu-and-ea-niszk-complete.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Inbar Kaslasi, Guy N. Rothblum, Ron D. Rothblum, Adam Sealfon and Prashant Nalini Vasudevan, "Batch Verification for Statistical Zero Knowledge Proofs", TCC (2020), ECCC TR20-147 (Lemmas 4.4–4.5, Corollary 4.6).
