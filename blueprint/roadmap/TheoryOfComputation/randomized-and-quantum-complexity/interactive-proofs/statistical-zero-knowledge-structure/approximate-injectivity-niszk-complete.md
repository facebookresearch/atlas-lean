# Kaslasi et al.: Approximate Injectivity is NISZK-complete

For $\delta\in[0,1]$, **Approximate Injectivity** $\mathrm{AI}_\delta$ is the promise problem on circuits $C:\{0,1\}^n\to\{0,1\}^m$ with $m\ge n$:

$$
\mathrm{AI}_{\delta,\mathrm{yes}}=\{C:\Pr_x[|C^{-1}(C(x))|>1]<\delta\},\qquad \mathrm{AI}_{\delta,\mathrm{no}}=\{C:\Pr_x[|C^{-1}(C(x))|=1]<\delta\}.
$$

YES instances are injective on all but a $\delta$ fraction of inputs; NO instances have a collision for all but a $\delta$ fraction of inputs. For suitable small $\delta$, $\mathrm{AI}_\delta$ is $\mathsf{NISZK}$-complete under Karp reductions.

## Proof sketch

Hardness is shown by reducing Entropy Approximation to $\mathrm{AI}_\delta$: after flattening, the entropy of a circuit's output determines the typical number of preimages of a sample, and composing the circuit with a many-wise independent hash of appropriate output length makes it nearly injective when the entropy is high and highly non-injective when it is low. Membership: $\mathrm{AI}_\delta$ Karp-reduces back to Entropy Approximation, which is in $\mathsf{NISZK}$.

## Depends on

- [Non-interactive statistical zero knowledge NISZK in the common random string model](niszk-common-random-string.md)

## Proof depends on

- [Goldreich–Sahai–Vadhan: Statistical Difference from Uniform and Entropy Approximation are NISZK-complete](sdu-and-ea-niszk-complete.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Inbar Kaslasi, Guy N. Rothblum, Ron D. Rothblum, Adam Sealfon and Prashant Nalini Vasudevan, "Batch Verification for Statistical Zero Knowledge Proofs", TCC (2020), ECCC TR20-147.
