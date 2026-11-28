# Learning from a distinguisher for the Nisan-Wigderson generator

In the setting of the one-run reconstruction, let the test $D$ have advantage at least $\varepsilon > 0$ against $\mathrm{NW}^f$ for every $f$ in a class $C$, and let $\eta > 0$, $k$, $t$ satisfy $\varepsilon/(2m) \le 1$, $\ln(2/\eta) \le \frac{\varepsilon}{2m}k$ and $8\ln(4k/\eta) \le t\left(\frac{\varepsilon}{2m}\right)^2$. Then best-of-$k$ selection on $t$ sample points over the reconstruction learns $C$ with error $\frac12 - \frac{\varepsilon}{4m}$ and confidence $1 - \eta$, makes at most $km2^a + t$ queries, and every hypothesis has the circuit-size bound of a single run. A test accepting at least a $\delta > 0$ fraction of strings but no generator output for any $f \in C$ yields this with $\varepsilon = \delta$.

## Proof sketch

Apply best-of-$k$ selection with per-run failure probability $1 - \varepsilon/(2m)$ and deviation $\theta = \varepsilon/(8m)$: all runs fail with probability $(1 - \varepsilon/(2m))^k \le \eta/2$, and the estimation failure $2ke^{-2t\theta^2}$ is at most $\eta/2$ under the stated condition.

## Depends on

- [Nisan-Wigderson reconstruction as a membership-query weak learner (one run)](nisan-wigderson-reconstruction-weak-learner.md)
- [Best-of-k selection boosts the confidence of a membership-query learner](../../circuit-complexity/learning-under-the-uniform-distribution/best-of-k-confidence-boosting.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
- Noam Nisan and Avi Wigderson, "Hardness vs Randomness", Journal of Computer and System Sciences 49(2), 1994.
