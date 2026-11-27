# Approximate balanced group commutators in $SU(d)$

Let $d \ge 2$. There are constants $c', c'' > 0$ and $\varepsilon_1 > 0$, depending on $d$, such that every
$U \in SU(d)$ with $\| I - U \| < \varepsilon \le \varepsilon_1$ has unitaries $V, W \in SU(d)$ with

$$\| V W V^{*} W^{*} - U \| < c' \varepsilon^{3/2} \qquad\text{and}\qquad \| I - V \|, \| I - W \| < c'' \sqrt{\varepsilon} .$$

Proof: write $U = e^{-iH}$ with $H$ traceless Hermitian and $\| H \| = \| I - U \| + O(\| I - U \|^3)$. By the
[commutator lemma](traceless-hermitian-matrix-as-a-commutator.md) applied to $H$ there are traceless Hermitian $F, G$ with
$[F, G] = iH$ and norms at most $c'' \sqrt{\varepsilon}$, where $c'' \approx d^{1/4} ((d - 1)/2)^{1/2}$. With
$V = e^{iF}$ and $W = e^{iG}$, which lie in $SU(d)$ because $\det e^{iF} = e^{i \operatorname{tr} F} = 1$ and likewise for $G$, the [exponential estimate](group-commutator-of-exponentials-approximates-the-exponential-of-the-commutator.md)
gives $\| V W V^{*} W^{*} - e^{-[F, G]} \| \le c_1 (c'' \sqrt{\varepsilon})^3$, and $e^{-[F, G]} = e^{-iH} = U$.

## Proof depends on

- [A traceless Hermitian matrix is a commutator of small Hermitian matrices](traceless-hermitian-matrix-as-a-commutator.md)
- [The group commutator of exponentials approximates the exponential of the commutator](group-commutator-of-exponentials-approximates-the-exponential-of-the-commutator.md)

## Sources

- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 5.1 (the qudit algorithm needs $d(VWV^\dagger W^\dagger, \Delta) < c_{gc'} \epsilon^{3/2}$ and $d(I, V), d(I, W) < c_{gc''} \sqrt{\epsilon}$) and Section 5.2, equation (33). The source writes $U = \exp(iH)$ with $[F, G] = iH$; with its Lemma 3 the commutator then approximates $\exp(-iH)$, so the sign of $H$ is chosen here to make the commutator approximate $U$.
