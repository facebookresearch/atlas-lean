# The group commutator of exponentials approximates the exponential of the commutator

There is a constant $c_1$ such that for all Hermitian matrices $F$ and $G$ with $\| F \|, \| G \| < \delta \le 1$,

$$\big\| e^{iF} e^{iG} e^{-iF} e^{-iG} - e^{-[F, G]} \big\| \le c_1 \delta^3 .$$

Here $e^{-[F, G]} = e^{i \cdot i [F, G]}$, the exponential of the Lie bracket $[iF, iG]$. The bound follows from the power
series of the matrix exponential, the terms of degree at most two cancelling; Dawson and Nielsen give $c_1 \approx 4$.

## Sources

- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 5.2, Lemma 3 ("$d(\exp(iF)\exp(iG)\exp(-iF)\exp(-iG), \exp(i \times i[F, G])) \le c_1 \delta^3$ for some constant $c_1 \approx 4$").
