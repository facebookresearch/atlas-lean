# Resilient monotone AC0 functions stay resilient under bounded independence

For $f:\{0,1\}^n\to\{0,1\}$ and a set $Q$ of coordinates, the *influence* $I_{Q,D}(f)$ of the coalition $Q$ under a distribution $D$ on the remaining coordinates is the probability that $f$ is still undetermined (not constant as a function of $x_Q$) after the coordinates outside $Q$ are drawn from $D$; $I_Q(f)$ is the case of the uniform distribution, and $I_q(f)=\max_{|Q|=q}I_Q(f)$. The function is *$(q,\varepsilon)$-resilient* if $I_q(f)\le\varepsilon$, and *$t$-independent $(q,\varepsilon)$-resilient* if $I_{Q,D}(f)\le\varepsilon$ for every $|Q|=q$ and every $t$-wise independent $D$. For monotone $f$, $I_Q(f)=\Pr_x[f(1_Q,x)=1]-\Pr_x[f(0_Q,x)=1]$.

There is a constant $b>0$ such that the following holds. Let $C$ be a monotone circuit over the unbounded fan-in basis of depth $d$ and size $m$ with $|\mathbb{E}_{x\sim U_n}C(x)-\tfrac12|\le\varepsilon_1$, and let $q>0$ satisfy $I_q(C)\le\varepsilon_2$. If $t\ge b(\log(5m/\varepsilon_3))^{3d+6}$, then $C$ is $t$-independent $(q,\varepsilon_2+\varepsilon_3)$-resilient, and $|\mathbb{E}_{x\sim D}C(x)-\tfrac12|\le\varepsilon_1+\varepsilon_3$ for every $t$-wise independent distribution $D$ on $\{0,1\}^n$.

## Proof sketch

For a coalition $Q$ let $C_0$ and $C_1$ be $C$ with the coordinates in $Q$ set to all zeros and all ones. Because $C$ is monotone, $C$ is undetermined on $y$ exactly when $C_1(y)=1$ and $C_0(y)=0$, so the indicator $E_Q=C_1\wedge\neg C_0$ has $\mathbb{E}_U E_Q=I_Q(C)$ and $\mathbb{E}_D E_Q=I_{Q,D}(C)$. It is computed by a constant-depth circuit of size $4m+3$ whose depth can be brought down to $d+1$. The Braverman–Tal theorem, that $O(\log(m/\varepsilon))^{3d+3}$-wise independence $\varepsilon$-fools circuits of depth $d$ and size $m$, applied at depth $d+1$ transfers both the influence and the bias from the uniform distribution to $D$.

## Depends on

- [k-wise independent and almost k-wise independent distributions](k-wise-independent-distributions.md)
- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)
- [Monotone circuits](../../../complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)

## Proof depends on

- [Braverman: polylogarithmic independence fools AC0](braverman-polylog-independence-fools-ac0.md)

## Sources

- Eshan Chattopadhyay, David Zuckerman, "Explicit Two-Source Extractors and Resilient Functions", Annals of Mathematics 189(3), 2019 (Definitions 1.8–1.9 and Theorem 4.1 in the ECCC version, TR15-119).
- Mark Braverman, "Polylogarithmic Independence Fools AC^0 Circuits", Journal of the ACM 57(5), Article 28, 2010.
- Avishay Tal, "Tight Bounds on the Fourier Spectrum of AC^0", 32nd Computational Complexity Conference (CCC 2017), LIPIcs 79, 2017.
