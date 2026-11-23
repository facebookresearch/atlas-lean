# Free energy of the SK model

For $\beta, h \in \mathbb{R}$ and $N \ge 1$, the free energy per spin of the Sherrington–Kirkpatrick
model is

$$F_N = \frac1N\,\mathbb{E}\log\sum_{\sigma \in \{-1,1\}^N}\exp\Big(H_N(\sigma) + h\sum_{i \le N}\sigma_i\Big),$$

the expectation over the [couplings](coupling-law.md), independent standard Gaussian variables, with
$H_N$ the [Hamiltonian](hamiltonian.md) (Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), left-hand side of (1.14) before the limit).
For $N = 0$ the value is $0$ by convention. Following Talagrand's (1.14), no further minus sign is put
in front of the Hamiltonian in the exponent (the one in (1.1) is part of $H_N$), and $h$ is the
external field.
