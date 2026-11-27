# Folded Reed-Solomon codes satisfy the dual-decodability and list-recovery conditions

Fix constants $0<c<c'<1$ and a security parameter $\lambda$. Let $q=2^{2\lfloor\log\lambda\rfloor}$, $N=q-1$, folding parameter $m=2^{\lfloor\log\lambda\rfloor}+1$ (which divides $N$), block length $n=N/m=\Theta(\lambda)$ and degree bound $k=\alpha N$ for a constant $\alpha\in(5/6,1)$, and let $C_\lambda$ be the $m$-folded Reed–Solomon code over $\mathbb{F}_q$ of these parameters, a code of length $n$ over the alphabet $\Sigma=\mathbb{F}_q^m$ with $|\Sigma|=2^{\lambda^{\Theta(1)}}$ and $|C_\lambda|\ge 2^{n+\lambda}$. Then $C_\lambda$ satisfies simultaneously: (i) $C_\lambda$ is $(\zeta,\ell,L)$-list recoverable with $\zeta=\Omega(1)$, $\ell=2^{\lambda^{c}}$ and $L=2^{\widetilde O(\lambda^{c'})}$; and (ii) there is an efficient deterministic decoder $\mathrm{Dec}$ for $C_\lambda^\perp$ such that, for $e\in\Sigma^n$ whose coordinates are independent, each equal to $0$ with probability $1/2$ and otherwise uniform on $\Sigma\setminus\{0\}$, $\Pr_e[\forall x\in C_\lambda^\perp:\ \mathrm{Dec}(x+e)=x]=1-2^{-\Omega(\lambda)}$.

## Proof sketch

Item (i) instantiates the list-recovery theorem for folded Reed–Solomon codes of Guruswami and Rudra (in the form of Rudra's thesis, with list size $q^{s}$ for a suitable $s\le m$) with these parameters. For item (ii), the dual of a folded Reed–Solomon code is a folded generalized Reed–Solomon code, which has an efficient list-decoding algorithm (Guruswami–Sudan); for errors drawn from the stated distribution, the list returned contains only the transmitted codeword except with probability $2^{-\Omega(\lambda)}$.

## Depends on

- [Quantum algorithm for codeword search via dual decoding](regev-style-quantum-sampling-of-oracle-good-codewords.md)
- [Classical query lower bound from list recoverability](classical-hardness-from-list-recovery.md)
- [List-recoverable codes](list-recoverable-codes-for-oracle-hardness.md)
- [Reed-Solomon code](../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
- Venkatesan Guruswami, Atri Rudra, "Explicit codes achieving list decoding capacity: error-correction with optimal redundancy", IEEE Transactions on Information Theory 54(1) (2008).
- Venkatesan Guruswami, Madhu Sudan, "Improved decoding of Reed-Solomon and algebraic-geometry codes", IEEE Transactions on Information Theory 45(6) (1999).
