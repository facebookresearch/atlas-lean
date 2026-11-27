# Nečiporuk branching program lower bounds for MKTP

Branching programs computing MKTP on $N$-bit inputs need size $\Omega(N^2/\log^2 N)$, and nondeterministic or parity branching programs need size $\Omega(N^{1.5}/\log N)$. These match the best bounds Nečiporuk's method gives for any explicit function.

A *branching program* is a directed acyclic graph with a source and two sinks labeled $0$ and $1$, whose inner nodes query an input variable and branch on its value; size counts nodes. In a *nondeterministic* program some edges are unlabeled guesses and the program accepts if some path reaches the $1$-sink; a *parity* program accepts if the number of such paths is odd.

**Theorem (Cheraghchi–Hirahara–Myrisiotis–Yoshida).** The size of a branching program computing MKTP is at least $\Omega(N^2/\log^2 N)$. The size of a nondeterministic branching program or a parity branching program computing MKTP is at least $\Omega(N^{1.5}/\log N)$.

**Key estimate.** Partition the $n$ input positions into $m$ blocks $V_1,\dots,V_m$ of size $v=O(\log n)$, and let $c_i(f)$ count the distinct subfunctions $f|_{\rho}$ over restrictions $\rho$ with $\rho^{-1}(*)=V_i$. For $f=\mathrm{MKTP}[\theta]$ on $n$-bit inputs with $\theta=n-3c\log n-4$, where $c>0$ is a universal constant, $c_i(f)=2^{\Omega(n)}$ for every $i\in[m]$.

## Expansion

Nečiporuk's method bounds deterministic branching program size by $\Omega(\sum_i\log c_i(f)/\log\log c_i(f))$ and nondeterministic or parity size by $\Omega(\sum_i\sqrt{\log c_i(f)})$; with $m=\Theta(n/\log n)$ blocks and $\log c_i(f)=\Omega(n)$ these give the two bounds. The key estimate uses only two properties of KT: $K(x)\le\mathrm{KT}(x)$, and the fact that a string whose blocks repeat has small KT complexity. Many restrictions therefore produce pairwise distinguishable subfunctions, without any pseudorandom generator or hitting set.

## Depends on

- [KT complexity and the minimum KT problem MKTP](../reductions-to-mcsp-and-mktp/kt-complexity-and-mktp.md)

## Proof depends on

None.

## Sources

- Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, Yuichi Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP", *Theory of Computing Systems*, 2022, https://doi.org/10.1007/s00224-022-10113-9; theorem numbers from the conference version, *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2021, https://doi.org/10.4230/LIPIcs.STACS.2021.23 (Theorems 4, 25 and 26, Definition 24).
