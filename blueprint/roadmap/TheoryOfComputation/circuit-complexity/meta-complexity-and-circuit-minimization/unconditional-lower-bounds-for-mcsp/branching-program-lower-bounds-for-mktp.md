# Nečiporuk branching program lower bounds for MKTP

Branching programs computing MKTP on $N$-bit inputs need size $\Omega(N^2/\log^2 N)$, and nondeterministic or parity branching programs need size $\Omega(N^{1.5}/\log N)$. These match the best bounds Nečiporuk's method gives for any explicit function.

A *branching program* is a directed acyclic graph with a source and two sinks labeled $0$ and $1$; a computation step queries an input variable $x_i$ and follows an edge labeled $x_i=0$ or $x_i=1$ according to its value. In a *nondeterministic* program a vertex may have any number of outgoing edges, the edges leaving one vertex may query different variables, and unlabeled edges are allowed; it accepts if some path consistent with the input reaches the $1$-sink, and a *parity* program accepts if the number of such paths is odd. The *size* of a branching program is the number of its labeled edges.

**Theorem (Cheraghchi–Hirahara–Myrisiotis–Yoshida).** The size of a branching program computing MKTP is at least $\Omega(N^2/\log^2 N)$. The size of a nondeterministic branching program or a parity branching program computing MKTP is at least $\Omega(N^{1.5}/\log N)$.

**Key estimate.** Let $c>0$ be the universal constant of the source's proof, set $v=4c\log n+4$, and assume, as the source does, that $n=mv$. Partition the $n$ input positions into $m$ blocks $V_1,\dots,V_m$ of size $v$, and let $c_i(f)$ count the distinct subfunctions $f|_{\rho}$ over restrictions $\rho$ with $\rho^{-1}(*)=V_i$. For $f=\mathrm{MKTP}[\theta]$ on $n$-bit inputs with $\theta=n-v+c\log n=n-3c\log n-4$, $c_i(f)=2^{\Omega(n)}$ for every $i\in[m]$; the proof gives $c_i(f)\ge2^{n/3-1}$.

## Expansion

Nečiporuk's method bounds deterministic branching program size by $\Omega(\sum_i\log c_i(f)/\log\log c_i(f))$ and nondeterministic or parity size by $\Omega(\sum_i\sqrt{\log c_i(f)})$; with $m=n/v=\Theta(n/\log n)$ blocks and $\log c_i(f)=\Omega(n)$ these give the two bounds. The key estimate uses only two properties of KT: $K_U(x)\le\mathrm{KT}(x)$ for the bitwise, time-unbounded complexity $K_U$ on the same universal machine, and the fact that a string whose blocks repeat has small KT complexity. The block size $v=4c\log n+4$ makes the subfunction of a random restriction equal to that of any fixed Kolmogorov-random restriction with probability at most $2^{-n/3}$, so many restrictions produce pairwise distinguishable subfunctions, without any pseudorandom generator or hitting set.

## Depends on

- [KT complexity and the minimum KT problem MKTP](../reductions-to-mcsp-and-mktp/kt-complexity-and-mktp.md)

## Proof depends on

None.

## Sources

- Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, Yuichi Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP", *Theory of Computing Systems*, 2022, https://doi.org/10.1007/s00224-022-10113-9; theorem numbers from the conference version, *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2021, https://doi.org/10.4230/LIPIcs.STACS.2021.23 (Section 2.4; Theorems 4, 25 and 26, Definition 24, Lemma 28 and the proof of Theorem 26).
