# Nečiporuk branching program lower bounds for MKTP

Branching programs computing MKTP on $N$-bit inputs need size $\Omega(N^2/\log^2 N)$, and nondeterministic or parity branching programs need size $\Omega(N^{1.5}/\log N)$. These match the best bounds Nečiporuk's method gives for any explicit function.

A *branching program* is a directed acyclic graph with a source and two sinks labeled $0$ and $1$; a computation step queries an input variable $x_i$ and follows an edge labeled $x_i=0$ or $x_i=1$ according to its value. In a *nondeterministic* program a vertex may have any number of outgoing edges, the edges leaving one vertex may query different variables, and unlabeled edges are allowed; it accepts if some path consistent with the input reaches the $1$-sink, and a *parity* program accepts if the number of such paths is odd. The *size* of a branching program is the number of its labeled edges.

**Theorem (Cheraghchi–Hirahara–Myrisiotis–Yoshida).** The size of a branching program computing MKTP is at least $\Omega(N^2/\log^2 N)$. The size of a nondeterministic branching program or a parity branching program computing MKTP is at least $\Omega(N^{1.5}/\log N)$.

Here KT and MKTP are as on the KT page: symbol-output convention, and the efficient universal machine whose simulation guarantee includes linear time overhead for two-tape machines.

**Key estimate.** Let $c>0$ be the universal constant of the source's proof, set $v=4c\log n+4$, and assume, as the source does, that $n=mv$. Partition the $n$ input positions into $m$ blocks $V_1,\dots,V_m$ of size $v$, and let $c_i(f)$ count the distinct subfunctions $f|_{\rho}$ over restrictions $\rho$ with $\rho^{-1}(*)=V_i$. For $f=\mathrm{MKTP}[\theta]$ on $n$-bit inputs with $\theta=n-v+c\log n=n-3c\log n-4$, $c_i(f)=2^{\Omega(n)}$ for every $i\in[m]$; the proof gives $c_i(f)\ge2^{n/3-1}$.

## Expansion

Nečiporuk's method bounds deterministic branching program size by $\Omega(\sum_i\log c_i(f)/\log\log c_i(f))$ and nondeterministic or parity size by $\Omega(\sum_i\sqrt{\log c_i(f)})$; with $m=n/v=\Theta(n/\log n)$ blocks and $\log c_i(f)=\Omega(n)$ these give the two bounds. The key estimate uses only two properties of KT, properties 1 and 2 in the source's proof of Theorem 26. First, $K_U(x)\le\mathrm{KT}(x)$ for the bitwise, time-unbounded complexity $K_U$ on the same universal machine; under the symbol-output convention a KT description halts with the correct symbol on every index, the end marker included, so it is also a $K_U$ description. Second, if $\rho_1,\dots,\rho_m\in\{0,1\}^v$ and $\rho_i=\rho_j$ for some $i\ne j$, then $\mathrm{KT}(\rho_1\cdots\rho_m)\le(m-1)v+O(\log n)$, because each bit of $\rho_1\cdots\rho_m$ is computed in time $O(\log n)$ from the ordered sequence of the $m-1$ surviving blocks $(\rho_1,\dots,\rho_{j-1},\rho_{j+1},\dots,\rho_m)$ together with both indices $i$ and $j$ (which identify which surviving block to copy and where to insert it, taking $O(\log n)$ bits). This $O(\log n)$ time per bit is what fits the additive $c\log n$ in the threshold $\theta$, and it is where the efficiency of the universal machine enters: the source's footnote 7 notes that a slower universal machine, needing polylogarithmic time per bit, yields only an $n^2/\mathrm{polylog}(n)$ lower bound. The block size $v=4c\log n+4$ makes the subfunction of a random restriction equal to that of any fixed Kolmogorov-random restriction with probability at most $2^{-n/3}$, so many restrictions produce pairwise distinguishable subfunctions, without any pseudorandom generator or hitting set.


Known unstated proof prerequisites needed before this node is ready for formalization:

- Nečiporuk's method for deterministic, nondeterministic and parity branching programs (Cheraghchi et al. Theorem 25)

## Depends on

- [KT complexity and the minimum KT problem MKTP](../reductions-to-mcsp-and-mktp/kt-complexity-and-mktp.md)

## Proof depends on

None.

## Sources

- Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, Yuichi Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP", *Theory of Computing Systems*, 2022, https://doi.org/10.1007/s00224-022-10113-9; theorem numbers from the conference version, *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2021, https://doi.org/10.4230/LIPIcs.STACS.2021.23 (Section 2.4; Theorems 4, 25 and 26, Definition 24, Lemma 28, and the proof of Theorem 26 with its properties 1 and 2 and footnotes 6 and 7).
- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, https://doi.org/10.1137/050628994 (Proposition 5 of the journal version, for the efficient universal machine and its linear-time simulation of two-tape machines).
