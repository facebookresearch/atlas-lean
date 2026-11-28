# Buhrman–Cleve–Koucký–Loff–Speelman: logspace-uniform TC^1 is contained in catalytic logspace

Every language decided by a logspace-uniform family of threshold circuits of polynomial size and depth $O(\log n)$ is in $\mathsf{CL}$, i.e. $\mathsf{TC}^1\subseteq\mathsf{CL}$; hence $\mathsf{NL}\subseteq\mathsf{CL}$ and $\mathsf{BPL}\subseteq\mathsf{PrL}\subseteq\mathsf{CL}$, the latter since unbounded-error logspace lies in $\mathsf{TC}^1$ (Borodin–Cook–Pippenger, Allender–Ogihara). Scaling the same simulation, for every $s(n)\ge\log n$,

$$
\mathsf{NSPACE}[O(s)]\subseteq\mathsf{CSPACE}\bigl[O(s),2^{O(s)}\bigr]\qquad\text{and}\qquad \mathsf{PrSPACE}[O(s)]\subseteq\mathsf{CSPACE}\bigl[O(s),2^{O(s)}\bigr].
$$

## Proof sketch

Gates are simulated by register programs over $\mathbb{Z}_p$ that cleanly compute them: a threshold gate is expressed through a polynomial in the sum of its inputs, and the products of cleanly computed values are obtained by the commutator-style identity $(\tau_1+a)(\tau_2+b)-\tau_1(\tau_2+b)-(\tau_1+a)\tau_2+\tau_1\tau_2=ab$, which needs the register holding $\tau_2$ (resp. $\tau_1$) to be unchanged while $a$ (resp. $b$) is added and removed; clean sub-programs guarantee this, and any transparent sub-program is first made clean by the page's conversion $r\leftarrow r-r_1,\ P,\ r\leftarrow r+r_1,\ P^{-1}$, which at most doubles its length plus two instructions. So each level multiplies the program length by a constant factor and depth $O(\log n)$ gives polynomial length. The registers, holding $O(\log n)$-bit ring elements, live on a polynomial-length catalytic tape, which the clean overall program restores, and the logspace machine only keeps a program counter; uniformity lets it generate the instructions. The scaled statements follow by applying the construction to the $2^{O(s)}$-size threshold circuits for reachability and for unbounded-error acceptance on the configuration graph.

## Depends on

- [Log-space uniform circuit families](../../time-and-space-complexity-classes/uniform-circuit-family.md)
- [Nondeterministic, bounded-error, unbounded-error and zero-error catalytic space classes](catalytic-resource-classes.md)

## Proof depends on

- [Transparent register programs (Buhrman–Cleve–Koucký–Loff–Speelman)](transparent-register-programs.md)
- [The class NC^k](../../time-and-space-complexity-classes/nck.md)
- [ST-connectivity is NL-complete](../../../completeness-other-classes/directed-s-t-connectivity/stcon-nl-complete.md)
- [NC^1 is contained in L](../../../circuit-complexity/parallel-complexity-class-nc/nc1-subset-logspace.md)

## Sources

- Harry Buhrman, Richard Cleve, Michal Koucký, Bruno Loff and Florian Speelman, "Computing with a Full Memory: Catalytic Space", STOC (2014), ECCC TR14-053.
- Michal Koucký, Ian Mertz, Edward Pyne and Sasha Sami, "Collapsing Catalytic Classes", FOCS (2025), arXiv:2504.08444, ECCC TR25-019.
