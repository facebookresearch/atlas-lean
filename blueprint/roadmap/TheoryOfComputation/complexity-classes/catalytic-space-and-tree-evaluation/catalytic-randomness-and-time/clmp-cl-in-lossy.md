# Cook–Li–Mertz–Pyne: catalytic logspace reduces to lossy coding (CL ⊆ LOSSY), so LOSSY = P implies CL = CLP

$\mathsf{CL}\subseteq\mathsf{LOSSY}\ (\subseteq\mathsf{ZPP})$. Consequently, if $\mathsf{LOSSY}=\mathsf{P}$ then $\mathsf{CL}\subseteq\mathsf{P}$ and hence $\mathsf{CL}=\mathsf{CLP}$. Since $\mathsf{LOSSY}=\mathsf{P}$ follows from uniform space-time tradeoff lower bounds (Korten), these also imply $\mathsf{CL}=\mathsf{CLP}$.

## Proof sketch

For a $\mathsf{CL}$ machine $M$ and input $x$, the compress-or-compute map $(\tau,i)\mapsto(\pi,u)$ and its backward recovery are computed by polynomial-size circuits $C_x,D_x$ constructible in polynomial time, with $C_x$ dropping one bit. Any solution $z=(\tau,i)$ of the LossyCode instance $(C_x,D_x)$ is a content on which compression fails, which forces $M$ to halt within $2^{s+1}=\mathrm{poly}(n)$ steps from $\tau$; simulating $M$ on $\tau$ then yields $M(x)$.

## Depends on

- [The lossy coding problem LossyCode and the classes LOSSY[C]](lossy-code-problem-and-classes.md)
- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)

## Proof depends on

- [Cook–Li–Mertz–Pyne compress-or-compute: a long-running catalytic computation compresses its own tape](clmp-runtime-compress-or-compute.md)
- [CL ⊆ P iff CL = CLP, and ZPP = P implies CL = CLP](cl-in-p-iff-cl-equals-clp.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
