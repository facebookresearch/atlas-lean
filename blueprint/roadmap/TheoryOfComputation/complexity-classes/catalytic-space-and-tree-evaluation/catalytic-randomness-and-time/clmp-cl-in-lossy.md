# Cook–Li–Mertz–Pyne: catalytic logspace reduces to lossy coding (CL ⊆ LOSSY), so LOSSY = P implies CL = CLP

$\mathsf{CL}\subseteq\mathsf{LOSSY}\ (\subseteq\mathsf{ZPP})$. Consequently, if $\mathsf{LOSSY}=\mathsf{P}$ then $\mathsf{CL}\subseteq\mathsf{P}$ and hence $\mathsf{CL}=\mathsf{CLP}$. Since $\mathsf{LOSSY}=\mathsf{P}$ follows from uniform space-time tradeoff lower bounds (Korten), these also imply $\mathsf{CL}=\mathsf{CLP}$.

## Proof sketch

For a $\mathsf{CL}$ machine $M$ ($s = O(\log n)$) and input $x$, set $B = 1$ in Theorem 3.1: the worst-case polynomial-time subroutines $\mathrm{DetComp}_w(1, x)$ and $\mathrm{DetDecomp}_{w' \circ 0}(1, x)$ (using the reversible Euler-tour subroutines $\mathrm{DetWalk}$ and $\mathrm{DetRev}$) are computed by polynomial-size circuits $C_x$ (truncating the final zero bit to drop one bit) and $D_x$ constructible in polynomial time. Any solution $w^*$ of the LossyCode instance $(C_x, D_x)$ satisfies $D_x(C_x(w^*)) \ne w^*$, which means $\mathrm{DetComp}_{w^*}(1, x)$ did not compress $w^*$ and therefore returns $L(x)$ in worst-case polynomial time; simulating $\mathrm{DetComp}_{w^*}(1, x)$ then outputs $L(x)$.

## Depends on

- [The lossy coding problem LossyCode and the classes LOSSY[C]](lossy-code-problem-and-classes.md)
- [Polynomial-time catalytic logspace CLP and zero-error polynomial-time catalytic logspace CZPLP](polynomial-time-catalytic-logspace-classes.md)

## Proof depends on

- [Cook–Li–Mertz–Pyne compress-or-compute: a long-running catalytic computation compresses its own tape](clmp-runtime-compress-or-compute.md)
- [CL ⊆ P iff CL = CLP, and ZPP = P implies CL = CLP](cl-in-p-iff-cl-equals-clp.md)

## Sources

- James Cook, Jiatu Li, Ian Mertz and Edward Pyne, "The Structure of Catalytic Space: Capturing Randomness and Time via Compression", STOC (2025), ECCC TR24-106.
