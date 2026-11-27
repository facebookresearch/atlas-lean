# Transparent register programs (Buhrman–Cleve–Koucký–Loff–Speelman)

Fix a ring $\mathcal{R}$ (typically $\mathbb{Z}_p$ for a prime $p$, or $\mathbb{Z}_{2^k}$). A register program over $\mathcal{R}$ has read-write work registers $r_1,\dots,r_m$ and read-only input registers $x_1,\dots,x_n$, each holding an element of $\mathcal{R}$ (a Boolean input $x\in\{0,1\}^n$ is held as ring elements $0$ and $1$). It is a sequence of instructions of the **standard basis**,

$$
r_i\leftarrow r_i\pm u\times v,
$$

where each of $u$ and $v$ is a constant of $\mathcal{R}$, an input register, or a work register other than $r_i$; an instruction is **skew** if $u$ or $v$ is an input register or a constant. Every instruction is invertible, its inverse exchanging $+$ and $-$, so each program $P = I_1,\dots,I_\ell$ has an inverse $P^{-1} = I_\ell^{-1},\dots,I_1^{-1}$; its length is the number $\ell$ of instructions. Write $\tau_1,\dots,\tau_m$ for the initial register contents. A program $P$ **transparently computes** $f:\{0,1\}^n\to\mathcal{R}$ into register $r_o$ if, for every input $x$ and **every** initial contents $(\tau_1,\dots,\tau_m)$, executing $P$ ends with $r_o=\tau_o+f(x)$; the other registers may end with arbitrary values. It **cleanly** (as well as transparently) computes $f$ into $r_o$ if moreover it ends with $r_i=\tau_i$ for all $i\ne o$. If a program $P$ of length $\ell$ transparently computes $f$ into $r_1$ and does not use the register $r$, then $r\leftarrow r-r_1,\ P,\ r\leftarrow r+r_1,\ P^{-1}$ cleanly computes $f$ into $r$ with length $2\ell+2$. When the registers are stored on a catalytic tape, a clean program uses the arbitrary initial content as scratch and restores it.

## Depends on

- [Valid catalytic machines with nondeterministic or random choices](valid-catalytic-machines-with-choices.md)

## Sources

- Harry Buhrman, Richard Cleve, Michal Koucký, Bruno Loff and Florian Speelman, "Computing with a Full Memory: Catalytic Space", STOC (2014), ECCC TR14-053 (Section 3, Definition 1).
- James Cook and Ian Mertz, "Catalytic Approaches to the Tree Evaluation Problem", STOC (2020), ECCC TR20-056.
