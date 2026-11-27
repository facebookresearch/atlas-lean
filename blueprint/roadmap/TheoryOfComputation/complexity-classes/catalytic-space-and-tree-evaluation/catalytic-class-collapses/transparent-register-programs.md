# Transparent register programs (Buhrman–Cleve–Koucký–Loff–Speelman)

Fix a ring $\mathcal{R}$ (typically $\mathbb{Z}_p$ for a prime $p$, or $\mathbb{Z}_{2^k}$). A register program over $\mathcal{R}$ with registers $r_1,\dots,r_m$ on inputs $x\in\{0,1\}^n$ is a sequence of instructions of the forms

$$
r_i\leftarrow r_i\pm x_j\cdot r_k,\qquad r_i\leftarrow r_i\pm r_j\cdot r_k,\qquad r_i\leftarrow r_i\pm 1,
$$

with $i\notin\{j,k\}$; every instruction is invertible, so each program $P$ has an inverse $P^{-1}$. A program $P$ **transparently computes** $f:\{0,1\}^n\to\mathcal{R}$ into register $r_o$ if, for every input $x$ and **every** initial register contents $(\tau_1,\dots,\tau_m)$, executing $P$ ends with $r_o=\tau_o+f(x)$ and $r_i=\tau_i$ for all $i\ne o$. Its length is the number of instructions. When the registers are stored on a catalytic tape, a transparent program uses the arbitrary initial content as scratch and leaves it recoverable.

## Depends on

- [Valid catalytic machines with nondeterministic or random choices](valid-catalytic-machines-with-choices.md)

## Sources

- Harry Buhrman, Richard Cleve, Michal Koucký, Bruno Loff and Florian Speelman, "Computing with a Full Memory: Catalytic Space", STOC (2014), ECCC TR14-053.
- James Cook and Ian Mertz, "Catalytic Approaches to the Tree Evaluation Problem", STOC (2020), ECCC TR20-056.
