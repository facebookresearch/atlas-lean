# Valiant–Skyum–Berkowitz–Rackoff depth reduction

Let $f \in \mathbb{F}[x_1, \dots, x_n]$ have degree $d$ and be computed by an arithmetic circuit of size $s$. Then $f$ is computed by a circuit of size $\operatorname{poly}(s, d)$ and depth $O(\log d)$ in which addition gates have unbounded fan-in and multiplication gates have fan-in two, and hence, replacing each addition gate by a binary tree, by an arithmetic circuit of size $\operatorname{poly}(s, d)$ and depth $O(\log d \cdot (\log s + \log d))$ with fan-in two gates. The depth is $O(\log d \cdot \log s)$ when $d \le \operatorname{poly}(s)$. In particular $\mathrm{VP}$ is contained in the class of families computed by polynomial-size circuits of depth $O(\log^2 n)$.

## Proof sketch

Homogenize the circuit, then for every pair of gates $u, v$ define the partial derivative-like polynomial $[u : v]$ obtained by replacing $v$ by a new variable and taking the coefficient. Choosing a frontier of gates of degree between $m$ and $2m$ splits every $[u:v]$ with $\deg u - \deg v \ge 2m$ into a sum of products of two quantities of half the degree difference. Recursing halves the degree at each level, giving $O(\log d)$ levels each realized by an unbounded fan-in sum over frontier gates.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)
- [Valiant's VP versus VNP conjecture](../valiant-s-vp-versus-vnp-conjecture.md)

## Sources

- L. G. Valiant, S. Skyum, S. Berkowitz, C. Rackoff, "Fast parallel computation of polynomials using few processors", SIAM Journal on Computing 12 (1983) 641-644.
