# Instance compression of parametric problems

A parametric problem is compressible if a polynomial-time map sends each instance $\langle x,1^n\rangle$ to an equivalent instance of some fixed set whose length is polynomial in the parameter $n$ alone, independent of $|x|$.

A parametric problem is a subset of $\{\langle x,1^n\rangle: x\in\{0,1\}^*, n\in\mathbb{N}\}$. Let $L$ be a parametric problem and $A\subseteq\{0,1\}^*$. $L$ is compressible within $A$ if there are a polynomial $p$ and a polynomial-time computable $f$ such that for every $x$ and $n$,

$$
|f(\langle x,1^n\rangle)|\le p(n)\quad\text{and}\quad\langle x,1^n\rangle\in L\iff f(\langle x,1^n\rangle)\in A.
$$

$L$ is compressible if it is compressible within some $A$, and self-compressible if it is compressible within $L$. Variants: $L$ is probabilistically compressible with error $\varepsilon$ within $A$ if a probabilistic polynomial-time $f$ satisfies both conditions with probability at least $1-\varepsilon(|x|)$; errorless if the error is $0$; compressible with advice $s$ if $f$ may use an advice string of length $s(|x|,n)$ depending only on $|x|$ and $n$ (non-uniformly compressible when $s$ is polynomial in $m=|x|$ and $n$).

Standard parametric versions take the parameter to be the witness size: $\mathrm{SAT}=\{\langle\varphi,1^n\rangle:\varphi\text{ satisfiable with at most }n\text{ variables}\}$, $\mathrm{VC}$ and $\mathrm{Clique}$ with parameter $k\log m$ for graphs of size $m$, and $\text{OR-SAT}=\{\langle\{\varphi_i\},1^n\rangle:\text{some }\varphi_i\text{ is satisfiable and each }|\varphi_i|\le n\}$.

A W-reduction from $L_1$ to $L_2$ is a polynomial-time $f$ with polynomials $p_1,p_2$ such that $f(\langle x,1^{n_1}\rangle)=\langle y,1^{n_2}\rangle$ with $|y|\le p_1(n_1+|x|)$ and $n_2\le p_2(n_1)$, and $f(\langle x,1^{n_1}\rangle)\in L_2$ iff $\langle x,1^{n_1}\rangle\in L_1$. If $L_1$ W-reduces to $L_2$ and $L_2$ is compressible, then $L_1$ is compressible. OR-SAT W-reduces to Clique, Clique to SAT, and SAT to Dominating Set and to Integer Programming, while VC is self-compressible.

## Expansion

Compression generalizes polynomial kernelization from parameterized complexity, which asks for an equivalent instance of the same problem whose size is bounded by a function of the parameter; a polynomial kernel is a self-compression. Fortnow and Santhanam show that [OR-SAT](or-sat-is-not-compressible-unless-np-in-conp-poly.md), and hence SAT, Clique, Dominating Set and Integer Programming, are not compressible unless $\mathsf{NP}\subseteq\mathsf{coNP}/\mathrm{poly}$, which settled the question of Bodlaender, Downey, Fellows and Hermelin and of Harnik and Naor.

## Depends on

- [Parameterized problems](param-problem.md)

## Proof depends on

None.

## Sources

- Lance Fortnow and Rahul Santhanam, "Infeasibility of Instance Compression and Succinct PCPs for NP", *Journal of Computer and System Sciences* 77(1), 2011, pp. 91–106, https://doi.org/10.1016/j.jcss.2010.06.007, read in the authors' version of March 19, 2010 <https://lance.fortnow.com/papers/files/compress.pdf>, whose numbering is cited (Definitions 2.1 to 2.10, Proposition 2.11, Theorem 2.12, Proposition 2.13, Theorem 1.2).
