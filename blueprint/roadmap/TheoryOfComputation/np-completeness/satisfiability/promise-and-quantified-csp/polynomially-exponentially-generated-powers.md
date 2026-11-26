# Polynomially and exponentially generated powers (PGP and EGP)

For a finite algebra $\mathbf{A}$ let $f_{\mathbf{A}}(n)$ be the least size of a generating set of the power $\mathbf{A}^n$. $\mathbf{A}$ has the **polynomially generated powers (PGP)** property if there is a polynomial $p$ with $f_{\mathbf{A}}(n)\le p(n)$ for all $n$, and the **exponentially generated powers (EGP)** property if there are constants $b > 1$ and $C > 0$ with $f_{\mathbf{A}}(n)\ge C\,b^{n}$ for all $n$. For a constraint language $\Gamma$ with all constants, these notions are applied to the idempotent algebra $(D;\mathrm{Pol}(\Gamma))$. PGP is the property that makes universal quantifiers "cheap": with PGP, a universally quantified block can be replaced by polynomially many instantiations (a polynomial-size set of tuples whose closure is everything), which (Chen) reduces $\mathrm{QCSP}(\Gamma)$ in polynomial time to $\mathrm{CSP}(\Gamma)$, so that $\mathrm{QCSP}(\Gamma)\in\mathsf{NP}$.

## Depends on

- [Quantified constraint satisfaction QCSP(Γ) over a finite constraint language](quantified-csp-over-finite-language.md)
- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](../finite-domain-csp-dichotomy/polymorphism-clone-of-a-finite-structure.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- Hubie Chen, "Quantified constraint satisfaction and the polynomially generated powers property", Algebra Universalis 65(3) (2011).
- Dmitriy Zhuk, "The Size of Generating Sets of Powers", arXiv preprint (2015), arXiv:1504.02121.
- Dmitriy Zhuk and Barnaby Martin, "QCSP Monsters and the Demise of the Chen Conjecture", STOC (2020); Journal of the ACM 69(5) (2022).
