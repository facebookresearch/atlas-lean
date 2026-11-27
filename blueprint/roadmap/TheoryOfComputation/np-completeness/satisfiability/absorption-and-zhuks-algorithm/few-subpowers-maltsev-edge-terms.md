# Few subpowers, Mal'tsev operations and edge terms

For a finite algebra $\mathbf{A}$ let $s_{\mathbf{A}}(n)=\log_2|\mathrm{Sub}(\mathbf{A}^n)|$, where $\mathrm{Sub}(\mathbf{A}^n)$ is the set of subuniverses of $\mathbf{A}^n$. $\mathbf{A}$ has **few subpowers** if $s_{\mathbf{A}}(n)$ is bounded by a polynomial in $n$ (the trivial bound is $|A|^n$). A ternary operation $p$ is **Mal'tsev** if $p(y,y,x)=p(x,y,y)=x$. For $k\ge 2$ a $(k+1)$-ary operation $e$ is a **$k$-edge operation** if it satisfies

$$
e(y,y,x,x,\dots,x)=e(y,x,y,x,\dots,x)=x,\qquad e(x,\dots,x,\underset{i}{y},x,\dots,x)=x\ \ (4\le i\le k+1).
$$

A Mal'tsev operation yields a 2-edge operation, and a $k$-ary near-unanimity operation yields a $k$-edge operation.

## Depends on

- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](../finite-domain-csp-dichotomy/polymorphism-clone-of-a-finite-structure.md)

## Sources

- Joel Berman, Paweł Idziak, Petar Marković, Ralph McKenzie, Matthew Valeriote and Ross Willard, "Varieties with few subalgebras of powers", Transactions of the American Mathematical Society 362(3) (2010).
- Paweł Idziak, Petar Marković, Ralph McKenzie, Matthew Valeriote and Ross Willard, "Tractability and learnability arising from algebras with few subpowers", SIAM Journal on Computing 39(7) (2010).
- Andrei Bulatov and Víctor Dalmau, "A simple algorithm for Mal'tsev constraints", SIAM Journal on Computing 36(1) (2006).
