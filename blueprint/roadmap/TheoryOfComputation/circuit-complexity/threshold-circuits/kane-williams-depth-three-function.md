# The Kane–Williams function: hardness for depth-two threshold circuits

Let the input consist of a message $x\in\{0,1\}^n$ and $k$ blocks of $\ell$ bits with block parities $z\in\{0,1\}^k$, and let $r:\{0,1\}^k\to\{0,1\}^n$ list rows of a $\delta$-biased set. The *Kane–Williams function* is $B(x,a)=\langle r_z,x\rangle\bmod2$; it is computed by depth-three threshold circuits of polynomial size. For $\gamma^2>\delta$, at most $1/(\gamma^2-\delta)$ rows $r_z$ can have correlation at least $\gamma$ with any fixed Boolean function of $x$; consequently depth-two weighted threshold circuits with few gates (or wires), in the regime of the Kane–Williams random-restriction bounds, have only small correlation with $B$, so the superlinear gate and superquadratic wire lower bounds hold even for approximating $B$.

## Proof sketch

After a random restriction most parities $z$ remain controlled by few live variables, so a small circuit becomes a small depth-two circuit on the message; small bias of the rows implies that at most $1/(\gamma^2-\delta)$ rows can correlate well with any fixed function of $x$, which contradicts correlation with $B$.

## Depends on

- [Depth-two weighted threshold circuits](depth-two-weighted-threshold-circuits.md)

## Proof depends on

- [Kane–Williams random restriction lemmas for linear threshold functions](kane-williams-random-restriction-lemmas.md)

## Sources

- Daniel M. Kane, Ryan Williams, "Super-Linear Gate and Super-Quadratic Wire Lower Bounds for Depth-Two and Depth-Three Threshold Circuits", Proceedings of the Forty-Eighth Annual ACM Symposium on Theory of Computing (STOC 2016), 2016.
