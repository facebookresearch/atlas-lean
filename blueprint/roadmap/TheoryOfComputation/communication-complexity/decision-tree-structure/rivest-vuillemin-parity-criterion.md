# Rivest–Vuillemin parity criterion for evasiveness

Let $f : \{0,1\}^n \to \{0,1\}$ and let $e$ and $o$ be the numbers of inputs of even and odd Hamming weight on which $f = 1$. If $e \ne o$ (for $n \ge 1$ this is equivalent to the top Fourier coefficient $\hat f([n])$ of $f$ read as $\pm1$ being nonzero, since $\hat f([n]) = -2^{1-n}(e-o)$; for $n=0$ the equivalence fails, as the constant $0$ has $e=o=0$ but $\hat f(\varnothing)=1$), then every decision tree computing $f$ queries all $n$ variables on some input; in particular $D(f) = n$, i.e. $f$ is *evasive*.

## Proof sketch

A consistent path that reads fewer than $n$ distinct variables ends at a leaf whose subcube has positive dimension and on which $f$ is constant; such a subcube has equally many even and odd inputs. If no input made the tree read all $n$ variables, summing over these subcubes, which partition the cube, would give $e = o$.

## Depends on

- [Binary decision tree](../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/decision-tree.md)
- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- R. L. Rivest and J. Vuillemin, "On Recognizing Graph Properties from Adjacency Matrices", Theoretical Computer Science 3(3), 1976.
- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
