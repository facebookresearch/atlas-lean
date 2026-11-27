# Faces parallel to a maximal Fourier support are nonconstant

Let $f : \{0,1\}^n \to \mathbb{R}$ and let $S$ be maximal (under inclusion) with $\hat f(S) \ne 0$. Then for every assignment $a$ to the coordinates outside $S$, the restriction $f(\cdot, a)$ to the face $\{0,1\}^S \times \{a\}$ has top coefficient $\hat f(S) \ne 0$; in particular it is nonconstant when $S \ne \emptyset$, so every input has a sensitive block of a Boolean $f$ contained in $S$.

## Proof sketch

The coefficient of $\chi_S$ in the restriction to a face is $\sum_{T \supseteq S} \hat f(T)\chi_{T \setminus S}(a)$, and by maximality only $T = S$ contributes.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014, Proposition 3.21.
