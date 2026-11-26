# Linial-Mansour-Nisan: constant-depth circuits are learnable from quasi-polynomially many uniform examples

Let $f$ on $n$ bits be computed by a circuit of negations and unbounded fan-in AND and OR gates of depth at most $d$ (counting every gate on a path) with at most $g$ gates, and let $s \ge 2$. Then the Fourier weight of $f$ above degree $t$ is at most $2g/2^s$ whenever $2\max\{8, 2s\}(16s+1)^d \le t+1$. Consequently, with $s = \max\{2, \lceil\log_2\lceil 4g/\varepsilon\rceil\rceil\}$ and $t = 2\max\{8,2s\}(16s+1)^d - 1 = O(\log(g/\varepsilon))^{d+1}$, the low-degree algorithm of degree $t$ from $m \ge (4N_t/\varepsilon)\ln(2N_t/\delta)$ uniform examples learns all such functions with error $\varepsilon$ and confidence $1-\delta$. For polynomial $g$ and constant $d, \varepsilon, \delta$ this is $n^{O(\log n)^{d+1}}$ examples.

## Proof sketch

A random restriction leaving each variable alive with small probability collapses the circuit to a shallow decision tree with high probability by repeated use of the switching lemma; a function computed by a depth-$r$ decision tree has no Fourier weight above degree $r$. Averaging over restrictions transfers this to a bound on the high-degree weight of $f$ itself, with failure probability charged to the $g$ gates. Plug the degree into the low-degree algorithm.

## Depends on

- [The low-degree algorithm learns classes with small Fourier weight above degree t](low-degree-algorithm.md)
- [The class $\mathsf{AC}^0$](../../complexity-classes/time-and-space-complexity-classes/ac0.md)

## Proof depends on

- [The low-degree algorithm learns classes with small Fourier weight above degree t](low-degree-algorithm.md)
- [Håstad's switching lemma](../lower-bounds-for-ac0-circuits/hastad-s-switching-lemma.md)

## Sources

- Nathan Linial, Yishay Mansour and Noam Nisan, "Constant Depth Circuits, Fourier Transform, and Learnability", Journal of the ACM, 1993.
- Ryan O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
