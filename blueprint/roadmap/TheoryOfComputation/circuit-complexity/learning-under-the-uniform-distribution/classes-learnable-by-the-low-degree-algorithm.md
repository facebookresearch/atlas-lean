# Low total influence, monotone and noise-stable functions are learnable by the low-degree algorithm

With $N_t \le (n+1)^t$ and $m \ge (4N_t/\varepsilon)\ln(2N_t/\delta)$ uniform examples, the degree-$t$ low-degree algorithm learns with error $\varepsilon$ and confidence $1-\delta$:

1. every Boolean function of total influence at most $K$, whenever $\varepsilon(t+1) \ge 2K$ (so $(n+1)^{O(K/\varepsilon)}$ examples);
2. every monotone Boolean function, whenever $\varepsilon(t+1) \ge 2\sqrt n$ (so $(n+1)^{O(\sqrt n/\varepsilon)}$ examples);
3. every Boolean function whose noise sensitivity $\Pr[f(x) \ne f(y)]$ at rate $\eta \le 1/2$ (with $y$ obtained from uniform $x$ by flipping each bit independently with probability $\eta$) is at most $\varepsilon/6$, whenever $\eta(t+1) \ge 1$ (so $(n+1)^{O(1/\eta)}$ examples).

## Proof sketch

The total influence equals $\sum_S |S|\hat f(S)^2$, so the weight above degree $t$ is at most $K/(t+1) \le \varepsilon/2$. Monotone functions have total influence at most $\sqrt n$. Noise sensitivity at rate $\eta$ equals $\frac12\sum_S (1 - (1-2\eta)^{|S|})\hat f(S)^2$, and $1 - (1-2\eta)^{|S|} \ge 1 - e^{-2}$ for $|S| > t \ge 1/\eta - 1$, which bounds the high-degree weight by a constant times the noise sensitivity.

## Depends on

- [The low-degree algorithm learns classes with small Fourier weight above degree t](low-degree-algorithm.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [The low-degree algorithm learns classes with small Fourier weight above degree t](low-degree-algorithm.md)
- [Low total influence implies low-degree spectral concentration](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/spectral-structure-of-boolean-functions/sum-sq-card-gt-le-of-pos.md)

## Sources

- Ryan O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- Nathan Linial, Yishay Mansour and Noam Nisan, "Constant Depth Circuits, Fourier Transform, and Learnability", Journal of the ACM, 1993.
