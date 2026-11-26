# Learning from uniform random examples

A concept on $n$ coordinates is a Boolean function $f : \{0,1\}^n \to \{0,1\}$. The uniform error of a hypothesis $h$ against $f$ is $\mathrm{err}(f,h) = \Pr_{x}[h(x) \ne f(x)]$ for $x$ uniform on $\{0,1\}^n$. A learner from $m$ examples maps a labelled sample $((x_1, f(x_1)), \ldots, (x_m, f(x_m)))$ to a hypothesis. It learns a class $C$ with error $\varepsilon$ and confidence $1 - \delta$ under the uniform distribution if for every $f \in C$, when $x_1,\ldots,x_m$ are independent and uniform, $\Pr[\mathrm{err}(f, h) > \varepsilon] \le \delta$. This is PAC learning restricted to the realizable family of the uniform distribution labelled by concepts of $C$.

## Sources

- Leslie G. Valiant, "A Theory of the Learnable", Proceedings of the 16th Annual ACM Symposium on Theory of Computing, 1984.
- Nathan Linial, Yishay Mansour and Noam Nisan, "Constant Depth Circuits, Fourier Transform, and Learnability", Journal of the ACM, 1993.
- Ryan O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
