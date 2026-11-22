# Boundary influence bound for the minus box measures

For $d \in \mathbb{N}$, $\beta, h \in \mathbb{R}$, $g \in \mathbb{Z}^d$ and $\varphi \colon \mathbb{N} \to \mathbb{N}$, this
condition holds when for every [cylinder function](pstc-cylinder-bcf-set.md) $f$ there is a constant $C$ such that for every $n$,

$$\Bigl| \int f \, d\mu^-_{\varphi(n)} - \int f \circ \theta_g \, d\mu^-_{\varphi(n)} \Bigr| \le C\, b(\varphi(n)),$$

with $\mu^-_n$ the minus-boundary box measures ([definition](../dlr-states-of-the-ising-model/minus-measure.md)),
$\theta_g$ the shift by $g \in \mathbb{Z}^d$, $(\theta_g \omega)_x = \omega_{x - g}$ and $b(n)$ the [boundary bond fraction](ibs-boundary-fraction.md) of $\Lambda_n$.
