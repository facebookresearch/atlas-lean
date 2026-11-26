# Monotonicity of time classes on codes

Let $t, t' : \mathbb{N} \to \mathbb{N}$ with
$t(n) \le t'(n)$ for every $n$. Then every decision problem that some code decides within
$t(|x|)$ steps on every input $x$ is decided by some code within $t'(|x|)$ steps on every
input $x$: $\mathrm{CodeTime}(t) \subseteq \mathrm{CodeTime}(t')$.
