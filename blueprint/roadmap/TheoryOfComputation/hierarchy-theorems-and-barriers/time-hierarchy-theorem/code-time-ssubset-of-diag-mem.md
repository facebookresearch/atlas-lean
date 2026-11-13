# A hierarchy within codes, given an upper bound

Let $f, g : \mathbb{N} \to \mathbb{N}$
with $f(n) \le g(n)$ for every $n$, and for a time bound $t$ let $\mathrm{CodeTime}(t)$ be the
class of decision problems that some code decides within $t(|x|)$ steps on every input $x$.
If the diagonal language $\mathrm{diag}(f)$ belongs to $\mathrm{CodeTime}(g)$, then
$\mathrm{CodeTime}(f)$ is a proper subclass of $\mathrm{CodeTime}(g)$.
