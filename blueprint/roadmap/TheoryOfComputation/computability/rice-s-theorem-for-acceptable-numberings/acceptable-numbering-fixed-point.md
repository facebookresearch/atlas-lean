# Rogers's fixed-point theorem for acceptable numberings

Let $\varphi$ assign to each
natural number $e$ a partial function $\varphi_e : \mathbb{N} \rightharpoonup \mathbb{N}$, and
suppose that the universal function $(e, n) \mapsto \varphi_e(n)$ is partial computable, that
every partial computable function $f : \mathbb{N} \rightharpoonup \mathbb{N}$ equals $\varphi_e$
for some $e$, and that for every partial computable
$g : \mathbb{N} \times \mathbb{N} \rightharpoonup \mathbb{N}$ there is a total computable
$s : \mathbb{N} \to \mathbb{N}$ with $\varphi_{s(e)}(n) = g(e, n)$ for all $e$ and $n$. Then for
every total computable $h : \mathbb{N} \to \mathbb{N}$ there is an $e$ with
$\varphi_e(n) = \varphi_{h(e)}(n)$ for all $n$.
