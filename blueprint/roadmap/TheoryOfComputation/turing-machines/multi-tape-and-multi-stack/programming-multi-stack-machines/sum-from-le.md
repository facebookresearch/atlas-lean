# Termwise bound on a sum of consecutive values

Let $f : \mathbb{N} \to \mathbb{N}$ and
$c, i, j \in \mathbb{N}$. If $f(t) \le c$ for every $t$ with $i \le t < i + j$, then
$\mathrm{sumFrom}(f, i, j) = f(i) + f(i+1) + \dots + f(i+j-1)$ is at most $j \cdot c$.
