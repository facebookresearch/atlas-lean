# Time classes are not empty once the bound exceeds the input length

Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $n + 1 \le f(n)$ for every $n$. Then the empty language, the
decision problem that answers false on every bit list, belongs to the time class of $f$: some code
decides it within $f(|x|)$ steps on every input $x$, where $|x|$ is the length of $x$.
