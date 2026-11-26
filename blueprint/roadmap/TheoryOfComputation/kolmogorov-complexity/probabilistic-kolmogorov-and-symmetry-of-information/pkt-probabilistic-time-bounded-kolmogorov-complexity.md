# Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form

Fix a time-efficient universal machine $U$ that takes a program $p$, an auxiliary input $y$ and a read-only random string $w$. Recall that the time-bounded conditional complexity $K^t(x\mid y)$ is the length of a shortest $p$ with $U(p,y)$ printing $x$ within $t$ steps. For $t\in\mathbb{N}$ and strings $x,y$, the **probabilistic $t$-time-bounded Kolmogorov complexity** of $x$ given $y$ is

$$
\mathrm{pK}^t(x\mid y)=\min\Bigl\{k\in\mathbb{N}:\ \Pr_{w\sim\{0,1\}^t}\bigl[\exists p\in\{0,1\}^{\le k}:\ U(p,y,w)\text{ prints }x\text{ within }t\text{ steps}\bigr]\ge\tfrac23\Bigr\},
$$

and $\mathrm{pK}^t(x)=\mathrm{pK}^t(x\mid\varepsilon)$. Thus for a typical public random string $w$ shared by encoder and decoder, $x$ has a $t$-time description of length $k$ relative to $w$; the program may depend on $w$. For a function $t:\mathbb{N}\to\mathbb{N}$ one writes $\mathrm{pK}^{t}(x)$ for $\mathrm{pK}^{t(|x|)}(x)$. The related **randomized** complexity $\mathrm{rK}^t(x\mid y)$ is the length of a shortest randomized program that, on input $y$, prints $x$ within $t$ steps with probability at least $2/3$ over its internal coins.

## Depends on

- [Kolmogorov complexity](../k.md)
- [Optimality (the invariance theorem)](../exists-k-le-of-partrec.md)

## Sources

- Halley Goldberg, Valentine Kabanets, Zhenjian Lu and Igor C. Oliveira, "Probabilistic Kolmogorov Complexity with Applications to Average-Case Complexity", CCC (2022), ECCC TR22-072.
- Shuichi Hirahara, Rahul Ilango, Zhenjian Lu, Mikito Nanashima and Igor C. Oliveira, "A Duality Between One-Way Functions and Average-Case Symmetry of Information", STOC (2023), ECCC TR23-035.
