# Truth of a quantified Boolean formula with circuit matrix

Let $P$ be a quantifier prefix,
a list of pairs $(q, v)$ of a quantifier $q$, $\exists$ (true) or $\forall$ (false), and a
variable $v \in \mathbb{N}$; let $\varphi$ be a matrix circuit and $\alpha$ an assignment of a
truth value to every natural number. Truth of $(P, \varphi)$ under $\alpha$ is defined by
recursion on $P$. If $P$ is empty, it means that $\varphi$ is nonempty and the value of its last
gate under $\alpha$ is true. If $P$ starts with $(q, v)$ followed by the prefix $P'$, it means that
$(P', \varphi)$ is true under $\alpha[v \mapsto \mathrm{true}]$ or under
$\alpha[v \mapsto \mathrm{false}]$ when $q$ is $\exists$, and under both when $q$ is $\forall$,
where $\alpha[v \mapsto b]$ agrees with $\alpha$ except that it sends $v$ to $b$.
