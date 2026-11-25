# Reachability gives an iteration count

Let $\alpha$ be a type, let $\bot \notin \alpha$,
and let $f : \alpha \to \alpha \cup \{\bot\}$ be a partial step function, where $f(x) = \bot$
means that no step is possible from $x$. Extend $f$ to
$\bar f : \alpha \cup \{\bot\} \to \alpha \cup \{\bot\}$ by $\bar f(\bot) = \bot$. If $b \in \alpha$
is reachable from $a \in \alpha$ under $f$, that is, $b$ is obtained from $a$ by finitely many
(possibly zero) steps $x \mapsto f(x)$ none of which gives $\bot$, then there is $N \in \mathbb{N}$
with $\bar f^{N}(a) = b$.
