# Yao's principle by averaging, algorithm side

Let $A$ and $Y$ be finite sets of deterministic algorithms and inputs and let $C(a, y) \in \mathbb{Q}$ be the cost of algorithm $a$ on input $y$. Let $A$ be nonempty, let $p \colon A \to \mathbb{Q}$ be a probability distribution ($p(a) \ge 0$ and $\sum_a p(a) = 1$) and let $q \colon Y \to \mathbb{Q}$ be any weights. Then some deterministic algorithm $a$ satisfies

$$\sum_{y} q(y)\, C(a, y) \le \sum_{a'} p(a') \sum_{y} q(y)\, C(a', y).$$

With $q$ an input distribution: some deterministic algorithm does at least as well against $q$ as the randomized algorithm $p$.
