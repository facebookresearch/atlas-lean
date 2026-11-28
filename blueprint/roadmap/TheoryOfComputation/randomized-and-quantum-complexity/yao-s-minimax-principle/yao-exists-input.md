# Yao's principle by averaging, input side

Let $A$ and $Y$ be finite sets of deterministic algorithms and inputs and let $C(a, y) \in \mathbb{Q}$ be the cost of algorithm $a$ on input $y$. Let $Y$ be nonempty, let $q \colon Y \to \mathbb{Q}$ be a probability distribution ($q(y) \ge 0$ and $\sum_y q(y) = 1$) and let $p \colon A \to \mathbb{Q}$ be any weights. Then some input $y$ satisfies

$$\sum_{a} p(a)\, C(a, y) \ge \sum_{y'} q(y') \sum_{a} p(a)\, C(a, y').$$

With $p$ an algorithm distribution: some single input is at least as costly for $p$ as the input distribution $q$.
