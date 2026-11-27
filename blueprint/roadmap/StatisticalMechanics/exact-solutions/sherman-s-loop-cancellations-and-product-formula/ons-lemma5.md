# Sherman's Lemma 5

Let $E$ be a finite set, $\Lambda \in \mathbb{C}^{E \times E}$, $n \ge 1$, $e \in E$, and $\rho : E \to E$ an involution with $\rho(e) \ne e$. Suppose that for every sequence $v$ of length $n$ visiting both $e$ and $\rho(e)$, the [segment-reversal surgery](ons-surgery.md) $\sigma(v)$ satisfies $W_\Lambda(\sigma(v)) = -W_\Lambda(v)$. Then

$$\sum_{v} W_\Lambda(v) = 0,$$

the sum over all sequences $v \in E^n$ that visit both $e$ and $\rho(e)$, where $W_\Lambda(v) = \prod_{k} \Lambda(v_k, v_{k+1})$ (indices mod $n$) is the loop weight (Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I*, 1960).
