# Number of pops bounded by the total splitter count

Let $\Sigma$ be a finite alphabet and $Q$ a finite set. For $q \in Q$, $b \in \Sigma$ and a list $W$ of splitters, the splitter count $\mathrm{cnt}(q, b, W)$ is the number of entries $(C, b')$ of $W$, counted with multiplicity, with $b' = b$ and $q \in C$. If every entry $(C, a)$ of a finite list $t$ of splitters
has $C$ nonempty, then

$$|t| \le \sum_{b \in \Sigma} \sum_{q \in Q} \mathrm{cnt}(q, b, t).$$
