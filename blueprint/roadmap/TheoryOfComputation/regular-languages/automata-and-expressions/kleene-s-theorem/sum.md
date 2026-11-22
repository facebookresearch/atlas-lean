# Regex-denoted languages are closed under finite unions

Let $\alpha$ be an alphabet. A language over $\alpha$ is regex-denoted if it is the language matched by some regular expression over $\alpha$ (regular expressions being built from $0$, $1$ and single letters by sum, concatenation and Kleene star). Let $s$ be a finite index set and $(L_i)_{i \in s}$ languages over $\alpha$ such that
$L_i$ is regex-denoted for every $i \in s$. Then $\bigcup_{i \in s} L_i$ is regex-denoted (the empty union being the
empty language).
