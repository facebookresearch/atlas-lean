# Input alphabet of the SAT verifier host

The alphabet $G$ of the host's input stack is the pair alphabet $\{0,1\} \sqcup (\{0,1\} \cup \{\#\})$ of the dense
SAT verifier.

In the encoding of a pair $(x, w)$, a formula bit $b$ is $\mathrm{inl}(b)$, the separator is $\#$ and a certificate
bit $b$ is $\mathrm{inr}(b)$.
