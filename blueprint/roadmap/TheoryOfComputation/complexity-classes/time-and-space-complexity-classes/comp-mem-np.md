# NP is closed under polynomial-time preimages

Decision problems are maps from bitstrings to $\{\mathrm{true}, \mathrm{false}\}$, and
polynomial-time maps are computed in polynomial time with the canonical bitstring encodings.
If a decision problem $L$ is in NP and $f$ is a polynomial-time map from bitstrings to bitstrings,
then the decision problem $x \mapsto L(f(x))$ is in NP.
