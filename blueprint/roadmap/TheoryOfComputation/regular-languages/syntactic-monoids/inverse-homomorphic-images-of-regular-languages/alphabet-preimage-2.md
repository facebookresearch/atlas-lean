# Regular languages are closed under alphabet preimages

Let $f \colon \Sigma \to \Gamma$
be a map between alphabets. If $L$ is a regular language over $\Gamma$, then its alphabet
preimage $\{w \in \Sigma^* \mid f^*(w) \in L\}$ is regular, where $f^*(w)$ is the word obtained
by applying $f$ to each letter of $w$.
