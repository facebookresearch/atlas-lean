# Time-bounded multi-tape machine

A deterministic Turing machine $M$ with $k$ work tapes
is time bounded by $t : \mathbb{N} \to \mathbb{N}$ when, for every input word $w$, every
computation path of $M$ on $w$ with at least $t(|w|)$ steps ends in a halted configuration,
where $|w|$ is the length of $w$.
