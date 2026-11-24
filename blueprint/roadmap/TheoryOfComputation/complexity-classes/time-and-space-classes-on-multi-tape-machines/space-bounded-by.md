# Space-bounded multi-tape machine

A deterministic Turing machine $M$ with $k$ work tapes
is space bounded by $s : \mathbb{N} \to \mathbb{N}$ when, for every input word $w$, every
computation path of $M$ on $w$ visits at most $s(|w|)$ work-tape cells, counting the cells
visited on each work tape and summing over the tapes, where $|w|$ is the length of $w$.
