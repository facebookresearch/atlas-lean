# Enumeration of bounded assignments as association lists

Let $\alpha$ be a finite alphabet. Let $V$ be a set of variables. For a finite list $vs$ of variables and $B \in \mathbb{N}$, the
bounded assignment enumeration is defined by recursion on $vs$: for the empty list it is the list whose
only entry is the empty association list; for $vs = v\, vs'$ it consists of the association lists $(v,
w)$ followed by $l$, for each $l$ in the enumeration for $vs'$ and each word $w$ over $\alpha$ of length
at most $B$ (in the enumeration of such words). Thus it lists every association list $(v_1, w_1), \dots,
(v_k, w_k)$ with keys $vs = v_1 \cdots v_k$ and all $|w_j| \le B$, each once.
