# Cook–Mertz 2020: catalytic branching programs beating the pebbling algorithm for Tree Evaluation

Recall that an instance of Tree Evaluation $\mathrm{TreeEval}_{k,h}$ (binary version) is a complete binary tree of height $h$ whose leaves carry values in $[k]$ and whose internal nodes carry explicit function tables $f_v:[k]\times[k]\to[k]$; the task is to output the value of the root, evaluated bottom-up. The input length is $n=2^{\Theta(h)}\cdot\mathrm{poly}(k)$, so $\log n=\Theta(h+\log k)$, and the depth-first (pebbling) algorithm uses space $\Theta(h\log k)$.

As layered branching programs, the pebbling algorithm has $2^h-1$ layers of width up to $k^h$. Cook and Mertz give three deterministic branching programs for $\mathrm{TreeEval}_{k,h}$:

1. $2^{4h}\mathrm{poly}(k)$ layers of width $2^{3k}$, which beats the pebbling bound when $h=\omega(k/\log k)$;
2. $(2k)^{2h}\mathrm{poly}(k)$ layers of width $k^3$, of total size comparable to pebbling but built in the catalytic framework;
3. for every constant $\epsilon\gt 0$ and some $C=O(1/\epsilon)$, $(1+Ck/h)^{2h}\mathrm{poly}(k)$ layers of width $(1+Ck/h)^{\epsilon h}$, which beats pebbling for all $h\ge k^{1/2+\mathrm{poly}(\epsilon)}$.

These are the first deterministic upper bounds for Tree Evaluation better than the pebbling algorithm.

## Proof sketch

The programs evaluate the tree by register programs in the style of Buhrman–Cleve–Koucký–Loff–Speelman: the value of a node is added into registers that already hold arbitrary content, using clean (transparent) computations of the children twice with opposite signs, so the registers used for a subtree are reused for its sibling and parent instead of being stacked. The three programs differ in how node values are encoded (bitwise indicator encodings versus field encodings), trading layer count against width.

## Proof depends on

- [Transparent register programs (Buhrman–Cleve–Koucký–Loff–Speelman)](../catalytic-class-collapses/transparent-register-programs.md)

## Sources

- James Cook and Ian Mertz, "Catalytic Approaches to the Tree Evaluation Problem", STOC (2020), doi:10.1145/3357713.3384316; ECCC TR20-056 (Theorems 1–3).
