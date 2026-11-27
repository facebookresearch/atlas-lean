# One step of the tardiness computation

Let $J = ((p_0, d_0), \dots, (p_{n-1}, d_{n-1}))$
be a list of jobs with processing times $p_i \in \mathbb{N}$ and due dates $d_i \in \mathbb{N}$,
let $j \in \mathbb{N}$, and let $(p, d) = (p_j, d_j)$ if $j < n$ and $(p, d) = (0, 0)$ otherwise.
Running job $j$ from the state $(t, s) \in \mathbb{N} \times \mathbb{N}$, where $t$ is the elapsed
time and $s$ the accumulated tardiness, gives the state $(t + p, \, s + \max(t + p - d, 0))$.
