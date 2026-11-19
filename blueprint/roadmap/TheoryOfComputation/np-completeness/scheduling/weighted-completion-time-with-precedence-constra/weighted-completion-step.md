# One step of the weighted completion time computation

Let $J$ be a list of jobs, each a
pair (processing time, weight), let $(t, s)$ be a state consisting of the elapsed time $t$ and the
accumulated weighted completion time $s$, and let $j$ be a job index. With $(p, w)$ the job at
position $j$ of $J$ counting from $0$, or $(0, 0)$ if $J$ has no such position, the step sends
$(t, s)$ to $(t + p, s + w (t + p))$.
