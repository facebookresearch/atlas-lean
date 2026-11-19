# Agreement of a circuit with a Boolean function

Let $\alpha$ be a finite type, let $C$
be a circuit given as a list of encoded gates, let $g$ assign a Boolean to each $a \in \alpha$,
and let $\mathrm{enc}$ encode each $a \in \alpha$ as a list of Booleans. The agreement of $C$
with $g$ is the rational number $N / |\alpha|$ (which is $0$ when $\alpha$ is empty), where $N$
is the number of $a \in \alpha$ such that $C$ has at least one gate and the value of its last
gate, when $C$ is evaluated on the input list $\mathrm{enc}(a)$, equals $g(a)$.
