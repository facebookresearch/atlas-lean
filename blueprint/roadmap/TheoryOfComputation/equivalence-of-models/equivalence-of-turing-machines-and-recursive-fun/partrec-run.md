# Running a primitive recursive machine is partial recursive

Let $\alpha$, $\sigma$ and
$\beta$ be primitive recursively encodable types, and let $\mathrm{init} : \alpha \to \sigma$,
$\mathrm{step} : \sigma \to \sigma$, $\mathrm{halted} : \sigma \to \mathrm{Bool}$ and
$\mathrm{out} : \sigma \to \beta$ be primitive recursive. Then the partial function sending $a$
to $\mathrm{out}(\mathrm{step}^k(\mathrm{init}(a)))$, where $k$ is the least natural number for
which $\mathrm{halted}(\mathrm{step}^k(\mathrm{init}(a)))$ is true, and undefined when there is
no such $k$, is partial recursive.
