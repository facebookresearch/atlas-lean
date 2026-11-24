# Name-loop outcome

For an optional bit $\ell$ and a bit string $u$, the name-loop outcome
is the tokenizer label defined by recursion on $u$: for empty $u$ it is $\mathsf{rej}$ if $\ell$ is
the bit false and $\mathsf{pol}$ otherwise, and for $u = c\,u'$ it is the outcome for the bit $c$
and the string $u'$. So it is $\mathsf{rej}$ exactly when the string formed by $\ell$ (if present)
followed by $u$ is non-empty and ends in false, and $\mathsf{pol}$ otherwise.
