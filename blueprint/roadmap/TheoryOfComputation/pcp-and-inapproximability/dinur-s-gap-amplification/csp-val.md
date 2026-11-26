# Value of a 2CSP instance under an assignment

Let $I = (n, \Sigma, C)$ be a 2CSP
instance and $\sigma$ an assignment of a label less than $\Sigma$ to each variable less than $n$.
The value of $I$ under $\sigma$ is the rational number $1$ if $C$ is empty, and otherwise the
number of entries of the list $C$ that are constraints satisfied by $\sigma$, divided by the
length of $C$.
