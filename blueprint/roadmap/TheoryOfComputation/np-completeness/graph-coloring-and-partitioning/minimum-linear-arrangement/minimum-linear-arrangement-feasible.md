# Feasible minimum linear arrangement instance

An instance $(n, E, K)$ of MINIMUM LINEAR
ARRANGEMENT is feasible when there is an ordering $\pi$ of $0, 1, \dots, n-1$ (a list containing
each of these numbers exactly once) such that $\sum_{(u, v) \in E} |\pi(u) - \pi(v)| \le K$. Here
$\pi(v)$ is the position of $v$ in $\pi$, counted from $0$, and is $n$ when $v \ge n$; the sum
runs over the list $E$, so a repeated pair is counted once for each occurrence.
