# Feasible instances of BREAKPOINT MEDIAN

Let $n$ be the length of $\pi_0$. An instance $(\pi_0, \pi_1, \pi_2, k)$ is feasible when some signed permutation $\sigma$ on $n$ elements satisfies

$$\mathrm{bp}(\pi_0, \sigma) + \mathrm{bp}(\pi_1, \sigma) + \mathrm{bp}(\pi_2, \sigma) \le k,$$

where $\mathrm{bp}(\pi, \sigma)$ counts the successive pairs of its first argument $\pi$ that are not successive pairs of $\sigma$ in either orientation, plus one for each end of $\pi$ that differs from the corresponding end of $\sigma$. The count is not symmetric on raw input: for $\pi_0 = [+1]$, $\pi_1 = \pi_2 = [+1, +1, +1]$ and $\sigma = [+1]$, the sum above is $4$ while the sum with the arguments reversed is $0$.
