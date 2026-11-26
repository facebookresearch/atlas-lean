# Persistence landscape

For a bar with birth $b$ and finite death $d$, put $f_{b,d}(t)=\max(0,\min(t-b,d-t))$; for infinite death put $f_{b,+\infty}(t)=\max(0,t-b)$. In degree $p\in\mathbb N$, the $k$-th landscape value of a barcode at real time $t$ is the $k$-th largest tent value of a degree-$p$ bar at $t$, counting multiplicity. It is zero if $k=0$ or fewer than $k$ such bars occur. Thus the landscape in degree $p$ is a function of $(k,t)\in\mathbb N\times\mathbb R$.

## Sources

- P. Bubenik, [Statistical Topological Data Analysis Using Persistence Landscapes](https://www.jmlr.org/papers/volume16/bubenik15a/bubenik15a.pdf), *Journal of Machine Learning Research* 16 (2015).
