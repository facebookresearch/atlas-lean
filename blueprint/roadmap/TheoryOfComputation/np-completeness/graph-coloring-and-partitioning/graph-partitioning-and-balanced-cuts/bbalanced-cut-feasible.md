# Feasible instances of b-BALANCED CUT

An instance $(n,w,E,(p,q),K)$ is feasible if some $C\subseteq V=\{0,\ldots,n-1\}$ satisfies $p\,w(V)\le q\,\min\{w(C),w(V\setminus C)\}$ and the costs of the listed edges with exactly one endpoint in $C$ sum to at most $K$. The weight of a set is the sum of its vertex weights, with zero for every missing weight. The displayed inequality also defines the test when $q=0$. For $q>0$ it says that each side has at least the fraction $p/q$ of the total weight.
