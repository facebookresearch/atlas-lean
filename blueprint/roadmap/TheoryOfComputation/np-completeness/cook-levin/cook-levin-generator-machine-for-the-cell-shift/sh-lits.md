# Literals of an in-range shift clause

Fix a layout $L$ and tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$. For a height $H$, write $C[t,k,j,x]$ for the cell variable of
stack $k$, depth $j$ and symbol code $x$ at time $t$, and $X[t,a]$ for the label/state variable
$a$ at time $t$. With $c = \mathrm{cn}(i,k)$ and $p = \mathrm{pl}(i,k)$, the literals of the
clause $(t, i, k, u, x)$ are, as (variable, sign) pairs in this order, $\neg C[t,k,u+c,x]$,
$\neg X[t+1,\mathrm{sa}(i)]$ and $C[t+1,k,u+p,x]$. Writing $S[t,i] = X[t+1,\mathrm{sa}(i)]$ for
the situation variable of situation $i$ at time $t$, this is the clause
$\neg C[t,k,u+c,x] \lor \neg S[t,i] \lor C[t+1,k,u+p,x]$.

When all indices are in range, the literals are in increasing variable order: a row $t$ cell, the
label/state block of row $t+1$, then a row $t+1$ cell.
