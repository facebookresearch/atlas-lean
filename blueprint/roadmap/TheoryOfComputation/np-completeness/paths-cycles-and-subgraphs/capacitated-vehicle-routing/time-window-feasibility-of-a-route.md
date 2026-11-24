# Load and time-window feasibility of a fixed route

Let a route leave a depot at a departure time $\tau_0$ chosen in $[e_0, l_0]$, visit customers $1, \dots, m$ in order and return to the depot, with time windows $[e_k, l_k]$ ($e_k \le l_k$), service times $\sigma_k \ge 0$, travel times $t_{k,k+1} \ge 0$ and a return window $[e_{m+1}, l_{m+1}]$ at the depot. With waiting allowed and $\sigma_0 = 0$, the earliest service starts $\tau_k = \max(e_k, \tau_{k-1} + \sigma_{k-1} + t_{k-1,k})$ are nondecreasing in the departure time, so departing at $\tau_0 = e_0$ is without loss of generality: the route is time-window feasible for some departure time in $[e_0, l_0]$ if and only if, with $\tau_0 = e_0$, $\tau_k \le l_k$ for $k = 1, \dots, m+1$. For delivery-only demands $q_k \ge 0$ the route respects vehicle capacity $Q$ exactly when $\sum_k q_k \le Q$; with pickups and deliveries every prefix load must lie in $[0, Q]$. That load condition certifies capacity only: when each delivery is paired with a pickup, visiting the pickup before its delivery is a separate precedence constraint.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
