# The SAT verifier on a decodable input

For all lists of Booleans $x$ and $w$ and every
CNF formula $\varphi$, if the complete CNF decoder returns $\varphi$ on $x$, then the SAT verifier
on $(x, w)$ coincides with the CNF check of $\varphi$ against the witness $w$ and the occurrence
list of $\varphi$: both the returned Boolean and the declared time cost are the same.
