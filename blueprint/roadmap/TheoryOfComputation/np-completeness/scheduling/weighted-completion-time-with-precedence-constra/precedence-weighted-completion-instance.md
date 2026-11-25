# Instances of single-machine weighted completion with precedence

An instance of the
scheduling problem $1 \mid \mathrm{prec} \mid \sum w_j C_j$ (one machine, precedence constraints,
objective the sum over jobs $j$ of the weight $w_j$ times the completion time $C_j$) is a triple
$(J, P, K)$: a list $J$ of jobs, each a pair $(p, w)$ of natural numbers giving its processing
time and weight; a list $P$ of pairs of natural numbers, read as precedence constraints between
job indices; and a natural number bound $K$.
