# The SAT verifier's answer through the occurrence table

For all lists $x$ and $w$ of bits,
the value returned by the SAT verifier on $(x, w)$, ignoring the time count, is false if the
complete length-prefixed CNF decoder fails on $x$, and is the clause check of $\varphi$ against
the occurrence table of $\varphi$ and $w$ if $x$ decodes to the CNF formula $\varphi$.
