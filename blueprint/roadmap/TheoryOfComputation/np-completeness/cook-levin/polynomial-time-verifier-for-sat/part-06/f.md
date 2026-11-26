# Filter exits in the SAT verifier host

The relabelling of the 3-clause filter's labels
into the labels of the SAT verifier host sends the filter's exit label *pass* to the start label
of the clause-check driver, its exit label *fail* to the cleanup label with answer false, and
every other filter label $l$ to the host's copy of $l$ among its filter labels.
