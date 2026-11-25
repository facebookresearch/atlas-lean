# Flow Shop Check

Check an encoded flow-shop instance and an encoded list of three start times per job.
The verifier checks each job's precedence and deadline and tests each pair for nonoverlap
on all three machines. Malformed inputs or certificates are rejected.
