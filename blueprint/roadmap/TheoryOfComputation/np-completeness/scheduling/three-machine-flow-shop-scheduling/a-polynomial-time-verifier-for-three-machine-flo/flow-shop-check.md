# Checking a three-machine flow-shop schedule

The verifier accepts an encoded instance and
a certificate exactly when both decode, there is one certificate row per job, each job has three
durations and three start times, and the schedule is feasible. Each job visits the machines in
order and finishes by the deadline. On each machine one operation of every pair finishes by the
start of the other, including when a duration is zero.
