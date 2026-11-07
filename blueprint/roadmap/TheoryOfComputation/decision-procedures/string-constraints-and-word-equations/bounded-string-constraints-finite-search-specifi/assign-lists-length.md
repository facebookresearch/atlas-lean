# Size of the bounded assignment enumeration

Counting the assignment enumeration: the total (worst-case) size of
the candidate search space is `(wordsUpToCount B) ^ |vs|`. This counts
enumerated association lists; see the cost model in the module header
for when it coincides with the number of distinct assignments.
