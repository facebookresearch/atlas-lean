# Decision trees identifying objects

A decision tree $tr$ identifies a set $S$ of objects when $tr$ uses only listed tests, and the label of each leaf of $tr$ is the unique object of $S$ consistent with the test outcomes on the path to it (each step keeps the objects of $S$ with the edge's outcome). A test with no listed outcome for an object has outcome $0$ on it.
