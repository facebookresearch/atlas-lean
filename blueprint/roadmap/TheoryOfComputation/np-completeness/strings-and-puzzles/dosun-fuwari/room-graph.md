# The room graph of a DOSUN-FUWARI grid

The room graph of a DOSUN-FUWARI instance keeps the edges of the grid graph between two cells with the same entry, label $0$ included. Its connected components are the maximal connected sets of cells of the same label. Only after [validation](well-formed.md), which requires all the cells with each positive label to be mutually reachable, are the positive components exactly the rooms. For example, on the well-formed grid $[[0, 0]]$ the two black cells form one component.
