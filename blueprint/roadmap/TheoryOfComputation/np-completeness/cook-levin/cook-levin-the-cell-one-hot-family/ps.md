# Stages of the one-hot precomputation

The control labels of the generator's
precomputation, sixteen in all: one each for incrementing the time counter $T_n$, writing the
number $g$ of symbol codes on the counter $G_c$, writing the label/state block size $A$ on the
counter $W_c$ and writing the number $K$ of stacks on the counter $K_c$, and one for each of the
four stages of a multiplication routine in each of the three multiplications
$HG := HG + H_s G_c$, $W_c := W_c + K_c \cdot HG$ and $V_c := V_c + T_n W_c$, where $H_s$ is the
height counter and $HG$ and $V_c$ are further counters of the generator.
