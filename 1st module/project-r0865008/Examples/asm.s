li x1, 1
li x2, 2
add x3, x1, x2

# There is an MMIO device mapped at address 0x10000000 that prints all written
# bytes to the standard output of the simulator. The value 0x4 (ASCII EOF) is
# interpreted specially and causes the simulation to end.
li x4, 0x10000000
li x5, 'X'
sb x5, 0(x4)
li x5, '\n'
sb x5, 0(x4)
li x5, 4
sb x5, 0(x4)
