In this repository I've implemented various adders, at the gate level, in
Verilog. All the gates have a uniform delay, this is done mainly for pedagogical
purposes, to see how the signals propagate through the various kinds of adders.

All the adder have also been verified to be correct by and exhaustive search    
over all possible 8-bit number. The adders implemented are:

  * ripple-carry
  * carry-select
  * carry-lookahead
  * serial
  * residue number system
  * redundant numer system (with signed digits)
