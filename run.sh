set -e

iverilog \
	-DDEBUG \
	-g2005 -gstrict-expr-width -Wall \
	-s adder_testbench \
	-o adder.vvp adder.v
vvp adder.vvp
# open -a gtkwave --args adder_testbench.vcd adder_testbench.gtkw
