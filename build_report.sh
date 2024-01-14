create_waveform_file() {
	python3 vcdvis/vcdvis.py -start_tick ${1}ns -end_tick ${2}ns -c vcdvis_config.json \
		-f adder_testbench.vcd latex >${3}.tex
	# We could have used sed but ed(1) is cooler XD.
	echo '%s/adder\\\\_testbench\.clock/clock/
	w
	q' | ed ${3}.tex
}

create_waveform_file 50 80 8p3wf
create_waveform_file 80 110 31p31wf
create_waveform_file 140 170 15p9wf

grep -e ' \$$' -e '^#' -e ' ,$' adder_testbench.vcd | sed -e 's/\$/sum_qsda/' -e 's/,/A/'
