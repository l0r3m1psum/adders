`timescale 1ns / 1ns
`define DELAY 1

/******************************************************************************
 * Ripple Carry Adder                                                         *
 ******************************************************************************/

module half_adder(a, b, c, s);
	input a, b;
	output c, s;

	xor #(`DELAY) sum(s, a, b);
	and #(`DELAY) carry(c, a, b);
endmodule

module full_adder(a, b, cin, cout, s);
	input a, b, cin;
	output cout, s;

	wire partial_sum, c1, c2;

	half_adder ha_sum(cin, partial_sum, c1, s);
	half_adder ha_carry(a, b, c2, partial_sum);
	or #(`DELAY) (cout, c1, c2);
endmodule

module ripple_carry_adder(a, b, cin, cout, s);
	parameter n = 4;
	input [n-1:0] a, b;
	input cin;
	output [n-1:0] s;
	output cout;

	wire c [n:0];
	assign c[0] = cin;
	assign cout = c[n];

	genvar i;
	generate
		for (i = 0; i < n; i = i + 1) begin
			full_adder fa(a[i], b[i], c[i], c[i+1], s[i]);
		end
	endgenerate
endmodule

/******************************************************************************
 * Carry Select Adder                                                         *
 ******************************************************************************/

// TODO: document how this works i.e. which value of select selects what.
// probably sel = 0 selects in2
module multiplexer_2_to_1(in1, in2, sel, out);
	input in1, in2, sel;
	output out;

	wire not_sel, out_sel1, out_sel2;

	not #(`DELAY) (not_sel, sel);
	and #(`DELAY) (out_sel1, in1, sel);
	and #(`DELAY) (out_sel2, in2, not_sel);
	or #(`DELAY) (out, out_sel1, out_sel2);
endmodule

module carry_select_block(a, b, carry_in, carry_out, sum);
	parameter n = 4;
	input [n-1:0] a, b;
	input carry_in;
	output [n-1:0] sum;
	output carry_out;

	wire upper_carry_out, lower_carry_out;
	wire [n-1:0] upper_sum, lower_sum;

	ripple_carry_adder #(n) upper_adder(a, b, 1'b0, upper_carry_out, upper_sum);
	ripple_carry_adder #(n) lower_adder(a, b, 1'b1,  lower_carry_out, lower_sum);
	multiplexer_2_to_1 carry_out_mux(lower_carry_out, upper_carry_out, carry_in, carry_out);

	genvar i;
	generate
		for (i = 0; i < n; i = i + 1) begin
			multiplexer_2_to_1 sum_mux(lower_sum[i], upper_sum[i], carry_in, sum[i]);
		end
	endgenerate
endmodule

module carry_select_adder(a, b, cin, cout, s);
	parameter n = 16;
	input [n-1:0] a, b;
	input cin;
	output [n-1:0] s;
	output cout;

	localparam closest_perfect_square = $rtoi($rtoi($sqrt(n))**2);
	localparam offset = n - closest_perfect_square; // distance from closest perfect square.
	localparam blocks_size = $rtoi($sqrt(closest_perfect_square));
	localparam n_of_blocks = closest_perfect_square/blocks_size - 1; // excluding the first rca.
	localparam first_block_size = blocks_size + offset;

	wire c [n_of_blocks:0];
	assign  cout = c[n_of_blocks];
	ripple_carry_adder #(first_block_size) initial_rca(
		a[0 +: first_block_size],
		b[0 +: first_block_size],
		cin, c[0],
		s[0 +: first_block_size]
	);

	genvar i;
	generate
		for (i = 1; i <= n_of_blocks; i = i + 1) begin
			carry_select_block #(blocks_size) csb(
				a[blocks_size*i + offset +: blocks_size],
				b[blocks_size*i + offset +: blocks_size],
				c[i-1], c[i],
				s[blocks_size*i + offset +: blocks_size]
			);
		end
	endgenerate
endmodule

/******************************************************************************
 * Carry Lookahead Adder                                                      *
 ******************************************************************************/

module carry_lookahead_block(a, b, carry_in, sum, propagate, generate_);
	input a, b, carry_in;
	output sum, propagate, generate_;
	wire partial_sum;

	xor #(`DELAY) (partial_sum, a, b);
	xor #(`DELAY) (sum, partial_sum, carry_in);
	or #(`DELAY) (propagate, a, b);
	and #(`DELAY) (generate_, a, b);
endmodule

module carry_lookahead_adder_slow(a, b, cin, cout, s);
	parameter n = 8;
	input [n-1:0] a, b;
	input cin;
	output [n-1:0] s;
	output cout;

	wire p [n-1:0];
	wire g [n-1:0];
	wire c [n:0];
	assign c[0] = cin;
	assign cout = c[n];

	generate
		genvar i;
		for (i = 0; i < n; i = i + 1) begin
			wire partial_carry;
			carry_lookahead_block clab(a[i], b[i], c[i], s[i], p[i], g[i]);
			and #`DELAY (partial_carry, p[i], c[i]);
			or #`DELAY (c[i+1], g[i], partial_carry);
		end
	endgenerate
endmodule

module carry_lookahead_adder_4bit(
		input [3:0] a, b,
		input cin,
		output cout,
		output [3:0] s,
		output propagate_group, generate_group
	);

	wire p [3:0], g [3:0], c [3:0];
	assign c[0] = cin;
	carry_lookahead_block cla_block1(a[0], b[0], c[0], s[0], p[0], g[0]);
	carry_lookahead_block cla_block2(a[1], b[1], c[1], s[1], p[1], g[1]);
	carry_lookahead_block cla_block3(a[2], b[2], c[2], s[2], p[2], g[2]);
	carry_lookahead_block cla_block4(a[3], b[3], c[3], s[3], p[3], g[3]);

	wire
		/* g0 */ p0_c0,
		/* g1 */ p1_g0, p1_p0_c0,
		/* g2 */ p2_g1, p2_p1_g0, p2_p1_p0_c0,
		/* g3 */ p3_g2, p3_p2_g1, p3_p2_p1_g0, p3_p2_p1_p0_c0;

	// Using one delay unit for ports with large fan-in is incorrect. But we do
	// it anyways since the fan-in is not that large.

	or #`DELAY (c[1], g[0], p0_c0);
		and #`DELAY (p0_c0, p[0], c[0]);
	or #`DELAY (c[2], g[1], p1_g0, p1_p0_c0);
		and #`DELAY (p1_g0,    p[1], g[0]);
		and #`DELAY (p1_p0_c0, p[1], p0_c0);
	or #`DELAY (c[3], g[2], p2_g1, p2_p1_g0, p2_p1_p0_c0);
		and #`DELAY (p2_g1,       p[2], g[1]);
		and #`DELAY (p2_p1_g0,    p[2], p1_g0);
		and #`DELAY (p2_p1_p0_c0, p[2], p1_p0_c0);
	or #`DELAY (cout, generate_group, p3_p2_p1_p0_c0);
		and #`DELAY (p3_g2,          p[3], g[2]);
		and #`DELAY (p3_p2_g1,       p[3], p2_g1);
		and #`DELAY (p3_p2_p1_g0,    p[3], p2_p1_g0);
		and #`DELAY (p3_p2_p1_p0_c0, p[3], p2_p1_p0_c0);

	and #`DELAY (propagate_group, p[3], p[2], p[1], p[0]);
	or #`DELAY (generate_group, g[3], p3_g2, p3_p2_g1, p3_p2_p1_g0);
endmodule

module carry_lookahead_adder_8bit(
		input [7:0] a, b,
		input cin,
		output cout,
		output [7:0] s,
		output propagate_group, generate_group
	);

	wire p [1:0], g [1:0], c [1:0];
	assign c[0] = cin;

	carry_lookahead_adder_4bit cla_4bit1(
		a[3:0], b[3:0], c[0], /* ignoring cout */, s[3:0], p[0], g[0]);
	carry_lookahead_adder_4bit cla_4bit2(
		a[7:4], b[7:4], c[1], /* ignoring cout */, s[7:4], p[1], g[1]);

	wire
		/* g0 */ p0_c0,
		/* g1 */ p1_g0, p1_p0_c0;

	or #`DELAY (c[1], g[0], p0_c0);
		and #`DELAY (p0_c0, p[0], c[0]);
	or #`DELAY (cout, generate_group, p1_p0_c0);
		and #`DELAY (p1_g0,    p[1], g[0]);
		and #`DELAY (p1_p0_c0, p[1], p0_c0);

	and #`DELAY (propagate_group, p[1], p[0]);
	or #`DELAY (generate_group, g[1], p1_g0);
endmodule

/******************************************************************************
 * Residue Number System Adder                                                *
 ******************************************************************************/

/* We implement an adder (together with conversion from and to binary) for the
 * moduli set m1 = 2**k, m2 = 2**k-1, m3 = 2**(k-1)-1.
 * To make sense of the expression in this section of the code read
 * "Residue-to-Binary Arithmetic Converter for the Moduli Set (2^k, 2^k-1,
 * 2^(k-1)-1)".
 * https://ieeexplore.ieee.org/document/661651
 */

`define m1(k) (2**(k))
`define m2(k) (2**(k)-1)
`define m3(k) (2**((k)-1)-1)
`define M(k) (`m1(k)*`m2(k)*`m3(k))

module binary_to_residue
	#(parameter k=3)
	(input  [$clog2(`M(k))-1:0] X,
	 output [k-1:0] r1, r2, output [k-2:0] r3);
	assign r1 = X % `m1(k);
	assign r2 = X % `m2(k);
	assign r3 = X % `m3(k);
endmodule

module residue_to_binary
	#(parameter k=3)
	(input  [k-1:0] r1, r2, input [k-2:0] r3,
	 output [$clog2(`M(k))-1:0] X);

	// wire [$clog2(`M(k))-1:0] m3_hat = `m1(k)*`m2(k);
	wire [$clog2(`M(k))-1:0] m3_hat = 2**k*(2**k-1);
	wire [$clog2(`M(k))-1:0] floor_X_over_m3_hat = (2**(k-2)*r1 - r2 + 2**(k-2)*r3 - (r2 < r1)) % (2**(k-1)-1);
	// wire [$clog2(`M(k))-1:0] X_mod_m3_hat = (2**k*(r2-r1) + r1) % (`m1(k)*`m2(k));
	wire [$clog2(`M(k))-1:0] X_mod_m3_hat = 2**k*(r2-r1) + r1 + (r2 < r1)*(2**k*(2**k-1));

	assign X = floor_X_over_m3_hat * m3_hat + X_mod_m3_hat;
endmodule

module residue_number_system_adder_impl
	#(parameter n=3)
	(input  [n-1:0] a1, a2, input  [n-2:0] a3,
	 input  [n-1:0] b1, b2, input  [n-2:0] b3,
	 output [n-1:0] s1, s2, output [n-2:0] s3);

	generate
		if (gcd(`m1(n), `m2(n)) != 1)
			non_existing_module_used_for_errors invalid_parameters();
		else if (gcd(`m2(n), `m3(n)) != 1)
			non_existing_module_used_for_errors invalid_parameters();
		else if (gcd(`m1(n), `m3(n)) != 1)
			non_existing_module_used_for_errors invalid_parameters();
	endgenerate

	wire end_arround_carry_n1, end_arround_carry_n2;
	ripple_carry_adder #(n) adder_mod_n(a1, b1, 1'b0, /* ignoring cout */, s1);
	ripple_carry_adder #(n) adder_mod_n_minus_1_n1(a2, b2, end_arround_carry_n1, end_arround_carry_n1, s2);
	ripple_carry_adder #(n-1) adder_mod_n_minus_1_n2(a3, b3, end_arround_carry_n2, end_arround_carry_n2, s3);

	function integer gcd (input integer a, b);
		begin: euclids_algorithm
			while (a != b)
				if (a > b)
					a = a - b;
				else
					b = b - a;
			gcd = a;
		end
	endfunction
endmodule

`define Nbit 5
module residue_number_system_adder_8bit
	(input  [$clog2(`M(`Nbit))-1:0] a, b,
	 output [$clog2(`M(`Nbit))-1:0] s);

	/*
	generate
		if ($clog2(`M(3))-1 != 7)
			non_existing_module_used_for_errors invalid_parameters();
	endgenerate
	*/

	wire [`Nbit-1:0] a1, a2; wire [`Nbit-2:0] a3;
	wire [`Nbit-1:0] b1, b2; wire [`Nbit-2:0] b3;
	wire [`Nbit-1:0] s1, s2; wire [`Nbit-2:0] s3;

	binary_to_residue #(`Nbit) b2r_a(a, a1, a2, a3);
	binary_to_residue #(`Nbit) b2r_b(b, b1, b2, b3);
	residue_to_binary #(`Nbit) r2b_s(s1, s2, s3, s);

	residue_number_system_adder_impl #(`Nbit) adder(
		a1, a2, a3,
		b1, b2, b3,
		s1, s2, s3);
endmodule
`undef Nbit

`undef m1
`undef m2
`undef m3
`undef M

/******************************************************************************
 * Redundant (Signed Digit) Number System Adder                               *
 ******************************************************************************/

// https://verilogcodes.blogspot.com/2020/12/quaternary-signed-digit-qsd-based-fast.html

module QSD_internal_carry_sum_generator_register_transfer
	(input [2:0] a, b,
	 output [2:0] s,
	 output [1:0] c);

	// (~a & ~b) should be just a (a nor b)
	assign s[0] = a[0] ^ b[0];
	assign s[1] = (a[1] ^ b[1]) ^ (a[0] & b[0]);
	assign s[2] = s[0] & (a[1] ^ b[1])
		| (b[2] & ~a[1] & ~b[0])
		| (a[2] & ~b[1] & ~a[0])
		| (a[0] &  b[0] & ~a[1] & ~b[1] & (a[2] | b[2]))
		| (a[0] &  b[0] &  a[1] &  b[1] & a[2] & b[2]);

	assign c[0] = c[1] | (
		(~a[2] & ~b[2])
		& (a[1]&b[1] | b[1]&b[0] | b[1]&a[0] | b[0]&a[1] | a[1]&a[0])
	);
	assign c[1] = a[2]&b[2] & ~(a[0]&b[0]&a[1]&b[1]) | ~(a[1] | b[1])
		& (a[2]&~b[0] | b[2]&~a[0]);
endmodule

module QSD_internal_carry_sum_generator
	(input [2:0] a, b,
	 output [2:0] s,
	 output [1:0] c);

	wire a0_and_b0, a1_xor_b1, a2_or_b2, not_a0, not_a1, not_b0, not_b1,
		xx1, xx2, xx3, xx4, xx5;

	not #`DELAY
		(not_a0, a[0]), (not_a1, a[1]),
		(not_b0, b[0]), (not_b1, b[1]);

	xor #`DELAY (s[0], a[0], b[0]);
	xor #`DELAY (s[1], a[1], b[1], a0_and_b0);
		and #`DELAY (a0_and_b0, a[0], b[0]);
	or #`DELAY (s[2], xx1, xx2, xx3, xx4, xx5);
		and #`DELAY (xx1, s[0], a1_xor_b1);
			xor #`DELAY (a1_xor_b1, a[1], b[1]);
		and #`DELAY (xx2, b[2], not_a1, not_b0);
		and #`DELAY (xx3, a[2], not_b1, not_a0);
		and #`DELAY (xx4, a[0], b[0], not_a1, not_b1, a2_or_b2);
			or #`DELAY (a2_or_b2, a[2], b[2]);
		and #`DELAY (xx5, a[0], b[0],  a[1],  b[1], a[2], b[2]);

	wire yy1, yy2, a2_nor_b2, a1_and_b1, b1_and_b0, b1_and_a0, b0_and_a1, a1_and_a0;
	or #`DELAY (c[0], c[1], yy1);
		and #`DELAY (yy1, a2_nor_b2, yy2);
			nor #`DELAY (a2_nor_b2, a[2], b[2]);
		or #`DELAY (yy2, a1_and_b1, b1_and_b0, b1_and_a0, b0_and_a1, a1_and_a0);
			and #`DELAY
				(a1_and_b1, a[1], b[1]),
				(b1_and_b0, b[1], b[0]),
				(b1_and_a0, b[1], a[0]),
				(b0_and_a1, b[0], a[1]),
				(a1_and_a0, a[1], a[0]);

	wire a2_and_b2, big_nand, a1_nor_b1, a2_and_not_b0_or_b2_and_not_a0,
		a2_and_not_b0, b2_and_not_a0, left_c1, right_c1;
	or #`DELAY (c[1], left_c1, right_c1);
		and #`DELAY (left_c1, a2_and_b2, big_nand);
			and #`DELAY (a2_and_b2, a[2], b[2]);
			nand #`DELAY (big_nand, a[0], b[0], a[1], b[1]);
		and #`DELAY (right_c1, a1_nor_b1, a2_and_not_b0_or_b2_and_not_a0);
			nor #`DELAY (a1_nor_b1, a[1], b[1]);
			or #`DELAY (a2_and_not_b0_or_b2_and_not_a0, a2_and_not_b0, b2_and_not_a0);
				and #`DELAY (a2_and_not_b0, a[2], not_b0);
				and #`DELAY (b2_and_not_a0, b[2], not_a0);
endmodule

module QSD_internal_2nd_step_adder_register_transfer
	(input [1:0] a, // internal carry
	 input [2:0] b, // internal sum
	 output [2:0] s);

	assign s[0] = a[0] ^ b[0];
	assign s[1] = a[1] ^ b[1] ^ (a[0] & b[0]);
	assign s[2] = a[1] ^ b[2] ^ (a[1]&b[1] | ((a[1] ^ b[1])&a[0]&b[0]));
endmodule

module QSD_internal_2nd_step_adder
	(input [1:0] a, // internal carry
	 input [2:0] b, // internal sum
	 output [2:0] s);

	wire a0_and_b0, a1_xor_b1,
		a1_and_b1, a1_xor_b1_and_a0_and_b0, a1_and_b1_or_a1_xor_b1_and_a0_and_b0;

	xor #`DELAY (s[0], a[0], b[0]);
	xor #`DELAY (s[1], a1_xor_b1, a0_and_b0);
		xor #`DELAY (a1_xor_b1, a[1], b[1]);
		and #`DELAY (a0_and_b0, a[0], b[0]);
	xor #`DELAY (s[2], a[1], b[2], a1_and_b1_or_a1_xor_b1_and_a0_and_b0);
		or #`DELAY (a1_and_b1_or_a1_xor_b1_and_a0_and_b0, a1_and_b1, a1_xor_b1_and_a0_and_b0);
		and #`DELAY (a1_xor_b1_and_a0_and_b0, a1_xor_b1, a0_and_b0);
		and #`DELAY (a1_and_b1, a[1], b[1]);
endmodule

// This takes as input 4 quaternary signed digits, so before we can use it in
// the test we have to convert back and forth.
module QSD_adder_impl
	#(parameter q=4) // where q is the number of QSD.
	(input [(3*q) - 1:0] a, b,
	 output [1:0] cout,
	 output [(3*q) - 1:0] s);

	wire [2:0] int_s [q-1:0]; // internal sum
	wire [1:0] int_c [q-1:0]; // internal carry

	assign s[2:0] = int_s[0];
	assign cout = int_c[q-1];

	generate
		for (genvar i = 0; i < q; i = i + 1) begin
			QSD_internal_carry_sum_generator cs_gen(
				a[i*3 +: 3], b[i*3 +: 3], int_s[i], int_c[i]
			);
		end

		for (genvar i = 0; i < q - 1; i = i + 1) begin
			QSD_internal_2nd_step_adder int_adder(
				int_c[i], int_s[i+1], s[(i+1)*3 +: 3]
			);
		end
	endgenerate
endmodule

// Sums two 9-bit numbers in 2's complement.
module QSD_9bit_adder
	(input [8:0] a, b,
	 output [8:0] s);

	localparam nbit_inp = 9;
	localparam nbit_qsd = (nbit_inp-1)/2*3;
	localparam nqsd = (nbit_inp-1)/2;

	function [nbit_qsd-1:0] int2qsd;
		input [nbit_inp-1:0] n;
	begin
		int2qsd = {
			n[8:7],
			n[6] === 1'b1 ? 2'b10 : 2'b00,
			n[5],
			n[4] === 1'b1 ? 2'b10 : 2'b00,
			n[3],
			n[2] === 1'b1 ? 2'b10 : 2'b00,
			n[1:0]
		};
	end
	endfunction

	// Interprest bits as 2's complement.
	function signed [2:0] to_int;
		input [2:0] n;
	begin
		to_int = n;
	end
	endfunction
	function signed [1:0] bit2_to_int;
		input [1:0] n;
	begin
		bit2_to_int = n;
	end
	endfunction

	wire [1:0] carry_qsd;
	wire [nbit_qsd-1:0] s_qsd;

	QSD_adder_impl #(nqsd) adder(int2qsd(a), int2qsd(b), carry_qsd, s_qsd);

	assign s =
		  to_int(s_qsd[2:0])  * (4 ** 0)
		+ to_int(s_qsd[5:3])  * (4 ** 1)
		+ to_int(s_qsd[8:6])  * (4 ** 2)
		+ to_int(s_qsd[11:9]) * (4 ** 3)
		+ 256 * bit2_to_int(carry_qsd);
endmodule

/******************************************************************************
 * Serial Adder                                                               *
 ******************************************************************************/

/* The amazing Ben Eater
 * https://www.youtube.com/watch?v=KM0DdEaY5sY the most basic latch is a OR
 * https://www.youtube.com/watch?v=F1OC5e7Tn_o edge triggering in real life is done with capacitors
 */

module or_latch
	(input in,
	 output out);

	or #1 gate(out, out, in);
endmodule

module or_latch_test_bench;
	reg in;
	wire out;

	or_latch latch(in, out);

	initial begin
		$monitor($time,, "in=%d, out=%d", in, out);
		#1
		in = 0;
		#10
		in = 1;
		#10
		$display("no more changes");
		in = 0;
		#10
		$finish();
	end
endmodule

/* This is jus a test JK flip flop, it is functional but it is hard to control
 * because of the "raw/nacked" clock (it is not edge triggered). Look at the
 * test bench below for a practical example. So this is not usefull in practice
 * but it has pedagogical value.
 */
module JK_flip_flop
	(input clock, reset,
	 input J /* set */, K /* reset */,
	 output Q, Q_bar);

	wire Q_input, Q_bar_input;

	nand #1
		(Q_input,     J, clock, Q_bar),
		(Q_bar_input, K, clock, Q),
		(Q,     Q_input,     Q_bar),
		(Q_bar, Q_bar_input, Q,   reset);
endmodule

module JK_flip_flop_test_bench;
	reg clock, J, K, reset;
	wire Q, Qn;

	JK_flip_flop ff(clock, reset, J, K, Q, Qn);

	always
		#5 clock = ~clock;

	initial begin
		$monitor($time,, "J=%d, K=%d, Q=%d, Qn=%d", J, K, Q, Qn);
		/* By doing the weird reset dance that we have seen here
		 * http://barrywatson.se/dd/dd_jk_flip_flop_master_slave.html
		 * the flip flop seems to work.
		 */
		clock = 1;
		J = 0; K = 0;
		reset = 1;
		#10
		reset = 0;
		#10
		reset = 1;
		#10
		$display("set to 0");
		J = 0; K = 1;
		#10
		$display("hold");
		J = 0; K = 0;
		#10
		$display("set to 1");
		J = 1; K = 0;
		#10
		$display("set to 0");
		J = 0; K = 1;
		#10
		$display("flip");
		J = 1; K = 1;
		#4 // If we don't get this timing right the flip flip goes bananas.
		$display("hold");
		J = 0; K = 0;
		#10
		$finish();
	end
endmodule

// NOTE: it would be cool to make this module with individual flip flops
module shift_register
	#(parameter N=8)
	(input data,
	 input clock,
	 input enabled,
	 input direction,
	 input batch_set,
	 input [N-1:0] data_batch,
	 output reg [N-1:0] out);

	localparam left = 0, right = 1;

	always @(posedge clock)
		if (batch_set)
			out <= data_batch;
		else begin
			if (enabled)
				case (direction)
					left  : out <= {out[N-2:0], data};
					right : out <= {data, out[N-1:1]};
				endcase
			else
				out <= out;
		end
endmodule

module serial_adder_block
	(input clock, reset,
	 input a, b,
	 output s);

	reg carry;
	wire j, k;

	assign j = a & b;
	assign k = ~a & ~b;
	assign s = carry ^ (a ^ b);

	always @(posedge clock)
		if (reset)
			carry <= 0;
		else
			case ({j, k})
				2'b00 : carry <= carry;
				2'b01 : carry <= 0;
				2'b10 : carry <= 1;
				2'b11 : carry <= ~carry;
			endcase
endmodule

module serial_adder
	#(parameter N=8)
	(input clock, reset,
	 input [N-1:0] A, B,
	 output [N-1:0] S);

	reg [3:0] counter;
	reg enabled, sel_A, sel_B;
	wire sum;

	always @(posedge clock) begin
		if (reset) begin
			counter <= 0;
			enabled <= 0;
		end else begin
			if (counter < N) begin
				counter <= counter + 1;
				enabled <= 1;
			end else
				enabled <= 0;
			sel_A <= A[counter];
			sel_B <= B[counter];
		end
	end

	reg [N-1:0] zero = 0;
	shift_register res(
		.data(sum),
		.clock(clock),
		.enabled(enabled),
		.direction(1'b1),
		.batch_set(reset),
		.data_batch(zero),
		.out(S)
	);
	serial_adder_block adder(clock, reset, sel_A, sel_B, sum);

endmodule

/******************************************************************************
 * Test Bench                                                                 *
 ******************************************************************************/

// Useful references:
// https://verificationguide.com/verilog-examples/
// https://www.design-reuse.com/articles/45979/system-verilog-macro-a-powerful-feature-for-design-verification-projects.html
// https://steveicarus.github.io/iverilog/usage/vvp_debug.html
// https://www.chipverify.com/verilog/

// TODO: mixed radix adder?

`define ASSERT(expected) \
	if (!(expected)) begin \
		$display("assertion \"``expected\" failed"); \
		$finish(2); \
	end

module adder_testbench;
	localparam N = 8;
	reg [N-1:0] A, B;

	wire [N-1:0] sum_rca, sum_csa, sum_cla_s, sum_cla, sum_sa;
	wire [13:0] sum_rnsa;
	wire [8:0] sum_qsda;
	wire carry_out_rca, carry_out_csa, carry_out_cla_s, carry_out_cla;
	wire [1:0] carry_out_qsda;

	reg clock = 0, reset;
	always #1 clock = ~clock;

	// carry_in is always 0
	ripple_carry_adder #(N)           rca(A, B, 1'b0, carry_out_rca, sum_rca);
	carry_select_adder #(N)           csa(A, B, 1'b0, carry_out_csa, sum_csa);
	carry_lookahead_adder_8bit        cla(A, B, 1'b0, carry_out_cla, sum_cla, /* ignoring propagate */, /* ignoring generate */);
	carry_lookahead_adder_slow #(N) cla_s(A, B, 1'b0, carry_out_cla_s, sum_cla_s);
	/* Here calculations are done with 14 bit because of internal overflow of RNS. */
	residue_number_system_adder_8bit rnsa({6'b0, A}, {6'b0, B}, sum_rnsa);
	QSD_9bit_adder                   qsda({1'b0, A}, {1'b0, B}, sum_qsda);
	serial_adder                       sa(clock, reset, A, B, sum_sa);

	localparam overflow_mask = (1 << N) - 1;
	integer a, b, expected_res;
	localparam fmt_str = {"t=%2d A=%3d B=%3d sum_rca=%3d sum_csa=%3d sum_cla=%3d",
		" sum_cla_s=%3d sum_rnsa=%3d sum_qsda=%3d sum_sa=%3d"};

	initial begin
`ifdef DEBUG
		$monitor(fmt_str, $time, A, B, sum_rca, sum_csa, sum_cla, sum_cla_s, sum_rnsa, sum_qsda, sum_sa);
		$dumpfile("adder_testbench.vcd");
		$dumpvars;
		// $dumpall;
		reset = 1; A = 0; B = 0; #10 reset = 0;
		#10
		`ASSERT(sum_rca === 0)
		`ASSERT(sum_csa === 0)
		`ASSERT(sum_cla === 0)
		`ASSERT(sum_cla_s === 0)
		`ASSERT(sum_rnsa === 0)
		`ASSERT(sum_qsda === 0)
		`ASSERT(sum_sa === 0)
		reset = 1;
		A = 1; B = 1;
		#10 reset = 0;
		#20
		`ASSERT(sum_rca === 2)
		`ASSERT(sum_csa === 2)
		`ASSERT(sum_cla === 2)
		`ASSERT(sum_cla_s === 2)
		`ASSERT(sum_rnsa === 2)
		`ASSERT(sum_qsda === 2)
		`ASSERT(sum_sa === 2)
		// 8 + 3 takes some time to stabilize.
		reset = 1;
		A = 8; B = 3;
		#10 reset = 0;
		#20
		`ASSERT(sum_rca === 11)
		`ASSERT(sum_csa === 11)
		`ASSERT(sum_cla === 11)
		`ASSERT(sum_cla_s === 11)
		`ASSERT(sum_rnsa === 11)
		`ASSERT(sum_qsda === 11)
		`ASSERT(sum_sa === 11)
		reset = 1;
		A = 32-1; B = 32-1;
		#10 reset = 0;
		#20
		`ASSERT(sum_rca === 62)
		`ASSERT(sum_csa === 62)
		`ASSERT(sum_cla === 62)
		`ASSERT(sum_cla_s === 62)
		`ASSERT(sum_rnsa === 62)
		`ASSERT(sum_qsda === 62)
		`ASSERT(sum_sa === 62)
		reset = 1;
		A = 0; B = 7;
		#10 reset = 0;
		#20
		`ASSERT(sum_rca === 7)
		`ASSERT(sum_csa === 7)
		`ASSERT(sum_cla === 7)
		`ASSERT(sum_cla_s === 7)
		`ASSERT(sum_rnsa === 7)
		`ASSERT(sum_qsda === 7)
		`ASSERT(sum_sa === 7)
		reset = 1;
		A = 15; B = 9;
		#10 reset = 0;
		#20
		`ASSERT(sum_rca === 24)
		`ASSERT(sum_csa === 24)
		`ASSERT(sum_cla === 24)
		`ASSERT(sum_cla_s === 24)
		`ASSERT(sum_rnsa === 24)
		`ASSERT(sum_qsda === 24)
		`ASSERT(sum_sa === 24)
		reset = 1;
		A = 128; B = 64;
		#10 reset = 0;
		#20
		`ASSERT(sum_rca === 192)
		`ASSERT(sum_csa === 192)
		`ASSERT(sum_cla === 192)
		`ASSERT(sum_cla_s === 192)
		`ASSERT(sum_rnsa === 192)
		`ASSERT(sum_sa === 192)
`else
		for (a = 0; a < overflow_mask; a = a + 1) begin
			for (b = 0; b < a; b = b + 1) begin
				reset = 1;
				A = a;
				B = b;
				#10 reset = 0;
				expected_res = (a + b) & overflow_mask;
				# 20
				$write(fmt_str, $time, A, B, sum_rca, sum_csa, sum_cla,
					sum_cla_s, sum_rnsa%256, sum_qsda%256, sum_sa);
				$display(" sum=%3d", expected_res);
				`ASSERT(sum_rca   === expected_res)
				`ASSERT(sum_csa   === expected_res)
				`ASSERT(sum_cla   === expected_res)
				`ASSERT(sum_cla_s === expected_res)
				`ASSERT(sum_rnsa%256  === expected_res)
				`ASSERT(sum_qsda%256  === expected_res)
				`ASSERT(sum_sa === expected_res)
			end
		end
`endif
		$finish();
	end
endmodule
