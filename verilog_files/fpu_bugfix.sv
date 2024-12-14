//IEEE 754 Single Precision ALU
module fpu(clk, A, B, opcode, O);
	input clk;
	input [31:0] A, B;
	input [1:0] opcode;
	output [31:0] O;

	wire [31:0] O;
	wire [7:0] a_exponent;
	wire [23:0] a_mantissa;
	wire [7:0] b_exponent;
	wire [23:0] b_mantissa;

	reg        o_sign;
	reg [7:0]  o_exponent;
	reg [24:0] o_mantissa;


	reg [31:0] adder_a_in;
	reg [31:0] adder_b_in;
	wire [31:0] adder_out;

	reg [31:0] multiplier_a_in;
	reg [31:0] multiplier_b_in;
	wire [31:0] multiplier_out;

	reg [31:0] divider_a_in;
	reg [31:0] divider_b_in;
	wire [31:0] divider_out;

	assign O[31] = o_sign;
	assign O[30:23] = o_exponent;
	assign O[22:0] = o_mantissa[22:0];

	assign a_sign = A[31];
	assign a_exponent[7:0] = A[30:23];
	assign a_mantissa[23:0] = {1'b1, A[22:0]};

	assign b_sign = B[31];
	assign b_exponent[7:0] = B[30:23];
	assign b_mantissa[23:0] = {1'b1, B[22:0]};

	assign ADD = !opcode[1] & !opcode[0];
	assign SUB = !opcode[1] & opcode[0];
	assign DIV = opcode[1] & !opcode[0];
	assign MUL = opcode[1] & opcode[0];

	adder A1
	(
		.a(adder_a_in),
		.b(adder_b_in),
		.out(adder_out)
	);

	multiplier M1
	(
		.a(multiplier_a_in),
		.b(multiplier_b_in),
		.out(multiplier_out)
	);

	divider D1
	(
		.a(divider_a_in),
		.b(divider_b_in),
		.out(divider_out)
	);

	always @ (posedge clk) begin
		if (ADD) begin
			//If a is NaN or b is zero return a
			if ((a_exponent == 255 && a_mantissa != 0) || (b_exponent == 0) && (b_mantissa == 0)) begin
				o_sign = a_sign;
				o_exponent = a_exponent;
				o_mantissa = a_mantissa;
			//If b is NaN or a is zero return b
			end else if ((b_exponent == 255 && b_mantissa != 0) || (a_exponent == 0) && (a_mantissa == 0)) begin
				o_sign = b_sign;
				o_exponent = b_exponent;
				o_mantissa = b_mantissa;
			//if a or b is inf return inf
			end else if ((a_exponent == 255) || (b_exponent == 255)) begin
				o_sign = a_sign ^ b_sign;
				o_exponent = 255;
				o_mantissa = 0;
			end else begin // Passed all corner cases
				adder_a_in = A;
				adder_b_in = B;
				o_sign = adder_out[31];
				o_exponent = adder_out[30:23];
				o_mantissa = adder_out[22:0];
			end
		end else if (SUB) begin
			//If a is NaN or b is zero return a
			if ((a_exponent == 255 && a_mantissa != 0) || (b_exponent == 0) && (b_mantissa == 0)) begin
				o_sign = a_sign;
				o_exponent = a_exponent;
				o_mantissa = a_mantissa;
			//If b is NaN or a is zero return b
			end else if ((b_exponent == 255 && b_mantissa != 0) || (a_exponent == 0) && (a_mantissa == 0)) begin
				o_sign = b_sign;
				o_exponent = b_exponent;
				o_mantissa = b_mantissa;
			//if a or b is inf return inf
			end else if ((a_exponent == 255) || (b_exponent == 255)) begin
				o_sign = a_sign ^ b_sign;
				o_exponent = 255;
				o_mantissa = 0;
			end else begin // Passed all corner cases
				adder_a_in = A;
				adder_b_in = {~B[31], B[30:0]};
				o_sign = adder_out[31];
				o_exponent = adder_out[30:23];
				o_mantissa = adder_out[22:0];
			end
		end else if (DIV) begin
			divider_a_in = A;
			divider_b_in = B;
			o_sign = divider_out[31];
			o_exponent = divider_out[30:23];
			o_mantissa = divider_out[22:0];
		end else begin //Multiplication
			//If a is NaN return NaN
			if (a_exponent == 255 && a_mantissa != 0) begin
				o_sign = a_sign;
				o_exponent = 255;
				o_mantissa = a_mantissa;
			//If b is NaN return NaN
			end else if (b_exponent == 255 && b_mantissa != 0) begin
				o_sign = b_sign;
				o_exponent = 255;
				o_mantissa = b_mantissa;
			//If a or b is 0 return 0
			end else if ((a_exponent == 0) && (a_mantissa == 0) || (b_exponent == 0) && (b_mantissa == 0)) begin
				o_sign = a_sign ^ b_sign;
				o_exponent = 0;
				o_mantissa = 0;
			//if a or b is inf return inf
			end else if ((a_exponent == 255) || (b_exponent == 255)) begin
				o_sign = a_sign;
				o_exponent = 255;
				o_mantissa = 0;
			end else begin // Passed all corner cases
				multiplier_a_in = A;
				multiplier_b_in = B;
				o_sign = multiplier_out[31];
				o_exponent = multiplier_out[30:23];
				o_mantissa = multiplier_out[22:0];
			end
		end
	end
endmodule


module adder(a, b, out);
  input  [31:0] a, b;
  output [31:0] out;

  wire [31:0] out;
  reg a_sign;
  reg [7:0] a_exponent;
  reg [23:0] a_mantissa;
  reg b_sign;
  reg [7:0] b_exponent;
  reg [23:0] b_mantissa;

  reg o_sign;
  reg [7:0] o_exponent;
  reg [24:0] o_mantissa;

  reg [7:0] diff;
  reg [26:0] tmp_mantissa;
  reg [7:0] tmp_exponent;

  reg [27:0] t_mant;
  reg [27:0] t_o_mant;

  reg [27:0] pre_round_mant;
  reg [7:0] pre_round_exp;
  reg [23:0] extract_bits;
  reg [23:0] low_bits;
  reg [23:0] mask;
  reg [2:0] shifted_off_bits;


  reg  [7:0] i_e;
  reg  [24:0] i_m;
  wire [7:0] o_e;
  wire [26:0] o_m;

//   reg [26:0] pre_round_mant;
  reg [24:0] post_round_mant;

  addition_normaliser norm1
  (
    .in_e(i_e),
    .in_m(t_o_mant),
    .out_e(o_e),
    .out_m(o_m)
  );

  rounder round1
  (
	.in_mant(pre_round_mant),
	.out_mant(post_round_mant)
  );

  reg [23:0] sticky_in;
  wire sticky_out;

  vec_or_26 sticky_calc
  (
	.in(sticky_in),
	.index(diff),
	.out(sticky_out)
  );

  assign out[31] = o_sign;
  assign out[30:23] = o_exponent;
  assign out[22:0] = o_mantissa[22:0];

  always @ ( * ) begin
	// break up the operands into sign, exp, and mantissa
		a_sign = a[31];
		if(a[30:23] == 0) begin
			a_exponent = 8'b00000001;
			a_mantissa = {1'b0, a[22:0]};
		end else begin
			a_exponent = a[30:23];
			a_mantissa = {1'b1, a[22:0]};
		end
		b_sign = b[31];
		if(b[30:23] == 0) begin
			b_exponent = 8'b00000001;
			b_mantissa = {1'b0, b[22:0]};
		end else begin
			b_exponent = b[30:23];
			b_mantissa = {1'b1, b[22:0]};
		end
    if (a_exponent == b_exponent) begin // Equal exponents
      o_exponent = a_exponent;
      if (a_sign == b_sign) begin // Equal signs = add
        o_mantissa = a_mantissa + b_mantissa;
        //Signify to shift
        o_mantissa[24] = 1;
        o_sign = a_sign;
      end 
	  else begin // Opposite signs = subtract
		if(a_mantissa > b_mantissa) begin
		  o_mantissa = a_mantissa - b_mantissa;
		  o_sign = a_sign;
		end 
		else begin
		  o_mantissa = b_mantissa - a_mantissa;
		  o_sign = b_sign;
		end
	  end
    end 
	else begin //Unequal exponents
      if (a_exponent > b_exponent) begin // A is bigger
		// take on a's exponent
        o_exponent = a_exponent;
		// take a's sign
        o_sign = a_sign;
		// subtract exponents
		diff = a_exponent - b_exponent;
		// shift b to line up with a
		mask = (24'b111 << (diff - 3));
		sticky_in = b_mantissa;
		extract_bits = b_mantissa & mask;
		low_bits = extract_bits >> (diff - 3);
		shifted_off_bits[2:1] = low_bits[2:1];
		shifted_off_bits[0] = sticky_out;
        tmp_mantissa = {b_mantissa >> diff, shifted_off_bits};
        if (a_sign == b_sign) begin
			// add mantissa's if same sign
			t_mant = {a_mantissa, 3'b00} + tmp_mantissa;
		end
        else begin
			// subtract mantissa's is diff signs
			t_mant = {a_mantissa, 3'b00} - tmp_mantissa;
		end
      end 
	  else if (a_exponent < b_exponent) begin // B is bigger
		// take on b's exponent
        o_exponent = b_exponent;
		// take on b's sign
        o_sign = b_sign;
		// subtract exponents
        diff = b_exponent - a_exponent;
		// shift a to line up with b
        // tmp_mantissa = {3'b000, a_mantissa} >> diff;
		mask = (24'b111 << (diff - 3));
		sticky_in = a_mantissa;
		extract_bits = a_mantissa & mask;
		low_bits = extract_bits >> (diff - 3);
		shifted_off_bits[2:1] = low_bits[2:1];
		shifted_off_bits[0] = sticky_out;
        tmp_mantissa = {a_mantissa >> diff, shifted_off_bits};
        if (a_sign == b_sign) begin
			// add mantissa's if same sign
			t_mant = {b_mantissa, 3'b000} + tmp_mantissa;
        end 
		else begin
			// subtract mantissa's is diff signs
			t_mant = {b_mantissa, 3'b000} - tmp_mantissa;
        end
      end
    end
	// shift to account for overflow
    if(o_mantissa[24] == 1) begin
      o_exponent = o_exponent + 1;
      t_o_mant = t_mant >> 1;
    end 
	else begin
	  o_exponent = o_exponent;
      t_o_mant = t_mant;
	end
	// if need to normalize, normalize (don't have a 1 in MSB of mantissa)
	if((o_mantissa[23] != 1) && (o_exponent != 0)) begin
	  i_e = o_exponent;
	  i_m = t_o_mant;
	  //   o_exponent = o_e;
	  //   o_mantissa = o_m;
	  pre_round_mant = o_m;
	end
	else begin
		pre_round_mant = t_o_mant;
	end


	if(post_round_mant[24] == 1) begin
	  o_exponent = o_exponent + 1;
	  o_mantissa = post_round_mant >> 1;
	end 
	else begin
		// o_exponent = o_exponent;
	  o_mantissa = post_round_mant;
	end


  end
endmodule



module rounder(in_mant, out_mant);

	input [26:0] in_mant;
	output [24:0] out_mant;

	wire [26:0] in_mant;
	reg [24:0] out_mant;

	always_comb begin
		if(in_mant[2] == 0) begin
			out_mant = in_mant[26:3];
		end
		else if(in_mant[2] == 1 && (in_mant[1] == 1 || in_mant[0] == 1))begin
			out_mant = in_mant[26:3] + 1;
		end
		else if(in_mant[2:0] == 3'b100 && in_mant[3] == 1'b1) begin
			out_mant = in_mant[26:3] + 1;
		end
		else if(in_mant[2:0] == 3'b100 && in_mant[3] == 1'b0) begin
			out_mant = in_mant[26:3];
		end
	end

endmodule: rounder



module vec_or_26(in, index, out);

	input [23:0] in;
	input [7:0] index;
	wire [23:0] in;
	wire [7:0] index;
	output reg out;

    always_comb begin

        if(index == 0) begin
            out = 0; 
        end
        else if(index == 1) begin
            out = 0 | in[0]; 
        end
        else if(index == 2) begin
            out = |in[1:0]; 
        end
        else if(index == 3) begin
            out = |in[2:0]; 
        end
        else if(index == 4) begin
            out = |in[3:0]; 
        end
        else if(index == 5) begin
            out = |in[4:0]; 
        end
        else if(index == 6) begin
            out = |in[5:0]; 
        end
        else if(index == 7) begin
            out = |in[6:0]; 
        end
        else if(index == 8) begin
            out = |in[7:0]; 
        end
        else if(index == 9) begin
            out = |in[8:0]; 
        end
        else if(index == 10) begin
            out = |in[9:0]; 
        end
        else if(index == 11) begin
            out = |in[10:0]; 
        end
        else if(index == 12) begin
            out = |in[11:0]; 
        end
        else if(index == 13) begin
            out = |in[12:0]; 
        end
        else if(index == 14) begin
            out = |in[13:0]; 
        end
        else if(index == 15) begin
            out = |in[14:0]; 
        end
        else if(index == 16) begin
            out = |in[15:0]; 
        end
        else if(index == 17) begin
            out = |in[16:0]; 
        end
        else if(index == 18) begin
            out = |in[17:0]; 
        end
        else if(index == 19) begin
            out = |in[18:0]; 
        end
        else if(index == 20) begin
            out = |in[19:0]; 
        end
        else if(index == 21) begin
            out = |in[20:0]; 
        end
        else if(index == 22) begin
            out = |in[21:0]; 
        end
        else if(index == 23) begin
            out = |in[22:0]; 
        end
        else if(index == 24) begin
            out = |in[23:0]; 
        end
    end

endmodule: vec_or_26



module addition_normaliser(in_e, in_m, out_e, out_m);
  input [7:0] in_e;
  input [26:0] in_m;
  output [7:0] out_e;
  output [26:0] out_m;

  wire [7:0] in_e;
  wire [26:0] in_m;
  reg [7:0] out_e;
  reg [26:0] out_m;

  always @ ( * ) begin
		if (in_m[23:0] == 24'b000000000000000000000001) begin // added in bugfix 2
			out_e = in_e - 23;
			out_m = in_m << 23;
		end if (in_m[23:1] == 23'b00000000000000000000001) begin // added in bugfix 2
			out_e = in_e - 22;
			out_m = in_m << 22;
		end else if (in_m[23:2] == 22'b0000000000000000000001) begin // added in bugfix 2
			out_e = in_e - 21;
			out_m = in_m << 21;
		end else if (in_m[23:3] == 21'b000000000000000000001) begin
			out_e = in_e - 20;
			out_m = in_m << 20;
		end else if (in_m[23:4] == 20'b00000000000000000001) begin
			out_e = in_e - 19;
			out_m = in_m << 19;
		end else if (in_m[23:5] == 19'b0000000000000000001) begin
			out_e = in_e - 18;
			out_m = in_m << 18;
		end else if (in_m[23:6] == 18'b000000000000000001) begin
			out_e = in_e - 17;
			out_m = in_m << 17;
		end else if (in_m[23:7] == 17'b00000000000000001) begin
			out_e = in_e - 16;
			out_m = in_m << 16;
		end else if (in_m[23:8] == 16'b0000000000000001) begin
			out_e = in_e - 15;
			out_m = in_m << 15;
		end else if (in_m[23:9] == 15'b000000000000001) begin
			out_e = in_e - 14;
			out_m = in_m << 14;
		end else if (in_m[23:10] == 14'b00000000000001) begin
			out_e = in_e - 13;
			out_m = in_m << 13;
		end else if (in_m[23:11] == 13'b0000000000001) begin
			out_e = in_e - 12;
			out_m = in_m << 12;
		end else if (in_m[23:12] == 12'b000000000001) begin
			out_e = in_e - 11;
			out_m = in_m << 11;
		end else if (in_m[23:13] == 11'b00000000001) begin
			out_e = in_e - 10;
			out_m = in_m << 10;
		end else if (in_m[23:14] == 10'b0000000001) begin
			out_e = in_e - 9;
			out_m = in_m << 9;
		end else if (in_m[23:15] == 9'b000000001) begin
			out_e = in_e - 8;
			out_m = in_m << 8;
		end else if (in_m[23:16] == 8'b00000001) begin
			out_e = in_e - 7;
			out_m = in_m << 7;
		end else if (in_m[23:17] == 7'b0000001) begin
			out_e = in_e - 6;
			out_m = in_m << 6;
		end else if (in_m[23:18] == 6'b000001) begin
			out_e = in_e - 5;
			out_m = in_m << 5;
		end else if (in_m[23:19] == 5'b00001) begin
			out_e = in_e - 4;
			out_m = in_m << 4;
		end else if (in_m[23:20] == 4'b0001) begin
			out_e = in_e - 3;
			out_m = in_m << 3;
		end else if (in_m[23:21] == 3'b001) begin
			out_e = in_e - 2;
			out_m = in_m << 2;
		end else if (in_m[23:22] == 2'b01) begin
			out_e = in_e - 1;
			out_m = in_m << 1;
		end else begin // added in bugfix 2
			out_e = in_e;
			out_m = in_m;
		end
  end
endmodule

module multiplier(a, b, out);
  input  [31:0] a, b;
  output [31:0] out;

  wire [31:0] out;
	reg a_sign;
  reg [7:0] a_exponent;
  reg [23:0] a_mantissa;
	reg b_sign;
  reg [7:0] b_exponent;
  reg [23:0] b_mantissa;

  reg o_sign;
  reg [7:0] o_exponent;
  reg [24:0] o_mantissa;

	reg [47:0] product;

  assign out[31] = o_sign;
  assign out[30:23] = o_exponent;
  assign out[22:0] = o_mantissa[22:0];

	reg  [7:0] i_e;
	reg  [47:0] i_m;
	wire [7:0] o_e;
	wire [47:0] o_m;

	multiplication_normaliser norm1
	(
		.in_e(i_e),
		.in_m(i_m),
		.out_e(o_e),
		.out_m(o_m)
	);


  always @ ( * ) begin
		a_sign = a[31];
		if(a[30:23] == 0) begin
			a_exponent = 8'b00000001;
			a_mantissa = {1'b0, a[22:0]};
		end else begin
			a_exponent = a[30:23];
			a_mantissa = {1'b1, a[22:0]};
		end
		b_sign = b[31];
		if(b[30:23] == 0) begin
			b_exponent = 8'b00000001;
			b_mantissa = {1'b0, b[22:0]};
		end else begin
			b_exponent = b[30:23];
			b_mantissa = {1'b1, b[22:0]};
		end
    o_sign = a_sign ^ b_sign;
    o_exponent = a_exponent + b_exponent - 127;
    product = a_mantissa * b_mantissa;
		// Normalization
    if(product[47] == 1) begin
      o_exponent = o_exponent + 1;
      product = product >> 1;
    end else if((product[46] != 1) && (o_exponent != 0)) begin
      i_e = o_exponent;
      i_m = product;
      o_exponent = o_e;
      product = o_m;
    end
		o_mantissa = product[46:23];
	end
endmodule

module multiplication_normaliser(in_e, in_m, out_e, out_m);
  input [7:0] in_e;
  input [47:0] in_m;
  output [7:0] out_e;
  output [47:0] out_m;

  wire [7:0] in_e;
  wire [47:0] in_m;
  reg [7:0] out_e;
  reg [47:0] out_m;

  always @ ( * ) begin
	  if (in_m[46:41] == 6'b000001) begin
			out_e = in_e - 5;
			out_m = in_m << 5;
		end else if (in_m[46:42] == 5'b00001) begin
			out_e = in_e - 4;
			out_m = in_m << 4;
		end else if (in_m[46:43] == 4'b0001) begin
			out_e = in_e - 3;
			out_m = in_m << 3;
		end else if (in_m[46:44] == 3'b001) begin
			out_e = in_e - 2;
			out_m = in_m << 2;
		end else if (in_m[46:45] == 2'b01) begin
			out_e = in_e - 1;
			out_m = in_m << 1;
		end
  end
endmodule

module divider (a, b, out);
	input [31:0] a;
	input [31:0] b;
	output [31:0] out;

	wire [31:0] b_reciprocal;

	reciprocal recip
	(
		.in(b),
		.out(b_reciprocal)
	);

	multiplier mult
	(
		.a(a),
		.b(b_reciprocal),
		.out(out)
	);

endmodule

module reciprocal (in, out);
	input [31:0] in;

	output [31:0] out;

	wire [31:0] D;
	assign D = {1'b0, 8'h80, in[22:0]};

	wire [31:0] C1; //C1 = 48/17
	assign C1 = 32'h4034B4B5;
	wire [31:0] C2; //C2 = 32/17
	assign C2 = 32'h3FF0F0F1;
	wire [31:0] C3; //C3 = 2.0
	assign C3 = 32'h40000000;

	wire [31:0] N0;
	wire [31:0] N1;
	wire [31:0] N2;

	
	assign out[31] = in[31];
	assign out[22:0] = N2[22:0];
	assign out[30:23] = (D==9'b100000000)? 9'h102 - in[30:23] : 9'h101 - in[30:23];


	//Temporary connection wires
	wire [31:0] S0_2D_out;
	wire [31:0] S1_DN0_out;
	wire [31:0] S1_2min_DN0_out;
	wire [31:0] S2_DN1_out;
	wire [31:0] S2_2minDN1_out;

	wire [31:0] S0_N0_in;

	assign S0_N0_in = {~S0_2D_out[31], S0_2D_out[30:0]};

	//S0
	multiplier S0_2D
	(
		.a(C2),
		.b(D),
		.out(S0_2D_out)
	);

	adder S0_N0
	(
		.a(C1),
		.b(S0_N0_in),
		.out(N0)
	);

	//S1
	multiplier S1_DN0
	(
		.a(D),
		.b(N0),
		.out(S1_DN0_out)
	);

	adder S1_2minDN0
	(
		.a(C3),
		.b({~S1_DN0_out[31], S1_DN0_out[30:0]}),
		.out(S1_2min_DN0_out)
	);

	multiplier S1_N1
	(
		.a(N0),
		.b(S1_2min_DN0_out),
		.out(N1)
	);

	//S2
	multiplier S2_DN1
	(
		.a(D),
		.b(N1),
		.out(S2_DN1_out)
	);

	adder S2_2minDN1
	(
		.a(C3),
		.b({~S2_DN1_out[31], S2_DN1_out[30:0]}),
		.out(S2_2minDN1_out)
	);

	multiplier S2_N2
	(
		.a(N1),
		.b(S2_2minDN1_out),
		.out(N2)
	);

endmodule
