`default_nettype none

module fpu_tb();

    reg clk;
    reg [31:0] a, b;
    reg [1:0] op;
    reg [31:0] correct;
    reg [31:0] pred;
    //----------------------------------------------------------
    // outputs from the DUT are wire type
    wire [31:0] out;
    

    fpu dut (
        .clk(clk),
        .A(a),
        .B(b),
        .opcode(op),
        .O(out)
    );

    // adder dut (.a(a), .b(b), .out(out));

    always begin
        #100 clk = 0;
        #100 clk = 1;
        // clk = 0;
        // #100 clk = ~clk; // every 100 nanoseconds invert
    end

    initial begin
        
        $monitor($time, , "out        = %b", out, " | match: %b", pred == out, " | correct: %b\n", correct == out,
                //  $time, , "o_exponent = %b\n", dut.M1.o_exponent,
                //  $time, , "o_e        = %b\n", dut.M1.o_e,
                 $time, , "correct    = %b\n", correct);

        

        // $monitor($time, , "tmp_mantissa     = %b\n", dut.A1.tmp_mantissa,
        //          $time, , "a_mantissa       = %b\n", dut.A1.a_mantissa);

        // $monitor($time, , "mask         = %b |\n", 24'b111 << dut.A1.diff,
        //          $time, , "mask         = %b |\n", dut.A1.mask,
        //          $time, , "a_mantissa   = %b |\n", dut.A1.a_mantissa,
        //         //  $time, , "a_mantissa_s = %b |\n", (dut.A1.a_mantissa >> dut.A1.diff),
        //          $time, , "extract_bits = %b\n", dut.A1.extract_bits,
        //          $time, , "low_bits     = %b |\n", dut.A1.low_bits,
        //          $time, , "shifted_off_bits  = %b |\n", dut.A1.shifted_off_bits, 
        //          $time, , "tmp_mantissa      = %b |\n", dut.A1.tmp_mantissa,  
        //          $time, , "b_mantissa        = %b |\n", {dut.A1.b_mantissa, 3'b000},  
        //          $time, , "t_mant            = %b\n", dut.A1.t_mant,
        //          $time, , "pre_round_mant    = %b\n", dut.A1.pre_round_mant,
        //          $time, , "post_round_mant   = %b\n", dut.A1.post_round_mant,
        //          $time, , "o_mantissa        = %b |\n", dut.A1.o_mantissa,
        //          $time, , "correct           = %b\n", correct);

        // $monitor($time, , "tmp_mantissa         = %b\n", dut.A1.tmp_mantissa,
        //          $time, , "{b_mantissa, 3'b000} = %b\n", {dut.A1.b_mantissa, 3'b000},
        //          $time, , "t_mant               = %b\n", dut.A1.t_mant);

        // $monitor($time, , "o_m         = %b\n", dut.A1.o_m);

        // $monitor($time, , "i_m       = %b\n", dut.A1.i_m,
        //          $time, , "i_m[23:3] = %b\n", dut.A1.i_m[23:3],
        //          $time, , "i_e       = %b\n", dut.A1.i_e);

        // add
        // op = 2'b00;

        // mult
        op = 2'b11;
        
        // ADD BUGS

        // IF BRANCH BUG
        // a       = 32'b1_10000000_00000000100100010000010;
        // b       = 32'b0_10000000_00000000100100001111100;
        // correct = 32'b1_01101011_10000000000000000000000;

        // IF BRANCH FIX
        // a       = 32'b00010010100000000000000100001000;
        // b       = 32'b10001010111111100100000000000000;
        // correct = 32'b00010010100000000000000000001010;

        // ROUNDING FIX
        // a       = 32'b00010010100000000000000100001000;
        // b       = 32'b10001010111111100100000000000000;
        // pred    = 32'b00010010000000000000000000010011;
        // correct = 32'b00010010100000000000000000001010;

        // MUL BUGS

        // DOESNT PROPERLY HANDLE RESULT BEING DENORM
        // a           = 32'b00000001001001010100110011100110;
        // b           = 32'b00100111111100011011110001110110;
        // correct     = 32'b01101001100111000001011100010101;
        
        // DOESNT PROPERLY ROUND
        a       = 32'b00000011111000101101001000101101;
        b       = 32'b00111100111000110111010011010100;
        pred    = 32'b00000001010010011000011111100000;
        correct = 32'b00000001010010011000011111100001; 


        #400;
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        
        // @(posedge clock);
        // @(posedge clock);
        // @(posedge clock);
        // @(posedge clock);
        // #400;

        $finish;

    end

endmodule: fpu_tb
