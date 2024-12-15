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
                 $time, , "correct    = %b\n", correct);


        // add
        // op = 2'b00;

        // mult
        op = 2'b11;
        
        // ADD BUGS

        // NOTE: pred is the output Z3 gave me translated into binary.  It is essentially just
        // a check for me to make sure my Z3Py FPU model was accurate to the verilog implementation

        // IF BRANCH BUG
        // a       = 32'b1_10000000_00000000100100010000010;
        // b       = 32'b0_10000000_00000000100100001111100;
        // // pred set to 0 here because Z3 could not give me "undefined" as an output
        // pred    = 32'd0;
        // correct = 32'b1_01101011_10000000000000000000000;

        // IF BRANCH FIX
        // a       = 32'b00010010100000000000000100001000;
        // b       = 32'b10001010111111100100000000000000;
        // pred    = 32'b00010010100000000000000000001010;
        // correct = 32'b00010010100000000000000000001010;

        // ROUNDING FIX
        // a       = 32'b00010010100000000000000100001000;
        // b       = 32'b10001010111111100100000000000000;
        // pred    = 32'b00010010000000000000000000010011;
        // correct = 32'b00010010100000000000000000001010;

        // MUL BUGS

        // DOESNT PROPERLY HANDLE RESULT BEING DENORM
        // a           = 32'b0_00000010_01001010100110011100110;
        // b           = 32'b0_01001111_11100011011110001110110;
        // pred        = 32'b0_11010011_00111000001011100010101;
        // correct     = 32'b0_00000000_00000000000000000000000;
        
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
