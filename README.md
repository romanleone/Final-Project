# Final-Project
Full processor
module Processor (clk,rst,fin_out);
	input clk,rst;
	output [31:0] fin_out;
	wire [31:0] inst;
	wire [3:0] status;
	wire WB, ALUsrc, PCsrc,RW, MRW;
	wire [3:0] ALU_OP;
	wire [1:0] imm_sel;
	
	Control_unit a (clk,rst,inst,status,ALU_OP,imm_sel,WB,ALUsrc,PCsrc,RW, MRW);
	
	core b (clk, rst, status, PCsrc, ALUsrc, ALU_OP, MRW, WB, inst, RW, imm_sel, fin_out);
	
endmodule 
