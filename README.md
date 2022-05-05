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

module Processor_tb (clk, rst, fin_out);

	output reg clk, rst;
	output [31:0] fin_out;
	
	Processor run (clk,rst,fin_out);
	
	
	initial begin 
	clk=0;
	forever #5 clk=~clk;
	end
	initial begin 
	rst=1;
	#10 rst=0;
	end 
endmodule

module core (clk, reset, status, pcsrc, alusrc, aluop, mrw, wb, instr, regrw, immgen_ctrl, out);

	input clk, reset, pcsrc, alusrc, mrw, wb, regrw;
	input [3:0] aluop;
	output [31:0] instr;
	output [3:0] status;	
	input [1:0] immgen_ctrl;
	output [31:0] out;
	
	wire [4:0] rd, rs1, rs2;
	wire [31:0] instr;
	
	wire [31:0] pc_in, pc_out, rom_out, ram_out, alu_out;
	wire [31:0] pc_addA_out, pc_addB_out;
	wire [31:0] pcmux_out;
	
	assign pc_in = pcmux_out;
	
	wire [31:0] rf_out1, rf_out2, immgen_out, alumux_out, alurammux_out;
		
	assign out = alurammux_out;
	
	ProgramCounter pc(clk, reset, pc_in, pc_out);
	Adder32 addA(pc_out, 32'd4, pc_addA_out);
	Adder32 addB(pc_out, immgen_out, pc_addB_out);
	Mux2to1_32bit pcmux(pcsrc, pc_addA_out, pc_addB_out, pcmux_out);
	ROM rom(pc_out, rom_out);
	InstDecoder id(rom_out, rd, rs1, rs2, instr);
	Register rf(rf_out1, rf_out2, rs1, rs2, alurammux_out, rd, regrw, reset, clk);
	Mux2to1_32bit alumux(alusrc, rf_out2, immgen_out, alumux_out);
	ImmGen ig(instr, immgen_out, immgen_ctrl);
	ALU alu(rf_out1, alumux_out, aluop, 1'd0, alu_out, status);
	RAM ram(alu_out[7:0], mrw, clk, rf_out2, ram_out); 
	Mux2to1_32bit alurrammux(wb, ram_out, alu_out, alurammux_out);
	

endmodule

module Register(A, B, SA, SB, D, DA, W, rst, clk);
	input [4:0] SA, SB, DA;
	input W, clk, rst;
	output [31:0] A, B; 
	input [31:0] D; 
	wire [31:0] load_enable;
	

	
	wire [31:0] R0, R1,R2,R3,R4,R5,R6,R7,R8,R9,R10,R11,R12,R13,R14,R15,R16,R17,R18,R19,R20,R21,R22,R23,R24,R25,R26,
	R27,R28,R29,R30,R31;
	
	Decoder dcode (DA, W,load_enable);
	
	
	lab3 reg0 (R0, D, clk, rst, load_enable[0]);
	lab3 reg1 (R1, D, clk, rst, load_enable[1]);
	lab3 reg2 (R2, D, clk, rst,load_enable[2]);
	lab3 reg3 (R3, D, clk, rst,load_enable[3]);
	lab3 reg4 (R4, D, clk, rst,load_enable[4]);
	lab3 reg5 (R5, D, clk, rst,load_enable[5]);
	lab3 reg6 (R6, D, clk, rst,load_enable[6]);
	lab3 reg7 (R7, D, clk, rst,load_enable[7]);
	lab3 reg8 (R8, D, clk, rst,load_enable[8]);
	lab3 reg9 (R9, D, clk, rst,load_enable[9]);
	lab3 reg10 (R10, D, clk, rst,load_enable[10]);
	lab3 reg11 (R11, D, clk, rst,load_enable[11]);
	lab3 reg12 (R12, D, clk, rst,load_enable[12]);
	lab3 reg13 (R13, D, clk, rst,load_enable[13]);
	lab3 reg14 (R14, D, clk, rst,load_enable[14]);
	lab3 reg15 (R15, D, clk, rst,load_enable[15]);
	lab3 reg16 (R16, D, clk, rst,load_enable[16]);
	lab3 reg17 (R17, D, clk, rst,load_enable[17]);
	lab3 reg18 (R18, D, clk, rst,load_enable[18]);
	lab3 reg19 (R19, D, clk, rst,load_enable[19]);
	lab3 reg20 (R20, D, clk, rst,load_enable[20]);
	lab3 reg21 (R21, D, clk, rst,load_enable[21]);
	lab3 reg22 (R22, D, clk, rst,load_enable[22]);
	lab3 reg23 (R23, D, clk, rst,load_enable[23]);
	lab3 reg24 (R24, D, clk, rst,load_enable[24]);
	lab3 reg25 (R25, D, clk, rst,load_enable[25]);
	lab3 reg26 (R26, D, clk, rst,load_enable[26]);
	lab3 reg27 (R27, D, clk, rst,load_enable[27]);
	lab3 reg28 (R28, D, clk, rst,load_enable[28]);
	lab3 reg29 (R29, D, clk, rst,load_enable[29]);
	lab3 reg30 (R30, D, clk, rst,load_enable[30]);
	
	assign R31 = 32'b0;
	
	Mux32to1_5bit muxA (A,R0,R1,R2,R3,R4,R5,R6,R7,R8,R9,R10,R11,R12,R13,R14,R15,R16,R17,R18,R19,R20,R21,R22,R23,R24,R25,R26,R27,R28,R29,R30,R31, SA);
	Mux32to1_5bit muxB (B,R0, R1,R2,R3,R4,R5,R6,R7,R8,R9,R10,R11,R12,R13,R14,R15,R16,R17,R18,R19,R20,R21,R22,R23,R24,R25,R26,R27,R28,R29,R30,R31, SB);
endmodule

module Decoder(select, enable, x);

	input [4:0] select;
	input enable;
	
	output reg [31:0] x;
	
	always @(select)
	begin
		if (enable==1)
			case (select)
				5'd0: x <= 32'b00000000000000000000000000000001;
				5'd1: x <= 32'b00000000000000000000000000000010;
				5'd2: x <= 32'b00000000000000000000000000000100;
				5'd3: x <= 32'b00000000000000000000000000001000;
				5'd4: x <= 32'b00000000000000000000000000010000;
				5'd5: x <= 32'b00000000000000000000000000100000;
				5'd6: x <= 32'b00000000000000000000000001000000;
				5'd7: x <= 32'b00000000000000000000000010000000;
				5'd8: x <= 32'b00000000000000000000000100000000;
				5'd9: x <= 32'b00000000000000000000001000000000;
				5'd10: x <= 32'b00000000000000000000010000000000;
				5'd11: x <= 32'b00000000000000000000100000000000;
				5'd12: x <= 32'b00000000000000000001000000000000;
				5'd13: x <= 32'b00000000000000000010000000000000;
				5'd14: x <= 32'b00000000000000000100000000000000;
				5'd15: x <= 32'b00000000000000001000000000000000;
				5'd16: x <= 32'b00000000000000010000000000000000;
				5'd17: x <= 32'b00000000000000100000000000000000;
				5'd18: x <= 32'b00000000000001000000000000000000;
				5'd19: x <= 32'b00000000000010000000000000000000;
				5'd20: x <= 32'b00000000000100000000000000000000;
				5'd21: x <= 32'b00000000001000000000000000000000;
				5'd22: x <= 32'b00000000010000000000000000000000;
				5'd23: x <= 32'b00000000100000000000000000000000;
				5'd24: x <= 32'b00000001000000000000000000000000;
				5'd25: x <= 32'b00000010000000000000000000000000;
				5'd26: x <= 32'b00000100000000000000000000000000;
				5'd27: x <= 32'b00001000000000000000000000000000;
				5'd28: x <= 32'b00010000000000000000000000000000;
				5'd29: x <= 32'b00100000000000000000000000000000;
				5'd30: x <= 32'b01000000000000000000000000000000;
				5'd31: x <= 32'b10000000000000000000000000000000;
			endcase
			else if (enable==0) x <= 32'b00000000000000000000000000000000;
	end
	
endmodule

module Mux32to1_5bit(o, i0, i1, i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31, s);
   input [31:0] i0, i1, i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,
	i29,i30,i31;
   input [4:0] s;
	
   output reg [31:0] o;
 
	always @*
	begin
		case (s)
			5'b00000 : o <= i0;
			5'b00001 : o <= i1;
			5'b00010 : o <= i2;
			5'b00011 : o <= i3;
			5'b00100 : o <= i4;
			5'b00101 : o <= i5;
			5'b00110 : o <= i6;
			5'b00111 : o <= i7;
			5'b01000 : o <= i8;
			5'b01001 : o <= i9;
			5'b01010 : o <= i10;
			5'b01011 : o <= i11;
			5'b01100 : o <= i12;
			5'b01101 : o <= i14;
			5'b01110 : o <= i15;
			5'b01111 : o <= i16;
			5'b10000 : o <= i17;
			5'b10001 : o <= i18;
			5'b10010 : o <= i19;
			5'b10011 : o <= i20;
			5'b10100 : o <= i21;
			5'b10101 : o <= i22;
			5'b10110 : o <= i23;
			5'b10111 : o <= i24;
			5'b11000 : o <= i25;
			5'b11010 : o <= i26;
			5'b11011 : o <= i27;
			5'b11100 : o <= i28;
			5'b11101 : o <= i29;
			5'b11110 : o <= i30;
			5'b11111 : o <= i31;
		  default : o <= 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
		endcase
	end
endmodule

module lab3(out, in, clk, rst,load);
	parameter N=32;
	input [N-1:0] in; 
	input load, clk, rst;
	
	output reg [31:0] out; 
	
	always @(posedge clk or posedge rst)begin 
		if (rst==1) 
			out <= 0;
	
	
		else if (load==1) 
			out <=	in;
		else
			out <= out;
	end
	
endmodule 

module ROM (addy,inst);
	input [31:0] addy;
	output reg [31:0]inst;
	
	always@(addy) begin 
	
		case(addy)
			32'h0: inst= 32'h00450693;
			32'h4: inst= 32'h00100713;
			32'h8: inst= 32'h00b76463;
			32'h10: inst= 32'h0006a803;
			32'hc: inst= 32'h00008067;
			32'h14: inst= 32'h00068613;
			32'h18: inst= 32'h00070793;
			32'h1c: inst= 32'hffc62883;
			32'h20: inst= 32'h01185a63;
			32'h24: inst= 32'h01162023;
			32'h28: inst= 32'hfff78793;
			32'h2c: inst= 32'hffc60613;
			32'h30: inst= 32'hfe0796e3;
			32'h34: inst= 32'h00279793;
			32'h38: inst= 32'h00f50763;
			32'h3c: inst= 32'h0107a023;
			32'h40: inst= 32'h00170713;
			32'h44: inst= 32'h00468693;
			32'h48: inst= 32'hfc1ff06f;
			endcase
		end
endmodule 

module RAM (addy, WR, clk, Di, Do);
	
	input [7:0] addy;
	input WR, clk;
	input [31:0] Di;
	output [31:0] Do;
	wire [3:0] x;
	
	DecoderRAM c (addy[7:6], 1'b1, x);
	
	wire [31:0] dosig0,dosig1,dosig2,dosig3;
	
	RAM64x8 ram1x1 (addy[5:0], WR, clk, x[0], Di[31:24], dosig0[31:24]);
	RAM64x8 ram1x2 (addy[5:0], WR, clk, x[0], Di[23:16], dosig0[23:16]);
	RAM64x8 ram1x3 (addy[5:0], WR, clk, x[0], Di[15:8], dosig0[15:8]);
	RAM64x8 ram1x4 (addy[5:0], WR, clk, x[0], Di[7:0], dosig0[7:0]);
	
	RAM64x8 ram2x1 (addy[5:0], WR, clk, x[1], Di[31:24], dosig1[31:24]);
	RAM64x8 ram2x2 (addy[5:0], WR, clk, x[1], Di[23:16], dosig1[23:16]);
	RAM64x8 ram2x3 (addy[5:0], WR, clk, x[1], Di[15:8], dosig1[15:8]);
	RAM64x8 ram2x4 (addy[5:0], WR, clk, x[1], Di[7:0], dosig1[7:0]);
	
	RAM64x8 ram3x1 (addy[5:0], WR, clk, x[2], Di[31:24], dosig2[31:24]);
	RAM64x8 ram3x2 (addy[5:0], WR, clk, x[2], Di[23:16], dosig2[23:16]);
	RAM64x8 ram3x3 (addy[5:0], WR, clk, x[2], Di[15:8], dosig2[15:8]);
	RAM64x8 ram3x4 (addy[5:0], WR, clk, x[2], Di[7:0], dosig2[7:0]);
	
	RAM64x8 ram4x1 (addy[5:0], WR, clk, x[3], Di[31:24], dosig3[31:24]);
	RAM64x8 ram4x2 (addy[5:0], WR, clk, x[3], Di[23:16], dosig3[23:16]);
	RAM64x8 ram4x3 (addy[5:0], WR, clk, x[3], Di[15:8], dosig3[15:8]);
	RAM64x8 ram4x4 (addy[5:0], WR, clk, x[3], Di[7:0], dosig3[7:0]);
	
	assign Do=x[0]? dosig0:32'bZ;
	assign Do=x[1]? dosig1:32'bZ;
	assign Do=x[2]? dosig2:32'bZ;
	assign Do=x[3]? dosig3:32'bZ;
endmodule 

module RAM64x8 (addy, WR, clk, CS, Di,Do);
	
	input [5:0] addy;
	input WR, clk, CS;
	input [7:0] Di;
	output reg[7:0]Do;

	
	reg [7:0] mem_array[5:0];
	reg [7:0] mem_out;
	
	always@(posedge clk)begin
		if (CS && WR)
			mem_array[addy]=Di;
		end 
	always@(posedge clk) begin 
		mem_out=mem_array[addy];
		Do <=CS ? mem_out : 8'b0;
	end 
	
	
endmodule

module DecoderRAM(select, enable, x);

	input [1:0] select;
	input enable;
	
	output reg [3:0] x;
	
	always @(select)
	begin
		if (enable==1)
			case (select)
				5'd0: x <= 4'b0001;
				5'd1: x <= 4'b0010;
				5'd2: x <= 4'b0100;
				5'd3: x <= 4'b1000;
			endcase
			else if (enable==0) x <= 4'b0000;
	end
	
endmodule 

module ProgramCounter(clk, reset, in, out);

	input clk, reset;
	input [31:0] in;
	output reg [31:0] out;
	
	initial out = 32'd0;
	
	always @(posedge clk or posedge reset) begin
		
		if (reset) begin
			out <= 32'd0;
		end
		else begin
			out <= in; 
		end
			
	end

endmodule 

module Mux2to1_8bit (F, A, B, out);

	input F;
	input [7:0] A, B;
	output reg [7:0] out;
	
	always@(*) begin
		if (F == 0) begin
			out <= A;
		end
		else if (F == 1) begin
			out <= B;
		end
	end

endmodule

module Mux2to1_32bit (F, A, B, out);

	input F;
	input [31:0] A, B;
	output reg [31:0] out;
	
	always@(*) begin
		if (F == 0) begin
			out <= A;
		end
		else if (F == 1) begin
			out <= B;
		end
	end

endmodule 

module InstDecoder(inst, rd, rs1, rs2, instr);

	input [31:0] inst;
	output [4:0] rd, rs1, rs2;
	output [31:0] instr;
	
	assign rd = inst[11:7];
	assign rs1 = inst[19:15];
	assign rs2 = inst[24:20];
	assign instr = inst;
			
endmodule 

module ImmGen(imm_in, imm_out, instruction_type);
	input [31:0] imm_in;
	input [1:0] instruction_type;
	output [31:0] imm_out;
	reg [31:0] imm_out_reg;

   assign imm_out = imm_out_reg;
	
   always @(imm_in)
		case(instruction_type)
			2'b01: imm_out_reg <= {{21{imm_in[31]}}, imm_in[30:20]}; //I-Type
			2'b10: imm_out_reg <= {{21{imm_in[31]}}, imm_in[30:25], imm_in[11:7]}; //S-Type
			2'b11: imm_out_reg <= {{20{imm_in[7]}}, imm_in[30:25], imm_in[11:8], {1{1'b0}}}; // B-Type
			default: imm_out_reg <= 32'bx;
		endcase
endmodule 

module Control_unit (clk,rst,inst,stat_flag,ALU_OP,imm_sel,WB,ALUsrc,PCsrc,RW, MRW);

input clk,rst;
input [31:0] inst;
input [3:0] stat_flag;
output reg WB, ALUsrc, PCsrc,RW, MRW;
output reg [3:0] ALU_OP;
output reg [1:0] imm_sel;
	
always @(inst or rst)
	if(rst==0)
	case(inst[6:0])
	
		7'b0110011:begin 
		ALUsrc=1'b0;
		RW= 1'b1;
		MRW=1'b0;
		WB=1'b0;
		PCsrc=1'b0;
		imm_sel= 2'b00;
		ALU_OP={inst[30],inst[14:12]};
		end 
		
		7'b0010011:begin  
		ALUsrc=1'b1;
		RW= 1'b1;
		MRW=1'b0;
		WB=1'b1;
		PCsrc=1'b0;
		imm_sel= 2'b01;
		ALU_OP={inst[30],inst[14:12]};
		end 
		
		7'b0000011:begin 
		ALUsrc=1'b1;
		RW= 1'b1;
		MRW=1'b0;
		WB=1'b1;
		PCsrc=1'b0;
		imm_sel= 2'b01;
		ALU_OP=4'b0000;
		end 
		
		7'b0100011:begin 
		ALUsrc=1'b1;
		RW= 1'b1;
		MRW=1'b0;
		WB=1'b1;
		PCsrc=1'b0;
		imm_sel= 2'b10;
		ALU_OP=4'b0000;
		end 
		
		7'b1100011:begin 
		ALUsrc=1'b0;
		RW=1'b0;
		MRW=1'b1;
		WB=1'b1;
		imm_sel=2'b11;
		ALU_OP=4'b1000;
		
		case (inst[14:12])
		3'b000:begin
		PCsrc=stat_flag[0]?1'b1:1'b0;
		end
		3'b100:begin 
		PCsrc=stat_flag[1]? 1'b1:1'b0;
		end 
		
		endcase
		end
		endcase
		else
		
		case(inst[6:0])
		7'b0000000:begin
		ALUsrc=1'b0;
		RW= 1'b0;
		MRW=1'b0;
		WB=1'b0;
		PCsrc=1'b0;
		imm_sel= 2'b00;
		ALU_OP=4'b0000;
		end
		endcase 
	endmodule 
	
	module Adder(A, B, out);

	input [7:0] A, B;
	output [7:0] out;
	
	assign out = A + B;
	
endmodule

module Adder32(A, B, out);

	input [31:0] A, B;
	output [31:0] out;
	
	assign out = A + B;
	
endmodule 

module ALU (A, B, FS, C0, F, status);
	input [31:0] A,B;
	input C0;
	input [3:0] FS;
	output [31:0] F;
	output [3:0] status;
	
	wire Z,N,C,V;
	wire temp;
	assign status= {V,C,N,Z};
	wire [31:0] A, B;
	
	assign N=F[31];
	assign Z= (F== 32'b0) ? 1'b1 : 1'b0 ;
	assign V = ((~A[31])&(~B[31])&F[31])|(A[31] & B[31] &(~F[31]));
	
	
	wire [31:0]and_out, or_out, xor_out, nor_out, add_out, left_out, right_out, i7;
	assign and_out = A & B;
	assign or_out = A | B;
	assign xor_out = A ^ B;
	assign nor_out = ~(A | B);
	
	AdderALU adderboi (A, B, C0,add_out, C);
	
	Shifter shiftboi (A, B[4:0], left_out, right_out);
	
	assign i7= 32'b0;
	
	mux8 mainmux (F, and_out, or_out, xor_out, nor_out, add_out, left_out, right_out,i7, FS[2:0]);
endmodule 

module Shifter(a, b, left_shift, right_shift);

	input [31:0] a;
	input [4:0] b;
	
	output [31:0] left_shift;
	output [31:0] right_shift;
	
	assign left_shift = a << b;
	assign right_shift = a>>b;
	
endmodule 

module AdderALU(A, B, Cin, S, Cout);
	 input [31:0] A, B; 
	 input Cin;
	 output [31:0] S; 
	 output Cout;
	 
	 wire [32:0] carry;
	 assign carry[0] = Cin;
	 assign Cout= carry[32];
	 
	 genvar i;
	 generate 
	 for (i=0; i<=31; i=i+1) begin: full_adders
		Full_Adder adder_inst (A[i], B[i], carry[i], S[i], carry[i+1]);
	end 
	endgenerate 
	
endmodule
	 
module Full_Adder(A,B,Cin, S, Cout);
	input A,B,Cin;
	output S, Cout;
	

	assign {Cout, S} = A+B+Cin;
endmodule 

module mux8(o,i0,i1,i2,i3,i4,i5,i6,i7,s);
	input [2:0] s;
	input [31:0]i0,i1,i2,i3,i4,i5,i6,i7;
	output reg [31:0] o;
	
	always @*
	begin 
		case(s)
			3'd0:o=i0;
			3'd1:o=i1;
			3'd2:o=i2;
			3'd3:o=i3;
			3'd4:o=i4;
			3'd5:o=i5;
			3'd6:o=i6;
			3'd7:o=i7;
		endcase
	end 
	
endmodule 
