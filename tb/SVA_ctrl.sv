/* 
 * This file holds the assertions for or1200_ctrl
 * Author: Saqib Khan
 */

`include "../rtl/verilog/or1200_defines.v"


module SVA_ctrl (
  // I/O
  input							clk,
  input							rst,
  input							id_freeze,
  input							ex_freeze /* verilator public */,
  input							wb_freeze /* verilator public */,
  input							if_flushpipe,
  input							id_flushpipe,
  input							ex_flushpipe,
  input							wb_flushpipe,
  input							extend_flush,
  input							except_flushpipe,
  input     			                      	abort_mvspr,
  input		[31:0]					if_insn,
  input	[31:0]						id_insn,
  input	[31:0]						ex_insn /* verilator public */,
  input	[`OR1200_BRANCHOP_WIDTH-1:0]			ex_branch_op,
  input	[`OR1200_BRANCHOP_WIDTH-1:0]			id_branch_op,
  input							ex_branch_taken,
  input	[`OR1200_REGFILE_ADDR_WIDTH-1:0]		rf_addrw,
  input	[`OR1200_REGFILE_ADDR_WIDTH-1:0]		rf_addra,
  input	[`OR1200_REGFILE_ADDR_WIDTH-1:0]		rf_addrb,
  input							rf_rda,
  input							rf_rdb,
  input	[`OR1200_ALUOP_WIDTH-1:0]			alu_op,
  input [`OR1200_ALUOP2_WIDTH-1:0] 			alu_op2,
  input	[`OR1200_MACOP_WIDTH-1:0]			mac_op,
  input	[`OR1200_RFWBOP_WIDTH-1:0]			rfwb_op,
  input  [`OR1200_FPUOP_WIDTH-1:0] 			fpu_op,     
  input							pc_we,
  input	[31:0]						wb_insn,
  input	[31:2]						id_branch_addrtarget,
  input	[31:2]						ex_branch_addrtarget,
  input	[`OR1200_SEL_WIDTH-1:0]				sel_a,
  input	[`OR1200_SEL_WIDTH-1:0]				sel_b,
  input	[`OR1200_LSUOP_WIDTH-1:0]			id_lsu_op,
  input	[`OR1200_COMPOP_WIDTH-1:0]			comp_op,
  input	[`OR1200_MULTICYCLE_WIDTH-1:0]			multicycle,
  input  [`OR1200_WAIT_ON_WIDTH-1:0]	 		wait_on,   
  input	[4:0]						cust5_op,
  input	[5:0]						cust5_limm,
  input   [31:0]           		               	id_pc,
  input   [31:0]                        		ex_pc,
  input	[31:0]						id_simm,
  input	[31:0]						ex_simm,
  input							wbforw_valid,
  input							du_hwbkpt,
  input							sig_syscall,
  input							sig_trap,
  input							force_dslot_fetch,
  input							no_more_dslot,
  input							id_void,
  input							ex_void,
  input							ex_spr_read,
  input							ex_spr_write,
  input	[`OR1200_MACOP_WIDTH-1:0]			id_mac_op,
  input							id_macrc_op,
  input							ex_macrc_op,
  input							rfe,
  input							except_illegal,
  input  						dc_no_writethrough,
  input							du_flush_pipe
);

//Instructions in EX stage
property ex_delayslot1;
  @(posedge clk) disable iff (rst) (!ex_freeze & ex_delayslot_dsi & !ex_delayslot_nop) |-> ##1 (ex_delayslot_nop == 0 && ex_delayslot_dsi == 0);
endproperty
assert property (ex_delayslot1);


endmodule

module Wrapper;
bind or1200_ctrl SVA_ctrl wrp (
  .clk(clk),
  .rst(rst),
  .id_freeze(id_freeze),
  .ex_freeze(ex_freeze ),
  .wb_freeze(wb_freeze ),
  .if_flushpipe(if_flushpipe),
  .id_flushpipe(id_flushpipe),
  .ex_flushpipe(ex_flushpipe),
  .wb_flushpipe(wb_flushpipe),
  .extend_flush(extend_flush),
  .except_flushpipe(except_flushpipe),
  .abort_mvspr(abort_mvspr ),
  .if_insn(if_insn),
  .id_insn(id_insn),
  .ex_insn(ex_insn ),
  .ex_branch_op(ex_branch_op),
  .id_branch_op(id_branch_op),
  .ex_branch_taken(ex_branch_taken),
  .rf_addrw(rf_addrw),
  .rf_addra(rf_addra),
  .rf_addrb(rf_addrb),
  .rf_rda(rf_rda),
  .rf_rdb(rf_rdb),
  .alu_op(alu_op),
  .alu_op2(alu_op2),
  .mac_op(mac_op),
  .rfwb_op(rfwb_op),
  .fpu_op(fpu_op),
  .pc_we(pc_we),
  .wb_insn(wb_insn),
  .id_branch_addrtarget(id_branch_addrtarget),
  .ex_branch_addrtarget(ex_branch_addrtarget),
  .du_hwbkpt(du_hwbkpt),
  .sig_syscall(sig_syscall),
  .sig_trap(sig_trap),
  .force_dslot_fetch(force_dslot_fetch),
  .no_more_dslot(no_more_dslot),
  .id_void(id_void),
  .ex_void(ex_void),
  .ex_spr_read(ex_spr_read),
  .ex_spr_write(ex_spr_write),
  .id_mac_op(id_mac_op),
  .id_macrc_op(id_macrc_op),
  .ex_macrc_op(ex_macrc_op),
  .rfe(rfe),
  .except_illegal(except_illegal),
  .dc_no_writethrough(dc_no_writethrough),
  .du_flush_pipe(du_flush_pipe)
);

endmodule
