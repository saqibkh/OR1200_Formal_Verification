/*
 * This file holds the assertions for or1200_genpc
 * Author: Saqib Khan
 */

`include "../rtl/verilog/or1200_defines.v"
import FSMProperties::*;

module SVA_genpc (
  input [31:2] pcreg, 
  input [31:2] ex_branch_addrtarget, 
  input flag, 
  input [2:0] branch_op,
  input [3:0] except_type,
  input except_start,
  input [31:0] operand_b,
  input [31:0] epcr,
  input spr_pc_we,
  input [31:0] spr_dat_i,
  input except_prefix,
  input [31:0] pc,
  input ex_branch_taken,
  input clk,
  input rst,
  input genpc_refetch,
  input genpc_refetch_r,
  input wait_lsu,
  input [2:0] pre_branch_op,
  input lsu_stall,
  du_flush_pipe,
  spr_dat_npc
);

//
// BRANCHOPs
//
localparam [2:0] OR1200_BRANCHOP_NOP = 3'd0,
                 OR1200_BRANCHOP_J = 3'd1,
                 OR1200_BRANCHOP_JR = 3'd2,
                 OR1200_BRANCHOP_BAL = 3'd3,
                 OR1200_BRANCHOP_BF = 3'd4,
                 OR1200_BRANCHOP_BNF = 3'd5,
                 OR1200_BRANCHOP_RFE = 3'd6;


//verify the PC update after invoking
//spr_pc_we
property PC_update_spr_pc_we;
@(posedge clk) disable iff (rst) spr_pc_we |-> (pc == spr_dat_i && ex_branch_taken == 0);
endproperty
assert_property_PC_update_spr_pc_we: assert property (PC_update_spr_pc_we);

//except_start
property PC_update_except_start;
@(pcreg | ex_branch_addrtarget | flag | branch_op | except_type | except_start | operand_b | epcr | spr_pc_we | spr_dat_i | except_prefix) (!du_flush_pipe && !spr_pc_we && except_start) |-> (pc == {(except_prefix ? `OR1200_EXCEPT_EPH1_P : `OR1200_EXCEPT_EPH0_P), except_type, `OR1200_EXCEPT_V} && (ex_branch_taken == 1));
endproperty
assert_property_PC_update_except_start: assert property (PC_update_except_start);

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//BRANCHOPs
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//BRANCHOP_NOP
property PC_update_branch_NOP;
@(pcreg | ex_branch_addrtarget | flag | branch_op | except_type | except_start | operand_b | epcr | spr_pc_we | spr_dat_i | except_prefix) (!du_flush_pipe && !spr_pc_we && !except_start && branch_op==`OR1200_BRANCHOP_NOP) |-> (pc == {pcreg + 30'd1, 2'b0}) && (ex_branch_taken == 0);
endproperty
assert_property_PC_update_branch_NOP: assert property (PC_update_branch_NOP);

//BRANCHOP_J
property PC_update_branch_J;
@(pcreg | ex_branch_addrtarget | flag | branch_op | except_type | except_start | operand_b | epcr | spr_pc_we | spr_dat_i | except_prefix) (!du_flush_pipe && !spr_pc_we && !except_start && branch_op==`OR1200_BRANCHOP_J) |-> (pc == {ex_branch_addrtarget, 2'b00}) && (ex_branch_taken == 1);
endproperty
assert_property_PC_update_branch_J: assert property (PC_update_branch_J);

//BRANCHOP_JR 
property PC_update_branch_JR;
@(pcreg | ex_branch_addrtarget | flag | branch_op | except_type | except_start | operand_b | epcr | spr_pc_we | spr_dat_i | except_prefix) (!du_flush_pipe && !spr_pc_we && !except_start && branch_op==`OR1200_BRANCHOP_JR) |-> (pc == operand_b) && (ex_branch_taken == 1);
endproperty
assert_property_PC_update_branch_JR: assert property (PC_update_branch_JR);


//BRANCHOP_RFE
property PC_update_branch_RFE;
@(pcreg | ex_branch_addrtarget | flag | branch_op | except_type | except_start | operand_b | epcr | spr_pc_we | spr_dat_i | except_prefix) (!du_flush_pipe && !spr_pc_we && !except_start && branch_op==`OR1200_BRANCHOP_RFE) |-> (pc == epcr && ex_branch_taken == 1);
endproperty
assert_property_PC_update_branch_RFE: assert property (PC_update_branch_RFE);




//verify genpc_refetch_r
assert_property_genpc_refetch_r_1: assert property ( @(posedge clk) disable iff(rst) (!genpc_refetch) |-> ##1 genpc_refetch_r == 0 );
assert_property_genpc_refetch_r_2: assert property ( @(posedge clk) disable iff(rst) (genpc_refetch) |-> ##1 genpc_refetch_r == 1 );

//verify wait_lsu
assert_property_wait_lsu_1: assert property ( @(posedge clk) disable iff (rst) (wait_lsu && ~|pre_branch_op) |-> ##1 wait_lsu == 0 );
assert_property_wait_lsu_2: assert property ( @(posedge clk) disable iff (rst) (!wait_lsu && |pre_branch_op && lsu_stall) |-> ##1 wait_lsu == 1 );


endmodule

module genpc_assert;

bind or1200_genpc SVA_genpc wrp (
  .pcreg(pcreg),
  .ex_branch_addrtarget(ex_branch_addrtarget),
  .flag(flag),
  .branch_op(branch_op),
  .except_type(except_type),
  .except_start(except_start),
  .operand_b(operand_b),
  .epcr(epcr),
  .spr_pc_we(spr_pc_we),
  .spr_dat_i(spr_dat_i),
  .except_prefix(except_prefix),
  .pc(pc),
  .ex_branch_taken(ex_branch_taken),
  .clk(clk),
  .rst(rst),
  .genpc_refetch(genpc_refetch),
  .genpc_refetch_r(genpc_refetch_r),
  .wait_lsu(wait_lsu),
  .pre_branch_op(pre_branch_op),
  .lsu_stall(lsu_stall),
  .du_flush_pipe(du_flush_pipe),
  .spr_dat_npc(spr_dat_npc)
);

endmodule
