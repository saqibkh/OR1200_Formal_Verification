/* 
 * This file holds the assertions for or1200_except
 * Author: Saqib Khan
 */

import FSMProperties::*;
`include "../rtl/verilog/or1200_defines.v"

module SVA_except (
  input wire clk, reset,
  input wire except_flushpipe, pc_we, icpu_ack_i, icpu_err_i,
  input wire genpc_freeze, if_stall, id_freeze,
  input [31:0] epcr, 
  input [31:0] wb_pc, 
  input [31:0] ex_pc, 
  input ex_dslot, delayed1_ex_dslot, delayed2_ex_dslot,
  input [31:0] dl_pc, 
  input [31:0] id_pc,
  input [3:0] except_type,
  input [13:0] except_trig,
  input [2:0] state
);

localparam [2:0] OR1200_EXCEPTFSM_IDLE    =    3'd0,
		 OR1200_EXCEPTFSM_FLU1	  =    3'd1,
		 OR1200_EXCEPTFSM_FLU2	  =    3'd2,
		 OR1200_EXCEPTFSM_FLU3	  =    3'd3,
		 OR1200_EXCEPTFSM_FLU4	  =    3'd4,
		 OR1200_EXCEPTFSM_FLU5	  =    3'd5;

localparam [3:0] OR1200_EXCEPT_UNUSED	= 	4'hf,
		 OR1200_EXCEPT_TRAP		= 	4'he,
		 OR1200_EXCEPT_FLOAT	= 	4'hd,
		 OR1200_EXCEPT_SYSCALL	= 	4'hc,
		 OR1200_EXCEPT_RANGE	= 	4'hb,
		 OR1200_EXCEPT_ITLBMISS	= 	4'ha,
		 OR1200_EXCEPT_DTLBMISS	= 	4'h9,
		 OR1200_EXCEPT_INT		= 	4'h8,
		 OR1200_EXCEPT_ILLEGAL	= 	4'h7,
		 OR1200_EXCEPT_ALIGN	= 	4'h6,
		 OR1200_EXCEPT_TICK		= 	4'h5,
		 OR1200_EXCEPT_IPF		= 	4'h4,
		 OR1200_EXCEPT_DPF		= 	4'h3,
		 OR1200_EXCEPT_BUSERR	= 	4'h2,
		 OR1200_EXCEPT_RESET	= 	4'h1,
		 OR1200_EXCEPT_NONE		= 	4'h0;


sequence acc_except_1;
  !(except_type == OR1200_EXCEPT_TICK);
endsequence

sequence acc_except_2;
  !(except_type == OR1200_EXCEPT_INT) and acc_except_1;
endsequence

sequence acc_except_3;
  !(except_type == OR1200_EXCEPT_FLOAT) and acc_except_2;
endsequence

sequence acc_except_4;
  !(except_type == OR1200_EXCEPT_RANGE) and acc_except_3;
endsequence

sequence acc_except_5;
  !(except_type == OR1200_EXCEPT_DPF) and acc_except_4;
endsequence

sequence acc_except_6;
  !(except_type == OR1200_EXCEPT_SYSCALL) and acc_except_5;
endsequence

sequence acc_except_7;
  !(except_type == OR1200_EXCEPT_TRAP) and acc_except_6;
endsequence

sequence acc_except_8;
  !(except_type == OR1200_EXCEPT_DTLBMISS) and acc_except_7;
endsequence

sequence acc_except_9;
  !(except_type == OR1200_EXCEPT_ALIGN) and acc_except_8;
endsequence

sequence acc_except_10;
  !(except_type == OR1200_EXCEPT_ILLEGAL) and acc_except_9;
endsequence

sequence acc_except_11;
  !(except_type == OR1200_EXCEPT_IPF) and !(except_type == OR1200_EXCEPT_BUSERR) and acc_except_10;
endsequence

property priority_check1;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[1]) |-> ##1 (acc_except_1);
endproperty
assert_priority_check1: assert property (priority_check1);

property priority_check2;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[2]) |-> ##1 (acc_except_2);
endproperty
assert_priority_check2: assert property (priority_check2);

property priority_check3;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[3]) |-> ##1 (acc_except_3);
endproperty
assert_priority_check3: assert property (priority_check3);

property priority_check4;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[5]) |-> ##1 (acc_except_4);
endproperty
assert_priority_check4: assert property (priority_check4);

property priority_check5;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[6]) |-> ##1 (acc_except_5);
endproperty
assert_priority_check5: assert property (priority_check5);

property priority_check6;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[7]) |-> ##1 (acc_except_6);
endproperty
assert_priority_check6: assert property (priority_check6);

property priority_check7;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[8]) |-> ##1 (acc_except_7);
endproperty
assert_priority_check7: assert property (priority_check7);

property priority_check8;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[9]) |-> ##1 (acc_except_8);
endproperty
assert_priority_check8: assert property (priority_check8);

property priority_check9;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[10]) |-> ##1 (acc_except_9);
endproperty
assert_priority_check9: assert property (priority_check9);

property priority_check10;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[12]) |-> ##1 (acc_except_10);
endproperty
assert_priority_check10: assert property (priority_check10);

property priority_check11;
@(posedge clk) disable iff(reset) (state == OR1200_EXCEPTFSM_IDLE && except_trig[13]) |-> ##1 (acc_except_11);
endproperty
assert_priority_check11: assert property (priority_check11);

property reset_state;
@(negedge reset) reset |=> (state == OR1200_EXCEPTFSM_IDLE);
endproperty
//assert_check_reset_FSM_IDLE: assert property (reset_state);

// state transition for except module

assert_property_FSM_IDLE_FLU1: assert property (FSMValidTransition(clk, (state == OR1200_EXCEPTFSM_IDLE), 
		(except_flushpipe || pc_we), (state == OR1200_EXCEPTFSM_FLU1)));

assert_property_FSM_FLU1_FLU2: assert property (FSMValidTransition(clk, (state == OR1200_EXCEPTFSM_FLU1), 
	(icpu_ack_i || icpu_err_i || genpc_freeze), (state == OR1200_EXCEPTFSM_FLU2)));

assert_property_FSM_FLU2_IDLE: assert property (FSMValidTransition(clk, (state == OR1200_EXCEPTFSM_FLU2), 
		(except_type == OR1200_EXCEPT_TRAP), (state == OR1200_EXCEPTFSM_IDLE)));

assert_property_FSM_FLU2_FLU3: assert property (FSMValidTransition(clk, (state == OR1200_EXCEPTFSM_FLU2), 
		!(except_type == OR1200_EXCEPT_TRAP), (state == OR1200_EXCEPTFSM_FLU3)));

assert_property_FSM_FLU3_FLU4: assert property (FSMValidTransition(clk, (state == OR1200_EXCEPTFSM_FLU3), 
		1, (state == OR1200_EXCEPTFSM_FLU4)));

assert_property_FSM_FLU4_FLU5: assert property (FSMValidTransition(clk, (state == OR1200_EXCEPTFSM_FLU4), 
		1, (state == OR1200_EXCEPTFSM_FLU5)));

assert_property_FSM_FLU5_IDLE: assert property (FSMValidTransition(clk, (state == OR1200_EXCEPTFSM_FLU5), 
		(!if_stall && !id_freeze), (state == OR1200_EXCEPTFSM_IDLE)));

property reset_epcr;
@(negedge reset) reset |=> (epcr == 0);
endproperty
//assert_property_reset_epcr: assert property (reset_epcr);

property except_handler_1;
  @(posedge clk) disable iff (reset) ($rose(except_type == OR1200_EXCEPT_ITLBMISS) || $rose(except_type == OR1200_EXCEPT_ILLEGAL) || $rose(OR1200_EXCEPT_ALIGN)) |-> (($past(ex_dslot) && (epcr == $past(wb_pc))) || (!$past(ex_dslot) && (epcr == $past(ex_pc))));
endproperty
assert_property_handler_1: assert property (except_handler_1);

property except_ipf;
@(posedge clk) disable iff (reset)
($rose(except_type == OR1200_EXCEPT_IPF) |-> (($past(ex_dslot) && (epcr == $past(wb_pc))) || (!$past(ex_dslot) && (epcr == $past(id_pc)))));
endproperty
assert_property_except_ipf: assert property (except_ipf);

property except_buserr;
@(posedge clk) disable iff (reset)
($rose(except_type == OR1200_EXCEPT_BUSERR) |-> ((!$past(ex_dslot) && $past(delayed1_ex_dslot) && (epcr == $past(dl_pc))) || 
	(!$past(ex_dslot) && !$past(delayed1_ex_dslot) && (epcr == $past(ex_pc))) || ($past(ex_dslot) && (epcr == $past(wb_pc))) || (!$past(ex_dslot) && (epcr == $past(ex_pc)))));
endproperty
assert_property_except_buserr: assert property (except_buserr);

property except_dtlbmiss_dpf;
@(posedge clk) disable iff (reset)
($rose(except_type == OR1200_EXCEPT_DTLBMISS) |-> (($past(ex_dslot) && (epcr == $past(wb_pc))) || (!$past(ex_dslot) && $past(delayed1_ex_dslot) && (epcr == $past(dl_pc)))
	|| (!$past(ex_dslot) && !$past(delayed1_ex_dslot) && (epcr == $past(ex_pc)))));
endproperty
assert_property_except_dtlbmiss_dpf: assert property (except_dtlbmiss_dpf);

property except_trap;
@(posedge clk) disable iff (reset)
($rose(except_type == OR1200_EXCEPT_TRAP) |-> (($past(ex_dslot) && (epcr == $past(wb_pc))) || (!$past(ex_dslot) && $past(delayed1_ex_dslot) && (epcr == $past(id_pc)))
	|| (!$past(ex_dslot) && !$past(delayed1_ex_dslot) && (epcr == $past(ex_pc)))));
endproperty
assert_property_except_trap: assert property (except_trap);

property except_syscall;
@(posedge clk) disable iff (reset)
($rose(except_type == OR1200_EXCEPT_SYSCALL) |-> (($past(ex_dslot) && (epcr == $past(wb_pc))) || (!$past(ex_dslot) && (epcr == $past(id_pc)))));
endproperty
assert_property_except_syscall: assert property (except_syscall);

property except_range;
@(posedge clk) disable iff (reset)
($rose(except_type == OR1200_EXCEPT_RANGE) |-> (($past(ex_dslot) && (epcr == $past(wb_pc))) || (!$past(ex_dslot) && $past(delayed1_ex_dslot) && (epcr == $past(dl_pc)))
	|| (!$past(ex_dslot) && !$past(delayed1_ex_dslot) && $past(delayed2_ex_dslot) && (epcr == $past(id_pc))) || (!$past(ex_dslot) && !$past(delayed1_ex_dslot) && !$past(delayed2_ex_dslot) && (epcr == $past(ex_pc)))));
endproperty
assert_property_except_range: assert property (except_range);

property except_handler_2;
@(posedge clk) disable iff (reset)
($rose(except_type == OR1200_EXCEPT_FLOAT) || $rose(except_type == OR1200_EXCEPT_INT) || $rose(except_type == OR1200_EXCEPT_TICK) |-> (epcr == $past(id_pc)));
endproperty
assert_property_except_handler_2: assert property (except_handler_2);

cover_EXCEPT_TRAP: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_TRAP));
cover_EXCEPT_FLOAT: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_FLOAT));
cover_EXCEPT_SYSCALL: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_SYSCALL));
cover_EXCEPT_RANGE: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_RANGE));
cover_EXCEPT_ITLBMISS: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_ITLBMISS));
cover_EXCEPT_DTLBMISS: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_DTLBMISS));
cover_EXCEPT_INT: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_INT));
cover_EXCEPT_ILLEGAL: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_ILLEGAL));
cover_EXCEPT_ALIGN: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_ALIGN));
cover_EXCEPT_TICK: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_TICK));
cover_EXCEPT_IPF: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_IPF));
cover_EXCEPT_DPF: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_DPF));
cover_EXCEPT_BUSERR: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_BUSERR));
cover_EXCEPT_NONE: cover property(@(posedge clk) (except_type == OR1200_EXCEPT_NONE));
endmodule

module except_assert;

bind or1200_except SVA_except wrp(
	.clk(clk),
	.reset(rst),
	.except_flushpipe(except_flushpipe),
	.pc_we(pc_we),
	.icpu_ack_i(icpu_ack_i),
	.icpu_err_i(icpu_err_i),
	.genpc_freeze(genpc_freeze),
	.if_stall(if_stall),
	.id_freeze(id_freeze),
	.epcr(epcr),
	.wb_pc(wb_pc),
	.ex_pc(ex_pc),
	.ex_dslot(ex_dslot),
	.delayed1_ex_dslot(delayed1_ex_dslot),
	.delayed2_ex_dslot(delayed2_ex_dslot),
        .dl_pc(dl_pc),
	.id_pc(id_pc),
	.except_type(except_type),
	.except_trig(except_trig),
  .state(state)
);
endmodule

