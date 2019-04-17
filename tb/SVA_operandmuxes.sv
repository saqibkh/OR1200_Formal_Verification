/*
 * This file holds the assertions for or1200_dc_fsm
 * Author: Saqib Khan
 */

import FSMProperties::*;
`include "../rtl/verilog/or1200_defines.v"

module SVA_operandmuxes (
  input wire clk,
  input wire reset, id_freeze, ex_freeze, 
  input [31:0] ex_forw, wb_forw, simm, rf_dataa, rf_datab,
  input [31:0] operand_a, operand_b,
  input [1:0] sel_a,
  input [1:0] sel_b
);

// operand_a related assertions
property reset_operand_a;
@(posedge clk) reset |=> (!operand_a);
endproperty
assert property (reset_operand_a);

// no freezing, rising edge or falling edge of the input data

property forward_operand_a1;
@(posedge clk) disable iff(reset)
	$rose(!ex_freeze && !id_freeze)
	##1 (!ex_freeze && !id_freeze && sel_a == 2'd2 && $stable(ex_forw) && $stable(sel_a)) |-> operand_a == ex_forw;
endproperty
assert property (forward_operand_a1);

property forward_operand_a2;
@(posedge clk) disable iff(reset)
	$rose(!ex_freeze && !id_freeze)
	##1 (!ex_freeze && !id_freeze && sel_a == 2'd3 && $stable(wb_forw) && $stable(sel_a)) |-> operand_a == wb_forw;
endproperty
assert property (forward_operand_a2);

property forward_operand_a3;
@(posedge clk) disable iff(reset)
	 $rose(!ex_freeze && !id_freeze) 
	 ##1 ( !ex_freeze && !id_freeze & !(sel_a == 2'd2 || sel_a == 2'd3) && $stable(rf_dataa) && $stable(sel_a) && !$isunknown(operand_a) ) 
	|-> operand_a == rf_dataa;
endproperty
assert property (forward_operand_a3);

  
// operand_b related assertions
property reset_operand_b;
@(posedge clk) reset |=> (!operand_b);
endproperty
assert property (reset_operand_b);

// no freezing, rising edge or falling edge of the input data
property forward_operand_b1;
@(posedge clk) disable iff(reset)
  $rose(!ex_freeze && !id_freeze)
  ##1 (!ex_freeze && !id_freeze && sel_b == 2'd1 && $stable(simm) && $stable(sel_b)) |->  operand_b == simm;
endproperty
assert property (forward_operand_b1);

property forward_operand_b2;
@(posedge clk) disable iff(reset)
	$rose(!ex_freeze && !id_freeze)
	##1 (!ex_freeze && !id_freeze && sel_b == 2'd2 && $stable(ex_forw) && $stable(sel_b)) |-> operand_b == ex_forw;
endproperty
assert property (forward_operand_b2);

property forward_operand_b3;
@(posedge clk) disable iff(reset)
	$rose(!ex_freeze && !id_freeze)
	##1 (!ex_freeze && !id_freeze && sel_b == 2'd3 && $stable(wb_forw) && $stable(sel_b)) |-> operand_b == wb_forw;
endproperty
assert property (forward_operand_b3);

property forward_operand_b4;
@(posedge clk) disable iff(reset)
 	$rose(!ex_freeze && !id_freeze) 
  ##1 (!ex_freeze && !id_freeze && !(sel_b == 2'd1 || sel_b == 2'd2 || sel_b == 2'd3) && $stable(rf_datab) && $stable(sel_b)) 
  |-> operand_b == rf_datab;
endproperty
assert property (forward_operand_b4);

endmodule

module operandmux_assert;

bind or1200_operandmuxes SVA_operandmuxes wrp (
  .clk(clk),
  .reset(rst),
  .id_freeze(id_freeze),
  .ex_freeze(ex_freeze),
  .ex_forw(ex_forw),
  .wb_forw(wb_forw),
  .simm(simm),
  .rf_dataa(rf_dataa),
  .rf_datab(rf_datab),
  .operand_a(operand_a),
  .operand_b(operand_b),
  .sel_a(sel_a),
  .sel_b(sel_b)
);

endmodule
