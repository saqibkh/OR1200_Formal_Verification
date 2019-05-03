/*
 * This file holds the assertions for or1200_if
 * Author: Saqib Khan
 */

`include "../rtl/verilog/or1200_defines.v"
import FSMProperties::*;

module SVA_if (
  input clk,
  input rst,
  input no_more_dslot,
  input except_itlbmiss,
  input except_immufault,
  input except_ibuserr,
  input if_flushpipe,
  input save_insn,
  input [31:0] insn_saved,
  input saved,
  input [31:0] icpu_dat_i,
  input icpu_err_i,
  input [31:0] icpu_adr_i,
  input [3:0] icpu_tag_i,
  input [31:0] addr_saved,
  input [2:0] err_saved,
  input if_freeze
);

//Exceptions under no_more_dslot
assert_property_no_more_dslot: assert property ( @(posedge clk) no_more_dslot |-> (except_itlbmiss == 0 && except_immufault == 0 && except_ibuserr == 0) );

//saved flag 
property valid_saved_tflag;
@(posedge clk) disable iff (rst) (!if_flushpipe && save_insn) |-> ##1 saved == 1;
endproperty
assert_property_valid_saved_tflag: assert property (valid_saved_tflag);

property valid_saved_fflag;
@(posedge clk) disable iff (rst) (if_flushpipe | (!save_insn && !if_freeze)) |-> ##1 saved == 0;
endproperty
assert_property_valid_saved_fflag: assert property (valid_saved_fflag);

//valid storage of fetch instruction
property valid_store_insfetch1;
@(posedge clk) disable iff (rst) (!if_flushpipe && save_insn && !icpu_err_i) |-> ##1 (insn_saved == $past(icpu_dat_i));
endproperty
assert_property_valid_store_insfetch1: assert property (valid_store_insfetch1);

property valid_store_insfetch2;
@(posedge clk) disable iff (rst) (if_flushpipe | (!save_insn && !if_freeze) && !icpu_err_i) |-> ##1 (insn_saved == {6'b000101, 26'h041_0000});
endproperty
assert_property_valid_store_insfetch2: assert property (valid_store_insfetch2);

property valid_fetched_addr1;
@(posedge clk) disable iff (rst) (!if_flushpipe && (save_insn | !if_freeze)) |-> ##1 (addr_saved == {$past(icpu_adr_i[31:2]), 2'b00});
endproperty
assert_property_valid_fetched_addr1: assert property (valid_fetched_addr1);

//valid storage of fetched instruction address
property valid_fetched_addr2;
@(posedge clk) disable iff (rst) (if_flushpipe) |-> ##1 (addr_saved == 32'h00000000);
endproperty
assert_property_valid_fetched_addr2: assert property (valid_fetched_addr2);

//valid error tags
property valid_error_tag0;
@(posedge clk) disable iff (rst) (!if_flushpipe && save_insn) |-> ##1 (err_saved[0] == ($past(icpu_err_i) & ($past(icpu_tag_i) == 4'hd)) );
endproperty
assert_property_valid_error_tag0: assert property (valid_error_tag0);

property valid_error_tag1;
@(posedge clk) disable iff (rst) (!if_flushpipe && save_insn) |-> ##1 (err_saved[1] == ($past(icpu_err_i) & ($past(icpu_tag_i) == 4'hc)));
endproperty
assert_property_valid_error_tag1: assert property (valid_error_tag1);

property valid_error_tag2;
@(posedge clk) disable iff (rst) (!if_flushpipe && save_insn) |-> ##1 (err_saved[2] == ($past(icpu_err_i) & ($past(icpu_tag_i) == 4'hb)) );
endproperty
assert_property_valid_error_tag2: assert property (valid_error_tag2);

property valid_error_tag_default;
@(posedge clk) disable iff (rst) (if_flushpipe | (!save_insn && !if_freeze)) |-> ##1 (err_saved == 3'b000);
endproperty
assert_property_valid_error_tag_default: assert property (valid_error_tag_default);

endmodule

module if_assert;

bind or1200_if SVA_if wrp (
  .clk(clk),
  .rst(rst),
  .no_more_dslot(no_more_dslot),
  .except_itlbmiss(except_itlbmiss),
  .except_immufault(except_immufault),
  .except_ibuserr(except_ibuserr),
  .if_flushpipe(if_flushpipe),
  .save_insn(save_insn),
  .insn_saved(insn_saved),
  .saved(saved),
  .icpu_dat_i(icpu_dat_i),
  .icpu_err_i(icpu_err_i),
  .icpu_adr_i(icpu_adr_i),
  .icpu_tag_i(icpu_tag_i),
  .addr_saved(addr_saved),
  .err_saved(err_saved),
  .if_freeze(if_freeze)
);

endmodule
