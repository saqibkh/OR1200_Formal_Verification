/*
 * This file holds the assertions for or1200_dc_fsm
 * Author: Saqib Khan
 */

`include "../rtl/verilog/or1200_defines.v"

//`include "FSMProperties.sv"
import FSMProperties::*;

module SVA_dc_fsm (
   // I/O
  input					clk,
  input					rst,
  input					dc_en,
  input					dcqmem_cycstb_i,
  input					dcqmem_ci_i,
  input					dcqmem_we_i,
  input [3:0] 				dcqmem_sel_i,
  input					tagcomp_miss,
  input					biudata_valid,
  input					biudata_error,
  input [31:0]	 			lsu_addr,
  input [3:0] 				dcram_we,
  input					biu_read,
  input					biu_write,
  input 				dcram_di_sel,
  input 				biu_do_sel,
  input					first_hit_ack,
  input					first_miss_ack,
  input					first_miss_err,
  input					burst,
  input					tag_we,
  input 				tag_valid,
  input [31:0] 				dc_addr,
  input 				dc_no_writethrough,
  input 				tag_dirty,
  input 				dirty,
  input [`OR1200_DCTAG_W-2:0] 		tag,
  input 				tag_v,   
  input 				dc_block_flush,
  input 				dc_block_writeback,
  input [31:0] 				spr_dat_i,
  input 				mtspr_dc_done,
  input 				spr_cswe, 

  input [2:0] 				state,
  input					hitmiss_eval,
  input [3:0]				cnt,
  input					writethrough,
  input                                 cache_spr_block_flush,
  input					cache_spr_block_writeback,
  input					store,
  input					cache_dirty_needs_writeback
);

localparam [2:0] OR1200_DC_FSM_IDLE	=	3'd0,
		 OR1200_DC_FSM_CLOADSTORE=	3'd1,
		 OR1200_DC_FSM_LOOP2	=	3'd2,
		 OR1200_DC_FSM_LOOP3	= 	3'd3,
		 OR1200_DC_FSM_LOOP4	= 	3'd4,
		 OR1200_DC_FSM_FLUSH5	=	3'd5,
		 OR1200_DC_FSM_INV6	= 	3'd6,
		 OR1200_DC_FSM_WAITSPRCS7=	3'd7;


//assert property (@(posedge clk or rst) rst |=> (state == OR1200_DCFSM_IDLE));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_IDLE), (dc_en && dcqmem_cycstb_i), (state == OR1200_DC_FSM_CLOADSTORE)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_IDLE), (dc_en && (dc_block_flush || dc_block_writeback)), (state == OR1200_DC_FSM_FLUSH5)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_CLOADSTORE), (hitmiss_eval && tagcomp_miss && !(store && writethrough) && !dcqmem_ci_i), (state == OR1200_DC_FSM_LOOP2)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_IDLE), (!dcqmem_cycstb_i || (!hitmiss_eval && (biudata_valid || biudata_error)) || (hitmiss_eval && !tagcomp_miss && !dcqmem_ci_i && !(store && writethrough))), (state == OR1200_DC_FSM_IDLE)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_FLUSH5), (hitmiss_eval && !tag_v && cache_spr_block_flush && !dirty), (state == OR1200_DC_FSM_INV6)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_FLUSH5), (hitmiss_eval && !tag_v && (cache_spr_block_flush || cache_spr_block_writeback) && dirty), (state == OR1200_DC_FSM_LOOP2)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_FLUSH5), (hitmiss_eval && !tag_v && cache_spr_block_writeback && !dirty), (state == OR1200_DC_FSM_WAITSPRCS7)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_LOOP2), (biudata_valid && !(cnt)), (state == OR1200_DC_FSM_LOOP3)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_LOOP2), (!dc_en | biudata_error), (state == OR1200_DC_FSM_IDLE)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_INV6), (!spr_cswe), (state == OR1200_DC_FSM_IDLE)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_WAITSPRCS7), (!spr_cswe), (state == OR1200_DC_FSM_IDLE)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_LOOP3), (cache_dirty_needs_writeback), (state == OR1200_DC_FSM_LOOP2)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_LOOP3), (!cache_dirty_needs_writeback), (state == OR1200_DC_FSM_LOOP4)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_LOOP3), (cache_spr_block_flush || cache_spr_block_writeback), (state == OR1200_DC_FSM_WAITSPRCS7)));

assert property (FSMValidTransition(clk, (state == OR1200_DC_FSM_LOOP4), (!spr_cswe), (state == OR1200_DC_FSM_IDLE)));

endmodule

module Wrapper;
bind or1200_dc_fsm SVA_dc_fsm wrp(
  .clk(clk),
  .rst(rst),
  .dc_en(dc_en),
  .dcqmem_cycstb_i(dcqmem_cycstb_i),
  .dcqmem_ci_i(dcqmem_ci_i),
  .dcqmem_we_i(dcqmem_we_i),
  .dcqmem_sel_i(dcqmem_sel_i),
  .tagcomp_miss(tagcomp_miss),
  .biudata_valid(biudata_valid),
  .biudata_error(biudata_error),
  .lsu_addr(lsu_addr),
  .dcram_we(dcram_we),
  .biu_read(biu_read),
  .biu_write(biu_write),
  .dcram_di_sel(dcram_di_sel),
  .biu_do_sel(biu_do_sel),
  .first_hit_ack(first_hit_ack),
  .first_miss_ack(first_miss_ack),
  .first_miss_err(first_miss_err),
  .burst(burst),
  .tag_we(tag_we),
  .tag_valid(tag_valid),
  .dc_addr(dc_addr),
  .dc_no_writethrough(dc_no_writethrough),
  .tag_dirty(tag_dirty),
  .dirty(dirty),
  .tag(tag),
  .tag_v(tag_v),
  .dc_block_flush(dc_block_flush),
  .dc_block_writeback(dc_block_writeback),
  .spr_dat_i(spr_dat_i),
  .mtspr_dc_done(mtspr_dc_done),
  .spr_cswe(spr_cswe),

  .state(state),
  .hitmiss_eval(hitmiss_eval),
  .cnt(cnt),
  .writethrough(writethrough),
  .cache_spr_block_flush(cache_spr_block_flush),
  .cache_spr_block_writeback(cache_spr_block_writeback),
  .store(store),
  .cache_dirty_needs_writeback(cache_dirty_needs_writeback)
);
endmodule
