/*
 * This file holds the assertions for or1200_qmem_top
 * Author: Saqib Khan
 */

`include "../rtl/verilog/or1200_defines.v"
import FSMProperties::*;

module SVA_qmem_top(
  input wire clk,
  input wire reset, qmemdmmu_cycstb_i, daddr_qmem_hit, qmem_ack, qmemdcpu_we_i,
  input wire iaddr_qmem_hit, 
  input [2:0] state
);

import FSMProperties::*;

localparam [2:0] OR1200_QMEMFSM_IDLE = 3'd0,
		 OR1200_QMEMFSM_STORE = 3'd1,
 		 OR1200_QMEMFSM_LOAD = 3'd2,
		 OR1200_QMEMFSM_FETCH = 3'd3;

//reset state 
//assert property (@(posedge clk) reset |=> (state == OR1200_QMEMFSM_IDLE));

//from IDLE state

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_IDLE), (qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && qmemdcpu_we_i), (state == OR1200_QMEMFSM_STORE)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_IDLE), (qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && !qmemdcpu_we_i), (state == OR1200_QMEMFSM_LOAD)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_IDLE), (qmemdmmu_cycstb_i && iaddr_qmem_hit && qmem_ack), (state == OR1200_QMEMFSM_FETCH)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_IDLE), (!(qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && !qmemdcpu_we_i) && !(qmemdmmu_cycstb_i && iaddr_qmem_hit && qmem_ack)), (state == OR1200_QMEMFSM_IDLE)));

//from store state

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_STORE), (qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && qmemdcpu_we_i), (state == OR1200_QMEMFSM_STORE)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_STORE), (qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && !qmemdcpu_we_i), (state == OR1200_QMEMFSM_LOAD)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_STORE), (qmemdmmu_cycstb_i && iaddr_qmem_hit && qmem_ack), (state == OR1200_QMEMFSM_FETCH)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_STORE), (!(qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && !qmemdcpu_we_i) && !(qmemdmmu_cycstb_i && iaddr_qmem_hit && qmem_ack)), (state == OR1200_QMEMFSM_IDLE)));

//from load state

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_LOAD), (qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && qmemdcpu_we_i), (state == OR1200_QMEMFSM_STORE)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_LOAD), (qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && !qmemdcpu_we_i), (state == OR1200_QMEMFSM_LOAD)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_LOAD), (qmemdmmu_cycstb_i && iaddr_qmem_hit && qmem_ack), (state == OR1200_QMEMFSM_FETCH)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_LOAD), (!(qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && !qmemdcpu_we_i) && !(qmemdmmu_cycstb_i && iaddr_qmem_hit && qmem_ack)), (state == OR1200_QMEMFSM_IDLE)));

//from load state

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_FETCH), (qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && qmemdcpu_we_i), (state == OR1200_QMEMFSM_STORE)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_FETCH), (qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && !qmemdcpu_we_i), (state == OR1200_QMEMFSM_LOAD)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_FETCH), (qmemdmmu_cycstb_i && iaddr_qmem_hit && qmem_ack), (state == OR1200_QMEMFSM_FETCH)));

assert property (FSMValidTransition(clk, (state == OR1200_QMEMFSM_FETCH), (!(qmemdmmu_cycstb_i && daddr_qmem_hit && qmem_ack && !qmemdcpu_we_i) && !(qmemdmmu_cycstb_i && iaddr_qmem_hit && qmem_ack)), (state == OR1200_QMEMFSM_IDLE)));

endmodule

module qmem_assert;

bind or1200_qmem_top SVA_qmem_top wrp (
  .clk(clk),
  .reset(rst),
  .qmemdmmu_cycstb_i(qmemdmmu_cycstb_i),
  .daddr_qmem_hit(daddr_qmem_hit),
  .qmem_ack(qmem_ack),
  .qmemdcpu_we_i(qmemdcpu_we_i),
  .iaddr_qmem_hit(iaddr_qmem_hit),
  .state(state)
);

endmodule
