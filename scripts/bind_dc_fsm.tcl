#Tcl script which can be used with JasperGold

clear -all

#Reading the files 
analyze -v2k ../rtl/verilog/or1200_defines.v
analyze -v2k ../rtl/verilog/or1200_dc_fsm.v

analyze -sv ../tb/FSMProperties.sv
analyze -sv ../tb/SVA_dc_fsm.sv

#Elaborating the design
elaborate -top or1200_dc_fsm

#Set the clock
clock clk
#Set Reset
reset (rst)
#Prove all
prove -bg -all
