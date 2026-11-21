module main(input clk, input bit [7:0] i, input bit [3:0] x);
  bit [3:0] a[1:3][3:1];
  always @(posedge clk) a[2][i] <= x;
  read_oob: assert property (@(posedge clk) i>3 |-> a[2][i]==0);
  keep: assert property (@(posedge clk) i>3 |=> a[2][1]==$past(a[2][1]));
  no_wrap: assert property (@(posedge clk) i==8'h81 |-> a[2][i]==0);
endmodule
