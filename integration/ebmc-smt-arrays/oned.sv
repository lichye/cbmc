module main(input clk, input [1:0] r, input [3:0] x);
  reg [3:0] a [0:3];
  always @(posedge clk) a[1] <= x;
  good: assert property (@(posedge clk) 1 |=> a[1] == $past(x));
  bad: assert property (@(posedge clk) a[r] == 0);
endmodule
