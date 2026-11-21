module main(input clk, input [0:0] r, c, input [3:0] x);
  reg [3:0] a [0:1][0:1];
  always @(posedge clk) a[0][1] <= x;
  good: assert property (@(posedge clk) 1 |=> a[0][1] == $past(x));
  bad: assert property (@(posedge clk) a[r][c] == 0);
endmodule
