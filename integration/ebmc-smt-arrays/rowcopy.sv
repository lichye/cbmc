module main(input clk);
  logic [3:0] a [0:1][0:1];
  always @(posedge clk) a[0] <= a[1];
  equal_rows: assert property (@(posedge clk) 1 |=> a[0] == a[1]);
  copy: assert property (@(posedge clk) 1 |=> a[0][0] == $past(a[1][0]));
  keep: assert property (@(posedge clk) 1 |=> a[1][1] == $past(a[1][1]));
  free: assert property (@(posedge clk) a[0][0] == a[1][0]);
endmodule
