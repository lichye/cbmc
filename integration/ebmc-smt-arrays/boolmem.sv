module main(input clk, input bit select, data);
  bit a[0:1][0:1];
  always @(posedge clk) a[select][0] <= data;
  written: assert property (@(posedge clk) 1 |=> a[$past(select)][0]==$past(data));
  free: assert property (@(posedge clk) a[0][0]==a[1][0]);
endmodule
