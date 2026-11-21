module main(input clk, input bit [3:0] x);
  bit [3:0] a[0:1][0:1], b[0:1][0:1];
  always @(posedge clk) begin a[0][0] <= x; b[0][0] <= x; end
  wire same = a[0][0]==b[0][0] && a[0][1]==b[0][1] &&
              a[1][0]==b[1][0] && a[1][1]==b[1][1];
  entire: assert property (@(posedge clk) same |-> a==b);
  row: assert property (@(posedge clk) (a[0][0]==b[0][0] && a[0][1]==b[0][1]) |-> a[0]==b[0]);
  unequal: assert property (@(posedge clk) a==b);
endmodule
