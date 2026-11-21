module main(input clk, input bit i,j,k, input bit [3:0] x);
  bit [3:0] a[0:1][0:1][0:1];
  always @(posedge clk) a[i][j][k] <= x;
  write_word: assert property (@(posedge clk) 1 |=> a[$past(i)][$past(j)][$past(k)]==$past(x));
  untouched: assert property (@(posedge clk) 1 |=> a[!$past(i)][$past(j)][$past(k)]==$past(a[!i][j][k]));
  arbitrary: assert property (@(posedge clk) a[0][0][0]==a[1][0][0]);
endmodule
