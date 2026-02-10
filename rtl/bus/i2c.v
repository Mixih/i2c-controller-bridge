module i2c #(
    parameter SYSTEM_CLK_HZ = 100_000_000,
    parameter MODE = "fast",
    localparam WIDTH = 8
) (
    input wire clk,
    input wire rst,

    // i2c txfifo intf
    input wire wr_stb;
    // i2c txfifo packet
    input wire restart;
    input wire stop;
    input wire cdm;
    input wire [WIDTH - 1:0] din;
    // i2c rxfifo intf
    input wire rd_stb;
    output wire dout[WIDTH - 1:0];
);

endmodule
