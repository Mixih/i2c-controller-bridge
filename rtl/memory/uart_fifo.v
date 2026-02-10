/*
 * SPDX-FileCopyrightText:  Copyright (C) 2026, Max Hahn
 * SPDX-License-Identifier: CERN-OHL-S-2.0
 *
 * This source describes Open Hardware and is licensed under the CERN-OHL-S v2.
 * You may redistribute and modify this source and make products using it under
 * the terms of the CERN-OHL-S v2 (https://ohwr.org/cern_ohl_s_v2.txt).
 *
 * This source is distributed WITHOUT ANY EXPRESS OR IMPLIED WARRANTY, INCLUDING
 * OF MERCHANTABILITY, SATISFACTORY QUALITY AND FITNESS FOR A PARTICULAR PURPOSE.
 * Please see the CERN-OHL-S v2 for applicable conditions.
 *
 * Source location: https://github.com/Mixih/NAIL
 *
 * As per CERN-OHL-S v2 section 4, should you produce hardware based on this
 * source, you must where practicable maintain the Source Location visible in
 * the documentation for the Product or other products you make using this
 * source.
 *
 * You should have recieved a copy of the CERN-OHL-S v2.0 license along with
 * this file. If you did not recieve a copy of the aforementioned license, you
 * may obtain a copy at https://ohwr.org/cern_ohl_s_v2.txt.
 */
 module uart_fifo
#(
    parameter DATA_WIDTH = 8,
    parameter FIFO_SIZE = 16,
    parameter XRUN_MODE = "KEEP",
    localparam FIFO_IDX_W = $clog2(FIFO_SIZE)
) (
    input wire clk,
    input wire rst,

    input wire wr,
    input wire [DATA_WIDTH - 1:0] din,
    input wire rd,
    output wire [DATA_WIDTH - 1:0] dout,
    output wire [FIFO_IDX_W - 1:0] dcount,
);
    `include "util.vh"

    reg [DATA_WIDTH - 1:0] buf [FIFO_SIZE - 1:0];
    reg [FIFO_IDX_W:0] rd_i;
    reg FIFO_IDX_W:0] wr_i;

    always @(posedge clk) begin
        if (rst) begin
            rd_i <= 'b0;
            wr_i <= 'b0;
        end
    end
    //////////////////////////////////////
    // Formal Properties
    //////////////////////////////////////
    `ifdef FORMAL
        `ifdef UART_FIFO
            `define ASSUME assume
            `define MODULE_IS_FORMAL_TOP 1
        `else
            `define ASSUME assert
            `define MODULE_IS_FORMAL_TOP 0
        `endif
    `endif
endmodule
