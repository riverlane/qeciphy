// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Alex Crownshaw

module riv_counter_checker #(
    parameter WIDTH = 16
) (
    input  logic             clk,     // Clock
    input  logic             rst_n,   // Active-low reset  
    input  logic [WIDTH-1:0] value,   // Initial value to load
    input  logic             load,    // Load new value
    input  logic             enable,  // Enable counting
    input  logic             done     // Asserted when counter reaches zero
);

    /* ------------ Counter Model ------------ */

    logic [WIDTH-1:0] count_t;

    always @ (posedge clk) begin
        if (!rst_n) begin
            count_t <= '0;
        end else if (load) begin
            count_t <= value;
        end else if (enable) begin
            count_t <= count_t - 1;
        end
    end

    /* ------------ Internal Count signal ------------ */

    logic [riv_counter.PADDED_WIDTH-1:0] internal_count;

    genvar i;
    generate
        for (i = 0; i < riv_counter.N_PRIM; i++) begin : gen_internal_count
            assign internal_count[i*4 +: 4] = riv_counter.gen_counter_prim[i].i_riv_counter_prim.count;
        end
    endgenerate

    /* ------------ Assertions ------------ */

    // Property: done is only asserted when count_t is zero
    property p_done_asserted_when_count_t_is_zero;
        @(posedge clk) (count_t == '0) |-> done;
    endproperty
    done_asserted_when_count_t_is_zero_A: assert property (p_done_asserted_when_count_t_is_zero)
    else $fatal("done de-asserted while count_t is zero");

    // property: done is de-asserted when count_t is non-zero
    property p_done_deasserted_when_count_t_nonzero;
        @(posedge clk) (count_t != '0) |-> !done;
    endproperty
    done_deasserted_when_count_t_nonzero_A: assert property (p_done_deasserted_when_count_t_nonzero)
    else $fatal("done asserted while count_t is non-zero");

    // Property: internal_count matches count_t in lower WIDTH bits
    property p_internal_count_matches_count_t;
        @(posedge clk) internal_count[WIDTH-1:0] == count_t;
    endproperty
    internal_count_matches_count_t_A: assert property (p_internal_count_matches_count_t)
    else $fatal("internal_count does not match count_t");
    
endmodule
