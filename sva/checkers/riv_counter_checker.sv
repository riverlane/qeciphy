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

    logic [WIDTH-1:0] model_count;

    always @ (posedge clk) begin
        if (!rst_n) begin
            model_count <= '0;
        end else if (load) begin
            model_count <= value;
        end else if (enable) begin
            model_count <= model_count - 1;
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

    // Property: done is only asserted when model_count is zero
    property done_asserted_when_model_count_is_zero;
        @(posedge clk) (model_count == '0) |-> done;
    endproperty
    assert_done_asserted_when_model_count_is_zero: assert property (done_asserted_when_model_count_is_zero)
    else $fatal("done de-asserted while model_count is zero");

    // property: done is de-asserted when model_count is non-zero
    property done_deasserted_when_model_count_nonzero;
        @(posedge clk) (model_count != '0) |-> !done;
    endproperty
    assert_done_deasserted_when_model_count_nonzero: assert property (done_deasserted_when_model_count_nonzero)
    else $fatal("done asserted while model_count is non-zero");

    // Property: internal_count matches model_count in lower WIDTH bits
    property internal_count_matches_model_count;
        @(posedge clk) internal_count[WIDTH-1:0] == model_count;
    endproperty
    assert_internal_count_matches_model_count: assert property (internal_count_matches_model_count)
    else $fatal("internal_count does not match model_count");
    
endmodule
