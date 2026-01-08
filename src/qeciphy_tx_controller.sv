// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

//------------------------------------------------------------------------------
// TX Controller
//------------------------------------------------------------------------------
// This module controls the transmission state machine for the QECIPHY TX subsystem.
// It manages three transmission states based on link and data enable signals.
//
// - TX_OFF: Link disabled - transmits idle words only, no boundary characters
// - TX_IDLE: Link enabled but no data - transmits idle words with boundary chars
// - TX_ACTIVE: Link and data enabled - transmits user data with boundary chars
//
// State Transitions:
// - States are updated on FAW boundary alignments (almost_faw_boundary_i)
// - Priority: !link_enable -> TX_OFF, !data_enable -> TX_IDLE, else TX_ACTIVE
// - Changes only occur at frame boundaries to satisfy qeciphy_tx_packet_gen timing requirements
//------------------------------------------------------------------------------

module qeciphy_tx_controller (
    input  logic clk_i,                  // Clock input
    input  logic rst_n_i,                // Active-low reset
    input  logic almost_faw_boundary_i,  // One cycle ahead of FAW boundary
    input  logic link_enable_i,          // Link enable
    input  logic data_enable_i,          // Data transmission enable
    output logic tx_off_o,               // TX off state (idle words only, no boundaries)
    output logic tx_idle_o,              // TX idle state (idle words + boundaries)  
    output logic tx_active_o             // TX active state (user data + boundaries)
);

   // Update transmission state on frame alignment boundaries
   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         // Default to off state on reset
         tx_off_o    <= 1'b1;
         tx_idle_o   <= 1'b0;
         tx_active_o <= 1'b0;
      end else if (almost_faw_boundary_i && !link_enable_i) begin
         // Link disabled: TX off (idle only, no boundaries)
         tx_off_o    <= 1'b1;
         tx_idle_o   <= 1'b0;
         tx_active_o <= 1'b0;
      end else if (almost_faw_boundary_i && !data_enable_i) begin
         // Link enabled, data disabled: TX idle (idle words + boundaries)
         tx_off_o    <= 1'b0;
         tx_idle_o   <= 1'b1;
         tx_active_o <= 1'b0;
      end else if (almost_faw_boundary_i) begin
         // Link and data enabled: TX active (user data + boundaries)
         tx_off_o    <= 1'b0;
         tx_idle_o   <= 1'b0;
         tx_active_o <= 1'b1;
      end
   end

endmodule  // qeciphy_tx_controller
