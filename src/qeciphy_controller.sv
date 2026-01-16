// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Aniket Datta, Gargi Sunil

//------------------------------------------------------------------------------
// QECIPHY Controller
//------------------------------------------------------------------------------
// This module implements the main link establishment and control state machine
// for the QECIPHY. It orchestrates the complete link initialization
// sequence from reset to operational data transfer.
//
// Link Establishment Sequence:
// 1. RESET -> Wait for system reset completion
// 2. Enable TX link training -> Start transmitting alignment patterns
// 3. Wait for RX datapath alignment -> SERDES byte/word alignment complete
// 4. Enable RX processing -> Start receiving and processing data
// 5. Wait for local RX lock -> Local receiver achieves frame synchronization
// 6. Wait for remote RX lock -> Remote side confirms its receiver is ready
// 7. Enable TX data -> Start transmitting actual user data
// 8. READY -> Link is fully operational for bidirectional data transfer
//
// Error Handling:
// - Fatal faults transition directly to FAULT_FATAL state from any state
// - Fault state is persistent until system reset
//------------------------------------------------------------------------------

`include "qeciphy_pkg.sv"

module qeciphy_controller (
    // System Interface
    input logic clk_i,   // Clock input
    input logic rst_n_i, // Active-low reset

    // Status Inputs
    input logic reset_done_i,           // System reset sequence completed
    input logic rx_datapath_aligned_i,  // SERDES alignment completed
    input logic rx_ready_i,             // Local RX frame lock achieved
    input logic remote_rx_ready_i,      // Remote RX ready status received
    input logic fault_fatal_i,          // Fatal error detected

    // Control Outputs
    output logic       link_ready_o,      // Link ready for user data transfer
    output logic       fault_fatal_o,     // Fatal error state indicator
    output logic [3:0] status_o,          // Link status code
    output logic       tx_link_enable_o,  // Enable TX training pattern
    output logic       tx_data_enable_o,  // Enable TX user data transmission
    output logic       rx_enable_o        // Enable RX data processing
);

   import qeciphy_pkg::*;

   // =========================================================================
   // State Machine Definition
   // =========================================================================

   typedef enum logic [13:0] {
      RESET                  = 14'b00000000000001,  // Initial reset state
      WAIT_RESET_DONE        = 14'b00000000000010,  // Waiting for reset completion
      TX_LINK_ENABLE         = 14'b00100000000100,  // Enable TX training pattern
      WAIT_RX_DATAPATH_ALIGN = 14'b00100000001000,  // Wait for SERDES alignment  
      RX_ENABLE              = 14'b01100000010000,  // Enable RX processing
      WAIT_RX_LOCKED         = 14'b01100000100000,  // Wait for local RX lock
      LOCAL_RX_LOCKED        = 14'b01100001000000,  // Local RX locked
      BOTH_RX_LOCKED         = 14'b01100010000000,  // Both RX sides locked
      TX_DATA_ENABLE         = 14'b11100100000000,  // Enable TX data
      READY                  = 14'b11101000000000,  // Link fully ready
      FAULT_FATAL            = 14'b00010000000000   // Fatal error state
   } fsm_t;

   fsm_t state, state_nxt;  // Current and next state registers
   qeciphy_status_t status;  // Mapped status output
   logic            in_ready_state;  // Link ready flag
   logic            in_fault_state;  // Fault state flag

   // =========================================================================
   // Control Signal Generation
   // =========================================================================

   assign in_ready_state   = state[9];
   assign in_fault_state   = state[10];

   assign link_ready_o     = in_ready_state;
   assign fault_fatal_o    = in_fault_state;
   assign tx_link_enable_o = state[11];
   assign tx_data_enable_o = state[13];
   assign rx_enable_o      = state[12];

   // =========================================================================
   // Status Code Mapping
   // =========================================================================
   // Maps internal detailed states to external simplified status codes

   assign status_o         = status;

   always_comb begin
      case (state)
         RESET:                  status = qeciphy_pkg::RESET;
         WAIT_RESET_DONE:        status = qeciphy_pkg::WAIT_FOR_RESET;
         TX_LINK_ENABLE:         status = qeciphy_pkg::LINK_TRAINING;
         WAIT_RX_DATAPATH_ALIGN: status = qeciphy_pkg::LINK_TRAINING;
         RX_ENABLE:              status = qeciphy_pkg::LINK_TRAINING;
         WAIT_RX_LOCKED:         status = qeciphy_pkg::LINK_TRAINING;
         LOCAL_RX_LOCKED:        status = qeciphy_pkg::RX_LOCKED;
         BOTH_RX_LOCKED:         status = qeciphy_pkg::RX_LOCKED;
         TX_DATA_ENABLE:         status = qeciphy_pkg::RX_LOCKED;
         READY:                  status = qeciphy_pkg::LINK_READY;
         FAULT_FATAL:            status = qeciphy_pkg::FAULT_FATAL;
         default:                status = qeciphy_pkg::RESET;
      endcase
   end

   // =========================================================================
   // State Machine
   // =========================================================================

   always_ff @(posedge clk_i) begin
      if (!rst_n_i) begin
         state <= RESET;
      end else if (fault_fatal_i) begin
         state <= FAULT_FATAL;  // Immediate transition on fatal fault
      end else begin
         state <= state_nxt;
      end
   end

   // Next State Logic
   always_comb begin
      unique case (state)
         RESET: state_nxt = WAIT_RESET_DONE;
         WAIT_RESET_DONE: state_nxt = reset_done_i ? TX_LINK_ENABLE : WAIT_RESET_DONE;  // Wait for reset completion
         TX_LINK_ENABLE: state_nxt = WAIT_RX_DATAPATH_ALIGN;  // Assert TX link enable
         WAIT_RX_DATAPATH_ALIGN: state_nxt = rx_datapath_aligned_i ? RX_ENABLE : WAIT_RX_DATAPATH_ALIGN;  // Wait for SERDES byte and word alignment
         RX_ENABLE: state_nxt = WAIT_RX_LOCKED;  // Enable RX processing
         WAIT_RX_LOCKED: state_nxt = rx_ready_i ? LOCAL_RX_LOCKED : WAIT_RX_LOCKED;  // Wait for local RX lock
         LOCAL_RX_LOCKED: state_nxt = remote_rx_ready_i ? BOTH_RX_LOCKED : LOCAL_RX_LOCKED;  // Wait for remote RX lock
         BOTH_RX_LOCKED: state_nxt = TX_DATA_ENABLE;  // Both RX locked
         TX_DATA_ENABLE: state_nxt = READY;  // Enable TX data
         READY: state_nxt = READY;  // Link fully operational - sticky until fault
         FAULT_FATAL: state_nxt = FAULT_FATAL;  // Sticky until reset
         default: state_nxt = RESET;  // Safety fallback
      endcase
   end

endmodule
