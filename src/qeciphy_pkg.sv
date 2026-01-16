// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta, Dogancan Davutoglu

`ifndef QECIPHY_PKG
`define QECIPHY_PKG

package qeciphy_pkg;

   localparam BYTE_ALIGNMENT_COMMA = 8'hBC;
   localparam WORD_ALIGNMENT_COMMA = 8'hCB;
   localparam IDLE_WORD = 64'h0;

   // QECIPHY Validation Packet Structure
   typedef struct packed {
      logic [15:0] crc45;
      logic [15:0] crc23;
      logic [15:0] crc01;
      logic [1:0]  reserved_15_14;
      logic [5:0]  valids;
      logic [7:0]  crcvw;
   } qeciphy_vd_pkt_t;

   // QECIPHY Frame Alignment Packet Structure
   typedef struct packed {
      logic        rx_rdy;
      logic [22:0] reserved_62_40;
      logic [7:0]  word_comma;
      logic [23:0] reserved_31_8;
      logic [7:0]  byte_comma;
   } qeciphy_faw_t;

   // QECIPHY error codes
   typedef enum logic [3:0] {
      NO_ERROR = 4'h0,
      FAW_ERROR = 4'h1,
      CRC_ERROR = 4'h2,
      TX_FIFO_OVERFLOW = 4'h3,
      RX_FIFO_OVERFLOW = 4'h4
   } qeciphy_error_t;

   // QECIPHY status codes
   typedef enum logic [3:0] {
      RESET = 4'h0,
      WAIT_FOR_RESET = 4'h1,
      LINK_TRAINING = 4'h2,
      RX_LOCKED = 4'h3,
      LINK_READY = 4'h4,
      FAULT_FATAL = 4'h5
   } qeciphy_status_t;

   // To check if the data is a Frame Alignment Word
   function bit is_faw(input logic [63:0] data);
      begin
         bit faw_detected;
         qeciphy_faw_t faw;
         faw = qeciphy_faw_t'(data);
         faw_detected = (faw.word_comma == WORD_ALIGNMENT_COMMA) && (faw.byte_comma == BYTE_ALIGNMENT_COMMA);
         return faw_detected;
      end
   endfunction

endpackage : qeciphy_pkg
`endif
