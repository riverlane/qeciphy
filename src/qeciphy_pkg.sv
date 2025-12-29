// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta, Dogancan Davutoglu

`ifndef QECIPHY_PKG
`define QECIPHY_PKG

package qeciphy_pkg;

   localparam BYTE_ALIGNMENT_COMMA = 8'hBC;
   localparam WORD_ALIGNMENT_COMMA = 8'hCB;

   // To check if the data is a Frame Alignment Word
   function bit is_faw(input logic [63:0] data);
      begin
         is_faw = (data[39:32] == WORD_ALIGNMENT_COMMA) && (data[7:0] == BYTE_ALIGNMENT_COMMA);
         return is_faw;
      end
   endfunction

   // QECIPHY Validation Packet Structure
   typedef struct packed {
      logic [15:0] crc45;
      logic [15:0] crc23;
      logic [15:0] crc01;
      logic [1:0]  reserved_15_14;
      logic [5:0]  valids;
      logic [7:0]  crcvw;
   } qeciphy_vd_pkt_t;

endpackage : qeciphy_pkg
`endif
