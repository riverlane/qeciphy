// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: aniketEng, Dogancan Davutoglu

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

endpackage : qeciphy_pkg
`endif
