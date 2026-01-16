// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_crc16_ibm3740_checker (
    input logic        clk_i,
    input logic        rst_n_i,
    input logic [63:0] tdata_i,
    input logic        tvalid_i,
    input logic [15:0] crc_o,
    input logic        crc_valid_o
);

   // Function to compute CRC16-IBM3740 over 64 bits of data
   function automatic [15:0] crc16_ibm3740_step(input [15:0] crc_in, input [63:0] data_in);
      reg [15:0] crc;
      integer k;
      reg fb;
      begin
         crc = crc_in;
         for (k = 63; k >= 0; k = k - 1) begin
            fb  = crc[15] ^ data_in[k];
            crc = {crc[14:0], 1'b0};
            if (fb) crc = crc ^ 16'h1021;
         end
         crc16_ibm3740_step = crc;
      end
   endfunction

   // On reset, crc_valid_o should be low and crc_o should be 0xFFFF.
   property p_correct_crc16_out_of_reset;
      @(posedge clk_i) $rose(
          rst_n_i
      ) |-> !crc_valid_o && (crc_o == 16'hFFFF);
   endproperty

   p_correct_crc16_out_of_reset_A :
   assert property (p_correct_crc16_out_of_reset)
   else $fatal(1, "Wrong CRC16 value out of reset at %m");

   // crc_valid_o should assert exactly 2 cycles after tvalid_i.
   property p_crc16_valid_delay;
      @(posedge clk_i) disable iff (!rst_n_i) tvalid_i |-> ##2 crc_valid_o;
   endproperty

   p_crc16_valid_delay_A :
   assert property (p_crc16_valid_delay)
   else $fatal(1, "CRC16 valid signal timing incorrect at %m");

   // crc_valid_o should never assert spuriously. It must be preceded by tvalid_i 2 cycles earlier.
   property p_crc16_valid_no_spurious;
      @(posedge clk_i) disable iff (!rst_n_i) crc_valid_o |-> $past(
          tvalid_i, 2
      );
   endproperty

   p_crc16_valid_no_spurious_A :
   assert property (p_crc16_valid_no_spurious)
   else $fatal(1, "Spurious CRC16 valid signal at %m");

   // Check step-by-step correctness (only checked in simulation)
   property p_crc16_step_matches_model;
      @(posedge clk_i) disable iff (!rst_n_i) crc_valid_o |-> (crc_o == crc16_ibm3740_step(
          $past(crc_o, 1), $past(tdata_i, 2)
      ));
   endproperty

   p_crc16_step_matches_model_A :
   assert property (p_crc16_step_matches_model)
   else $fatal(1, "CRC16 value incorrect at %m");

endmodule
