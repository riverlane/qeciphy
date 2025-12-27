// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_crc8_smbus_checker (
    input logic       clk_i,
    input logic       rst_n_i,
    input logic [7:0] tdata_i,
    input logic       tvalid_i,
    input logic [7:0] crc_o,
    input logic       crc_valid_o
);

   // Function to compute the next CRC-8/SMBUS value given current CRC and input data byte
   function automatic [7:0] crc8_smbus_step(input [7:0] crc_in, input [7:0] data_in);
      reg [7:0] crc;
      int i;

      begin
         crc = crc_in ^ data_in;

         for (i = 0; i < 8; i++) begin
            if (crc[7]) begin
               crc = (crc << 1) ^ 8'h07;
            end else begin
               crc = crc << 1;
            end
         end

         crc8_smbus_step = crc;
      end
   endfunction

   // On reset, crc_valid_o should be low and crc_o should be zero.
   property p_crc8_correct_crc_out_of_reset;
      @(posedge clk_i) $rose(
          rst_n_i
      ) |-> !crc_valid_o && (crc_o == 8'd0);
   endproperty

   p_crc8_correct_crc_out_of_reset_A :
   assert property (p_crc8_correct_crc_out_of_reset);


   // crc_valid_o should assert exactly one cycle after any asserted tvalid_i.
   property p_crc8_valid_delay;
      @(posedge clk_i) disable iff (!rst_n_i) tvalid_i |-> ##1 crc_valid_o;
   endproperty

   p_crc8_valid_delay_A :
   assert property (p_crc8_valid_delay);

   // crc_valid_o should never assert spuriously. It must be preceded by tvalid_i in the prior cycle.
   property p_crc8_valid_no_spurious;
      @(posedge clk_i) disable iff (!rst_n_i) crc_valid_o |-> $past(
          tvalid_i, 1
      );
   endproperty

   p_crc8_valid_no_spurious_A :
   assert property (p_crc8_valid_no_spurious);

   // Check step-by-step correctness
   property p_crc8_one_step_matches_model;
      @(posedge clk_i) disable iff (!rst_n_i) crc_valid_o |-> (crc_o == crc8_smbus_step(
          $past(crc_o, 1), $past(tdata_i, 1)
      ));
   endproperty

   p_crc8_one_step_matches_model_A :
   assert property (p_crc8_one_step_matches_model);

endmodule
