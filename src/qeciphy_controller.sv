// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta, Gargi Sunil

module qeciphy_controller (
    input  logic       axis_clk,
    input  logic       axis_rst_n,
    input  logic       i_reset_done,
    input  logic       i_rx_rdy,
    input  logic       i_remote_rx_rdy,
    input  logic       i_fap_missing,
    input  logic       i_crc_error,
    output logic [3:0] o_state,
    output logic [3:0] o_ecode,
    input  logic       i_pstate,
    input  logic       i_preq,
    output logic       o_paccept,
    output logic       o_pactive,
    input  logic       i_tx_tvalid,
    input  logic       i_remote_pd_ack,
    input  logic       i_remote_pd_req,
    output logic       o_pd_req,
    output logic       o_pd_ack,
    output logic       o_allow_user_tx,
    output logic       o_rst_n
);


   // -------------------------------------------------------------
   // Local declaration
   // -------------------------------------------------------------

   logic any_error;
   logic state_ready;
   logic state_sleep;
   logic state_link_training;
   logic error_check_enable;
   logic pd_req_nxt;
   logic pu_req;
   logic pu_req_nxt;
   logic paccept_nxt;
   logic pactive_nxt;
   logic usr_pd_req_latched;
   logic remote_pd_req_latched;

   // -------------------------------------------------------------
   // Type definition
   // -------------------------------------------------------------
   typedef enum bit [3:0] {
      RESET = 0,
      WAIT_FOR_RESET = 1,
      LINK_TRAINING = 2,
      RX_LOCKED = 3,
      LINK_READY = 4,
      FAULT_FATAL = 5,
      SLEEP = 6,
      WAIT_FOR_POWERDOWN = 7
   } fsm_t;

   typedef enum bit [3:0] {
      OK,
      FAP_MISSING,
      CRC_ERROR
   } error_t;

   fsm_t state, state_nxt;
   error_t err, error_nxt;

   // -------------------------------------------------------------
   // General
   // -------------------------------------------------------------

   assign any_error  = i_fap_missing || i_crc_error;

   // -------------------------------------------------------------
   // Power up and power down requests
   // -------------------------------------------------------------

   assign pd_req_nxt = (~i_pstate && i_preq && state_ready) ? 1'b1 : state_sleep ? 1'b0 : o_pd_req;

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) o_pd_req <= 1'b0;
      else o_pd_req <= pd_req_nxt;
   end

   assign pu_req_nxt = (i_pstate && i_preq && state_sleep) ? 1'b1 : 1'b0;

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) pu_req <= 1'b0;
      else pu_req <= pu_req_nxt;
   end

   assign paccept_nxt = (~i_preq && o_paccept) ? 1'b0 : (state_sleep && i_preq && ~i_pstate) ? 1'b1 : (state_ready && i_preq && i_pstate) ? 1'b1 : o_paccept;

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) o_paccept <= 1'b0;
      else o_paccept <= paccept_nxt;
   end

   assign pactive_nxt = (state_link_training) ? 1'b0 : (state_sleep && i_tx_tvalid) ? 1'b1 : o_pactive;

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) o_pactive <= 1'b0;
      else o_pactive <= pactive_nxt;
   end

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) begin
         usr_pd_req_latched <= 1'b0;
      end else if (state_link_training) begin
         usr_pd_req_latched <= 1'b0;
      end else if (~i_pstate && i_preq && state_ready) begin
         usr_pd_req_latched <= 1'b1;
      end
   end

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) begin
         remote_pd_req_latched <= 1'b0;
      end else if (state_link_training) begin
         remote_pd_req_latched <= 1'b0;
      end else if (i_remote_pd_req && state_ready) begin
         remote_pd_req_latched <= 1'b1;
      end
   end

   // -------------------------------------------------------------
   // FSM
   // -------------------------------------------------------------

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) state <= RESET;
      else state <= state_nxt;
   end

   always_comb begin
      case (state)
         // Keep the FSM in reset state till both the TX and RX reset
         // is complete
         RESET: state_nxt = WAIT_FOR_RESET;
         WAIT_FOR_RESET: state_nxt = i_reset_done ? LINK_TRAINING : WAIT_FOR_RESET;
         LINK_TRAINING: state_nxt = i_rx_rdy ? RX_LOCKED : LINK_TRAINING;
         RX_LOCKED: state_nxt = any_error ? FAULT_FATAL : (i_remote_rx_rdy ? LINK_READY : RX_LOCKED);
         LINK_READY: state_nxt = any_error ? FAULT_FATAL : i_remote_pd_ack ? SLEEP : o_pd_ack ? WAIT_FOR_POWERDOWN : LINK_READY;
         SLEEP: state_nxt = pu_req ? WAIT_FOR_RESET : SLEEP;
         WAIT_FOR_POWERDOWN: state_nxt = any_error ? RESET : WAIT_FOR_POWERDOWN;
         FAULT_FATAL: state_nxt = FAULT_FATAL;
         default: state_nxt = fsm_t'(1'bx);
      endcase
   end

   assign state_ready = (state == LINK_READY);
   assign state_sleep = (state == SLEEP);
   assign state_link_training = (state == LINK_TRAINING);

   // -------------------------------------------------------------
   // Error
   // -------------------------------------------------------------

   assign error_check_enable = state_ready || (state == RX_LOCKED);

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) err <= OK;
      else err <= error_nxt;
   end

   assign error_nxt = (error_check_enable && i_fap_missing) ? FAP_MISSING : ((error_check_enable && i_crc_error) ? CRC_ERROR : err);

   // -------------------------------------------------------------
   // Output assignments
   // -------------------------------------------------------------

   assign o_state   = state;
   assign o_ecode   = err;
   assign o_pd_ack  = i_remote_pd_req;

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) begin
         o_rst_n <= 1'b0;
      end else begin
         o_rst_n <= ~(state == SLEEP) && ~(state == RESET) && ~(state == FAULT_FATAL);
      end
   end

   always_ff @(posedge axis_clk) begin
      if (~axis_rst_n) begin
         o_allow_user_tx <= 1'b0;
      end else if (usr_pd_req_latched | remote_pd_req_latched) begin
         o_allow_user_tx <= 1'b0;
      end else if (state == LINK_READY) begin
         o_allow_user_tx <= 1'b1;
      end
   end

endmodule  //qeciphy_controller
