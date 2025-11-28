
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY__UVMTB_COMMON_SVH_
`define QECIPHY__UVMTB_COMMON_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Typedefs, constants, functions and tasks for use within the qeciphy environment's package.
//------------------------------------------------------------------------------------------------------------------------------------------

   //parameter real T_DFLT_DUT_ACLK_PERIOD_NS   = 6.25;
   //parameter real T_DFLT_DUT_RCLK_PERIOD_NS   = 6.40;
   //parameter real T_DFLT_DUT_FCLK_PERIOD_NS   = 6.40;
   //parameter real T_DFLT_TBPHY_ACLK_PERIOD_NS = 6.25;
   //parameter real T_DFLT_TBPHY_RCLK_PERIOD_NS = 6.40;
   //parameter real T_DFLT_TBPHY_FCLK_PERIOD_NS = 6.40;

   parameter real T_DFLT_DUT_ACLK_PERIOD_NS   = 4.0;
   parameter real T_DFLT_DUT_RCLK_PERIOD_NS   = 8.0;
   parameter real T_DFLT_DUT_FCLK_PERIOD_NS   = 8.0;
   parameter real T_DFLT_TBPHY_ACLK_PERIOD_NS = 4.0;
   parameter real T_DFLT_TBPHY_RCLK_PERIOD_NS = 8.0;
   parameter real T_DFLT_TBPHY_FCLK_PERIOD_NS = 8.0;




//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY__UVMTB_COMMON_SVH_
