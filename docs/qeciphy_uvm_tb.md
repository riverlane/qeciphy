# QECi Phy UVM top level tb structure
The block diagram below shows the structure of the top-level of the UVM TB.
| ![](./qeci_phy_uvmtb.jpg) |
|:--:|
| *Block Diagram of QECi Phy UVM TB* |

# Description of Agents
   # QECIPHY instances
   The i_dut instance is the QECi Phy being tested in the TB.
   The i_tbphy instance is another QECi Phy which is needed to process/drive the DUT signals (it is effectively acting as a simulation model).
   # Clock/Reset Interfaces
   There is one riv_clk_rst_gen_vip_if instance per clock on each instance of the QECi Phy (DUT and TB Phy).
   These interfaces drive the ACLK, RCLK and FCLK clocks as well as the single ARST_n (which comes from the i_dut_aclk_if and i_tbphy_aclk_if generators respectively.
   The generators (which are just SV interfaces with methods to configure them) are accessed from environment sequences via the sequencer's config object (e.g. p_sequencer.m_config.m_vifs.dut_aclk_vif).
   They can also be accessed from scoreboards and coverage_collectors via the m_config.m_vifs field.
   # P-Bus BFMs (containing Interfaces)
   There is one P-Bus agent for each QECIPHY instance (i_dut and i_tbphy).
   These agents allow driving and monitoring of the P-Bus signals and attached to the m_dut_pbus_agt and m_tbphy_pbus_agt agents in the environment.
   # Rdy/Vld Sink BFMs (containing Interfaces)
   There is one Rdy/Vld Sink agent for each QECIPHY instance (i_dut and i_tbphy).
   These agents allow monitoring of the AXI-Stream Rx channel signals.
   They are attached to the m_dut_axis_rx_agt and m_tbphy_axis_rx_agt agents in the environment.
   In this TB, the RDY signals of these interfaces are constantly driven to 1 by the agents (as per QECi-Phy spec).
   # Rdy/Vld Source BFMs (containing Interfaces)
   There is one Rdy/Vld Source agent for each QECIPHY instance (i_dut and i_tbphy).
   These agents allow driving and monitoring of the AXI-Stream Tx channel signals.
   They are attached to the m_dut_axis_tx_agt and m_tbphy_axis_tx_agt agents in the environment.
   # Differential Pair Interfaces
   There are 2 riv_diff_pair_connector_vip_if connecting the i_dut and i_tbphy QECIPHY instances (one per direction, identified by instance name).
   These interfaces act, by default, as simple differntial-pair wires but can be driven via methods defined in them to disconnect, force, swap or short the two wires they model.
   The interfaces and methods are accessed from environment sequences via the sequencer's config object (e.g. p_sequencer.m_config.m_vifs.dut2tbphy_conn_vif).
   They can also be accessed from scoreboards and coverage_collectors via the m_config.m_vifs field.
   # MISC I/O Interface
   The qeciphy_env_miscio_if interface provides connections to the clocks and resets of each QECIPHY instance as well as their ECODE and STATUS outputs.
   The interface is accessed from environment sequences via the sequencer's config object (e.g. p_sequencer.m_config.m_vifs.miscio_vif).
   It can also be accessed from scoreboards and coverage_collectors via the m_config.m_vifs field.

