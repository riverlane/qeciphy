# QECIPHY Architecture

## Overview

QECIPHY is a high-speed serial communication protocol designed for reliable data transmission over multi-gigabit links between FPGAs from different product families. It implements automatic link establishment, frame alignment, error detection, and comprehensive error handling with AXI4-Stream compliant interfaces.

The aim of this module is to hide the complexity of high-speed serial communication using transceiver primitives and provide a simple interface for users to transmit and receive data across FPGAs with low latency, high reliability and minimal configuration.

## Working Principle

### 1. Protocol Overview

QECIPHY implements a frame-based protocol with periodic overhead insertion for link maintenance and data integrity verification. The protocol operates on 64-bit data words transmitted at the GT transceiver rate and includes three types of packets:

**Frame Alignment Words (FAW)**: Synchronization patterns inserted every 64 clock cycles to maintain frame alignment between transmitter and receiver. They carry link status information and contain distinctive bit patterns (`0xBC` and `0xCB`) for alignment detection.

**Validation Words (CRC)**: Data integrity packets inserted every 7 clock cycles containing CRC checksums calculated over the previous data segments. These enable real-time error detection and reporting.

**User Data/Idle Words**: Actual payload data from user logic or idle patterns when no data is available.

### 2. Link Establishment Procedure

Once QECIPHY comes out of reset, the transmitter immediately begins sending boundary words (Frame Alignment Words and Validation Words) to help the remote receiver achieve synchronization. No user data is accepted during this initial phase.

On the receiver side, the incoming serial data stream first undergoes byte alignment. The byte alignment process finds the distinctive comma patterns (0xBC) embedded in the Frame Alignment Words. Once byte alignment is achieved, the word aligner combines the 32-bit words from the transceiver into properly framed 64-bit words by testing different combinations and selecting the one that shows valid FAW patterns.

With the word aligned, the receiver begins processing the data stream to detect Frame Alignment Words. The receiver searches for seven consecutive valid FAWs to ensure stable frame synchronization before declaring itself locked. During this process, the transmitter continues sending boundary patterns and monitors the FAW packets from the remote side to determine when the remote receiver has also achieved lock.

Once both receivers on each side of the link have achieved frame synchronization, the transmitter enables user data transmission. At this point, the link becomes fully operational and can accept user data through the AXI4-Stream interface. The transmitter multiplexes user data with the required boundary words while the receiver filters out protocol overhead and delivers only valid user data to the output interface.

If any fatal errors occur during the establishment process or during normal operation, the link immediately transitions to a fault state and remains there until the entire IP is reset.

### 3. Frame Alignment Word (FAW) Structure

FAWs are 64-bit packets with the following structure:

```
Bits [63:40]: rx_rdy (1) + reserved (23) 
Bits [39:32]: word_alignment_marker = 0xCB
Bits [31:8]:  reserved (24)
Bits [7:0]:   byte_comma = 0xBC
```

**Key Features**:
- **Frequency**: Inserted every 64 clock cycles (1.56% overhead)
- **Alignment Patterns**: Two alignment sequences (0xBC, 0xCB) enable byte and word alignment detection
- **Status Information**: `rx_rdy` bit communicates local receiver status to remote transmitter

### 4. Validation Word Structure

Validation Words are 64-bit CRC packets with the following structure:

```
Bits [63:48]: crc45 (CRC16-IBM3740 for data words 4-5)
Bits [47:32]: crc23 (CRC16-IBM3740 for data words 2-3)  
Bits [31:16]: crc01 (CRC16-IBM3740 for data words 0-1)
Bits [15:14]: reserved (2)
Bits [13:8]:  valids (6-bit mask indicating which data segments contain valid user data)
Bits [7:0]:   crcvw (CRC8-SMBUS protecting the valids field)
```

**Key Features**:
- **Frequency**: Inserted every 7 clock cycles (14.06% overhead)
- **Multi-Channel Protection**: Three separate CRC16 calculations protect different data word pairs
- **Valid Data Tracking**: 6-bit mask tracks which of the 6 data words between CRC packets contain actual user data (vs. idle)
- **Meta-CRC**: CRC8 protects the validity mask itself from corruption

### 5. Transmission Timing and Overhead

The protocol operates with deterministic timing:

**Total Overhead**: ~15.6% (1.56% FAW + 14.06% CRC)
- **Frame Period**: 64 clock cycles 
- **CRC Period**: 7 clock cycles
- **Frame Structure**: 1 FAW + 9 x (6 Data Words + 1 CRC) = 64 total cycles
- **Data Opportunities**: 54 out of 64 cycles available for user data (remainder occupied by 1 FAW + 9 CRC words)

## Clock Domains

**User Clocks:**
- `ACLK`: User AXI4-Stream interface clock
- `RCLK`: GT reference clock
- `FCLK`: Free-running fabric clock for internal logic

**Generated Clocks:**
- `tx_clk`: TX clock (Generated by GT from RCLK for 64-bit data)
- `tx_clk_2x`: 2x TX clock (synchronized to TX clock for 32-bit data)
- `rx_clk`: RX clock (Generated by GT through CDR for 64-bit data)
- `rx_clk_2x`: 2x RX clock (synchronized to RX clock for 32-bit data)

**Clock Relationships:**
- ACLK, RCLK, and FCLK can be asynchronous to each other
- TX clocks are derived from RCLK
- RX clocks are recovered from incoming data stream
- TX and RX clocks operate at the same frequency but are independent
- 2x clocks run at double the rate and are phase-aligned with their respective base clocks

## Implementation

This section aims to provide basic details of the key modules and their internal workings. To learn more, please refer to the individual module documentation in the source code.

### 1. Top-Level Module (QECIPHY.sv)

The top module that:
- Implements AXI4-Stream interfaces for user data
- Orchestrates all submodules

### 2. Reset Controller

The reset controller (`qeciphy_resetcontroller.sv`) manages the complex reset sequencing required for GT transceivers and datapath logic across multiple clock domains.

**Working Principle:**
- Waits for GT power good signal
- Provides 1250 cycle delay in FCLK domain
- Releases GT resets and waits for GT reset done signals
- Provides additional 32 cycle delay in ACLK domain
- Releases all datapath resets simultaneously
- Asserts reset sequence completion

**Cross-Domain Reset Synchronization:**
- State machine runs in ACLK domain
- Reset deassertion synchronized to each destination clock
- Prevents metastability during reset release

### 3. Link Controller

The link controller (`qeciphy_controller.sv`) manages the link establishment and state transitions based on status signals from the TX and RX paths.

**Key Features:**
- Monitors status signals from different modules
- Manages link state transitions
- Interfaces with TX and RX data paths for enable signals
- Maps the internal states to spec compliant link states

**Link Establishment Sequence:**
1. `RESET` -> IP in reset state
2. `WAIT_RESET_DONE` -> Wait for reset completion
3. `TX_LINK_ENABLE` -> Start transmitting alignment patterns
4. `WAIT_RX_DATAPATH_ALIGN` -> Wait for SERDES byte/word alignment
5. `RX_ENABLE` -> Start processing RX data
6. `WAIT_RX_LOCKED` -> Wait for local RX frame synchronization
7. `LOCAL_RX_LOCKED` -> Wait for remote RX frame synchronization
8. `BOTH_RX_LOCKED` -> Both ends synchronized
9. `TX_DATA_ENABLE` -> Enable user data transmission
10. `READY` -> Link is fully operational for bidirectional data

**Error Handling:**
- Fatal faults cause immediate transition to `FAULT_FATAL` state
- Fault state persists until system reset

### 4. TX Data Path

```
User AXI4-S -> TX FIFO -> TX Channel Encoder -> SERDES TX

TX Channel Encoder:
TX Boundary Gen -> TX Controller -> TX Packet Gen

SERDES TX:
TX 64b to 32b Serializer -> GT Primitive
```

**Flow Control:**
- Backpressure via `TX_TREADY` when TX FIFO is full or link is not ready
- User data is enabled only when link is established and remote is ready

#### 4.1 TX Controller
The TX controller (`qeciphy_tx_controller.sv`) manages transmission states:
   - Link Enable: FAW + CRC + Idle words
   - Data Enable: FAW + CRC + User data (or Idle if no data)

#### 4.2 TX Boundary Generator
The TX boundary generator (`qeciphy_tx_boundary_gen.sv`) creates timing signals for inserting boundary words.
   - FAW boundaries: Every 64 cycles (provides frame structure)
   - CRC boundaries: Every 7 cycles (for validation word insertion)

#### 4.3 TX Packet Generator
The TX packet generator (`qeciphy_tx_packet_gen.sv`) constructs the actual data packets to be sent over the link.
   - 3-stage pipeline for packet assembly
   - Inserts the following respecting TX controller mode:
     - Frame Alignment Words (FAW) at FAW boundaries
     - Validation Words (CRC) at CRC boundaries
     - Idle Words when no user data is available
   - Refer to the CRC implementation details below for validation word generation

#### 4.4 TX 64b to 32b Serializer
The TX 64b to 32b serializer (`qeciphy_tx_64b_to_32b.sv`) uses a toggle counter to alternate between upper and lower 32 bits of 64 bit data

### 5. RX Data Path

```
SERDES RX -> RX Channel Decoder -> RX FIFO -> User AXI4-S

SERDES RX:
GT Primitive -> RX Byte Aligner -> RX Word Aligner (32b to 64b)

RX Channel Decoder:
RX Boundary Gen -> RX Monitor -> User Data
```

**Flow Control:**
- Data is valid only when link is ready and valid user data is received
- RX FIFO overflow protection with error reporting

#### 5.1 RX Byte Aligner

The byte aligner (`qeciphy_rx_bytealigner.sv`) performs automatic byte alignment using slide control and comma detection (`0xBC` pattern every 128 32-bit words) through an 8-state FSM:
1. **IDLE**: Wait for slide ready from GT
2. **SLIDE0/SLIDE1**: Assert slide for 2 cycles
3. **OFF**: Deassert slide for 32+ cycles (GT requirement)
4. **CHECK**: Look for comma patterns; slide again if not found, otherwise proceed to REVIEW
5. **REVIEW**: Verify pattern stability
6. **DONE**: Alignment successful (sticky)
7. **FAIL**: Alignment failed after max attempts, restart process

#### 5.2 RX Word Aligner

The word aligner (`qeciphy_rx_32b_to_64b.sv`) creates two possible 64-bit combinations in `rx_clk_2x` domain:
   - **Option 0**: `{current_32b, previous_32b}`
   - **Option 1**: `{previous_32b, older_32b}`

FAW detection tests both options in `rx_clk` domain and locks onto the one showing valid FAW patterns.

#### 5.3 RX Controller
The RX controller (`qeciphy_rx_controller.sv`) manages the RX states and error handling:
   - Manages reception states:
      - Disabled: No data output
      - Enabled: Validated user data output
   - Latches RX errors until disabled

#### 5.4 RX Boundary Generator
The RX boundary generator (`qeciphy_rx_boundary_gen.sv`) uses an FSM to detect FAW patterns and generate timing signals:
   - 8-state FSM: RESET -> DISABLED -> ALIGN -> CHECK -> LOCKED -> FAW_START -> CRC_START -> OPERATIONAL
   - Searches for 7 consecutive valid FAWs before declaring lock
   - Generates synchronized timing for FAW and CRC validation

#### 5.5 RX Monitor
The RX monitor (`qeciphy_rx_monitor.sv`) validates and filters incoming data:
   - 11-stage pipeline for data processing
   - FAW error detection
   - CRC validation (Refer to CRC Implementation Details below)
   - Any detected errors are latched until the module is disabled
   - Remote RX lock detection
   - Filters out protocol overhead: Frame Alignment Words, Validation Words, and Idle Words; outputs only valid user data

### 6. Error Handler
The error handler (`qeciphy_error_handler.sv`) implements a comprehensive error management system:
- **Centralized Collection**: Aggregates errors from all subsystems
- **Fault Latching**: Errors persist until system reset

**Error Types:**
- FAW Error: Frame alignment issues
- CRC Error: Data integrity violations
- TX FIFO Overflow: Transmit buffer overflow
- RX FIFO Overflow: Receive buffer overflow

### 7. Clock Domain Crossing

The CDC module (`qeciphy_cdc.sv`) implements comprehensive CDC management across all the required clock domains.

All crossings use 2-FF synchronizers (`riv_synchronizer_2ff`) for metastability prevention.


### 8. CRC Implementation Details

The CRC subsystem provides multi-level error detection through a sophisticated pipelined architecture that operates concurrently with data processing.

#### 8.1 CRC Computation Engine
The CRC computation engine (`qeciphy_crc_compute.sv`) calculates four distinct CRC values over different segments of the data stream using a multi-channel pipelined design.
- **CRC01**: CRC16-IBM3740 protecting data words 0-1 
- **CRC23**: CRC16-IBM3740 protecting data words 2-3 
- **CRC45**: CRC16-IBM3740 protecting data words 4-5 
- **CRCVW**: CRC8-SMBUS protecting valid bits

**Staggered Operation:** Each CRC calculator operates with different enable and reset timing to ensure proper pipeline operation.

#### 8.2 CRC Validation Engine
The CRC validation engine (`qeciphy_crc_validate.sv`) verifies the computed CRC values against expected values received in validation packets.
   - **2-cycle pipeline** for CRC comparison
   - **Byte-wise comparison** to reduce combinational logic complexity
   - **Error latching** until next validation cycle
   - **Concurrent validation** of all four CRC values during CRC boundary cycles






