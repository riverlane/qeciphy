#!/usr/bin/env bash

# Guard against someone running `source scripts/deploy_zcu111.sh`
if [[ "${BASH_SOURCE[0]}" != "${0}" ]]; then
    echo "ERROR: Do not source this script. Run it with: ./scripts/deploy_zcu111.sh"
    return 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"

# --- Configuration ---
BOARD_IP="${1:-10.30.70.118}"
BOARD_USER="xilinx"
REMOTE_DIR="/home/xilinx"
TOP_NAME="qeciphy_syn_wrapper"
BD_NAME="zcu111_debug_bridge"

IMPL_DIR="$REPO_ROOT/run/synth_qeciphy/synth_qeciphy.runs/impl_1"
GEN_HWH="$REPO_ROOT/run/synth_qeciphy/synth_qeciphy.gen/sources_1/bd/${BD_NAME}/hw_handoff/${BD_NAME}.hwh"

BIT_FILE="$IMPL_DIR/${TOP_NAME}.bit"
LTX_FILE="$IMPL_DIR/${TOP_NAME}.ltx"

if [[ -f "$GEN_HWH" ]]; then
    HWH_FILE="$GEN_HWH"
elif [[ -f "$REPO_ROOT/${TOP_NAME}.hwh" ]]; then
    HWH_FILE="$REPO_ROOT/${TOP_NAME}.hwh"
else
    HWH_FILE=""
fi

if [[ ! -f "$BIT_FILE" || -z "$HWH_FILE" || ! -f "$LTX_FILE" ]]; then
    echo "ERROR: Missing build artifact(s):"
    echo "  BIT: $BIT_FILE ($( [[ -f "$BIT_FILE" ]] && echo OK || echo 'NOT FOUND' ))"
    echo "  HWH: ${HWH_FILE:-NOT FOUND}"
    echo "  LTX: $LTX_FILE ($( [[ -f "$LTX_FILE" ]] && echo OK || echo 'NOT FOUND' ))"
    exit 1
fi

echo "==> Using artifacts:"
echo "    BIT: $BIT_FILE"
echo "    HWH: $HWH_FILE -> ${TOP_NAME}.hwh"
echo "    LTX: $LTX_FILE"

# 1. Stop any running XVC / start_pynq.py process safely
echo "==> Stopping existing PYNQ XVC process on ${BOARD_IP}..."
ssh "${BOARD_USER}@${BOARD_IP}" "sudo -n pkill -f [s]tart_pynq.py || true" || { echo "SSH failed"; exit 1; }

# 2. Upload .bit and renamed .hwh to ZCU111
echo "==> Uploading .bit and renamed .hwh to ${BOARD_IP}..."
scp "$BIT_FILE" "${BOARD_USER}@${BOARD_IP}:${REMOTE_DIR}/${TOP_NAME}.bit" || exit 1
scp "$HWH_FILE" "${BOARD_USER}@${BOARD_IP}:${REMOTE_DIR}/${TOP_NAME}.hwh" || exit 1

# 3. Start start_pynq.py in the background on ZCU111 using pynq-venv
echo "==> Loading overlay and starting XVC server on ${BOARD_IP}..."
ssh "${BOARD_USER}@${BOARD_IP}" "nohup sudo -n bash -c 'source /etc/profile.d/pynq_venv.sh; source /etc/profile.d/xrt_setup.sh 2>/dev/null || true; python3 ${REMOTE_DIR}/start_pynq.py' > ${REMOTE_DIR}/xvc.log 2>&1 < /dev/null &" || exit 1

# Wait until TCP port 2542 is actually open (up to 20s)
echo -n "==> Waiting for XVC server on ${BOARD_IP}:2542"
READY=0
for i in {1..20}; do
    if timeout 1 bash -c "</dev/tcp/${BOARD_IP}/2542" 2>/dev/null; then
        echo " READY!"
        READY=1
        break
    fi
    echo -n "."
    sleep 1
done

if [[ "$READY" -ne 1 ]]; then
    echo " TIMEOUT!"
    echo "==> Remote xvc.log output:"
    ssh "${BOARD_USER}@${BOARD_IP}" "cat ${REMOTE_DIR}/xvc.log"
    exit 1
fi

# 4. Preload system zlib for cs_server (Vivado 2024.1 Linux fix)
pkill -f [c]s_server || true
LD_PRELOAD=/lib64/libz.so.1 /slurm_tools/xilinx/Vivado/2024.1/bin/cs_server -d -s tcp::3042

# 5. Launch Vivado Hardware Manager and load .ltx automatically
echo "==> Launching Vivado Hardware Manager..."
vivado -mode gui -source "$SCRIPT_DIR/open_xvc_hw.tcl" -tclargs "$BOARD_IP" "$(realpath "$LTX_FILE")" &
