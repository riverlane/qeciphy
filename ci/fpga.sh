module purge
module load xilinx/vivado
make clean
make generate-xci OPT_PROFILE=zcu216
make synth OPT_PROFILE=zcu216
