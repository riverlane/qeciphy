module purge
module load xilinx/vivado
make clean
make sim OPT_PROFILE=zcu216
