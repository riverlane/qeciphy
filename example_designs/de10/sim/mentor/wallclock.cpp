#include <time.h>

extern "C" int wallclock() {
   return time(NULL);
}

// right under the module top add this --
//
// integer end_time;
// integer start_time;
// import "DPI-C" function int wallclock();
// initial begin
//     start_time = wallclock();
// end


// to report add this --
//
// end_time = wallclock();
// $display("Total Elapsed time about %d seconds", end_time - start_time);

// right before elab in run.do add this
// vlog wallclock.cpp