// Section 71.1: Nettype

typedef struct {
	int x;
	int y;
	real r;
} R;

function automatic R RAvg(input R driver[]);
  RAvg = '{x:0, y:0, r:0.0};

  foreach (driver[i]) begin
    /*...*/
  end
  /*...*/
endfunction

nettype R wRAvg with RAvg;


