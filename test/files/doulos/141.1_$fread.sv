// Section 141.1: $fread

parameter NumPatterns = 100;
integer Pattern;

reg [3:0] StimUp[1:NumPatterns];
reg [3:0] StimDown[NumPatterns:1];

$fread (StimUp, "stimulus.txt", 5);   // First loaded data 
              // is StimUp[5] then StimUp[6]
$fread (StimDown, "stimulus.txt", 5); // First loaded data 
              // is StimDown[5] then StimDown[6]


