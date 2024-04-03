// Copyright (C) 2016 Doulos Ltd. All rights reserved.

// The information contained herein is the provided for the convenience
// of readers of the UVM Golden Reference Guide, and is supplied
// without liability for errors or omissions. Subject to the following
// paragraphs, code snippets may be used freely within your own code,
// and there is no obligation to acknowledge Doulos.  Our only
// restriction, is that this body of code snippets may not be published
// for public viewing in any form or medium without the written
// permission of Doulos. Examples of prohibited use would include
// publication on a website or use within a book or magazine. Examples
// of valid use would include being part of your UVM verification code
// for projects and electronic product design, whether commercial,
// private, government or non-profit.

// Unless required by applicable law or agreed to in writing, Doulos
// provides the these code snippets on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied,
// including, without limitation, any warranties or conditions of
// TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
// PARTICULAR PURPOSE. You are solely responsible for determining the
// appropriateness of using or redistributing the Work and assume any
// risks associated with Your exercise of permissions under this
// License.

// Limitation of Liability. In no event and under no legal theory,
// whether in tort (including negligence), contract, or otherwise,
// unless required by applicable law (such as deliberate and grossly
// negligent acts) or agreed to in writing, shall Doulos be liable to
// You for damages, including any direct, indirect, special,
// incidental, or consequential damages of any character arising as a
// result of this License or out of the use or inability to use the
// Work (including but not limited to damages for loss of goodwill,
// work stoppage, computer failure or malfunction, or any and all other
// commercial damages or losses), even if such Doulos has been advised
// of the possibility of such damages.

///////////////////////////////////////////////////////////////////////

// NOTE: Section numbers are merely a way to sort the sections.
// Also, not all sections of the GRG have examples.

// Section 1.1: Alias

// Reverse the bits of bi-directional ports
module ReverseBits (inout [7:0] A, B);
  alias A = {B[0],B[1],B[2],B[3],B[4],B[5],B[6],B[7]};
endmodule


// Section 1.2: Alias

// C is implicitly declared as an 1-bit wire
wire [8:0] word9;
wire [7:0] word;
alias word9 = {word, C};


// Section 2.1: Always

always @(A or B or C or D) // Equiv. to @(*), @*, or @(A, B, C, D)
begin
  R = {A, B, C, D};
  F = 0;

  for (int I = 0; I < 4; I = I + 1)
    if (R[I])
    begin
      F = I;
      break;
    end
end


// Section 2.2: Always

always_comb
  A = B & C;
always_comb
  A <= #10ns B & C;

  
// Section 2.3: Always
  
always_ff @(posedge Clk iff Reset == 0 or posedge Reset)
  begin
    ...
  end

always_ff @(posedge Clock iff nReset or negedge nReset)
  begin
    if (~nReset)                    // Asynchronous reset
      Count <= 0;
    else
      if (~Load)                    // Synchronous load
        Count <= Data;
      else
        Count <= Count + 1;
  end

always_ff @(edge Clk, posedge Reset) // Daul Data Rate (DDR)
  begin                              // clock on both edges
    ...
  end

always_ff @(Clk, posedge Reset) // Alternative DDR coding style
  begin
    ...
  end
  
  
// Section 2.4: Always
  
always_latch
  if (Enable) Q <= D;


// Section 3.1: Array

wire  [7:0] A [0:15][0:15], B[0:15][0:15];  // Two 16x16 array of bytes
A[0][1][2] = B[1][2][3];     // Bit-select

A = B;

logic [15:0] Array1;
logic [7:0] Array2;
Array2 = Array1[8:1];        // Part-select

int A [7:0];
int B [31:0];
assign A = B[7:0];        // B[7:0] is also an unpacked aray


// Section 3.2: Array

// Reading and writing a variable slice of the array
A[x+:c] = B[y+:c];                   // c must be constant


// Section 3.3: Array

// Multiple packed dimensions defined in stages using typedef
typedef bit [0:7] B8;
B8 [0:15] B8_16;                     // [0:7] varies most rapidly


// Section 3.4: Array

// Multiple unpacked dimensions defined in stages using typedef
typedef B8 Mem[0:3];                 // Array of four B8 elements
Mem Mem8[0:7];                       // Array of 8 Mem elements


// Section 4.1: Array Manipulation Methods

byte b[] = '{1, 3, 2};
byte s, r[$];
r = b.find(x) with (x > 2);          // r = {3}
r = b.find with (item == item.index);// find all items equal to their 
                                     // index, i.e. {2}
r = b.min;                           // r = 1
b.reverse;                           // b = '{2, 3, 1}
b.sort;                              // b = '{1, 2, 3}
s = b.sum with (item + 4);           // s = 18 (i.e. 5 + 7 + 6)
s = b.xor;                           // s =  0 (i.e. 1 ^ 3 ^ 2)

  
// Section 4.2: Array Manipulation Methods

// Find all items in Ar1 that are greater than corresponding item in Ar2
int Ar1[3:0][3:0], Ar2[3:0][3:0];
int r[$];
r = Ar1.find(x) with (x > Ar2[x.index(1)][x.index(2)]);      


// Section 5.1: Assert (Immediate)

always @(posedge clk)
  assert (State != Illegal_State)
    else $error ("Illegal state reached");

initial
begin
  assert (A == B);
  assert (C && D) $display("OK - C and D are both true");
  assert (E) else $warning("E is NOT true");
end


// Section 6.1: Assign

//Continuous assignment
wire cout, cin;
wire [31:0] sum, a, b;

assign {cout, sum} = a + b + cin;


// Section 6.2: Assign

// Procedural continuous assignment (Deprecated!)
always @(posedge Clock)
  Count = Count + 1;
always @(Reset)         // Asynchronous Reset
  if (Reset)
    assign Count = 0;   // Prevents counting, until Reset goes low
  else
    deassign Count;     // Resume counting on next posedge Clock


// Section 7.1: Associative Array

// Create an array of integer, indexed by string
integer CountWords [string];
CountWords["one"]++;
$display("There are %0d different words", CountWords.num);
CountWords.delete("one");              // Deletes the "one" entry
CountWords.delete;                     // Clears the entire array


// Section 7.2: Associative Array

// Create an array of string, indexed by integers
string Table [*];
Table = '{0:"Zero", 1:"One", 2:"Two", default:"None"};
$display("%s %s", Table[0], Table[3]); // Displays "Zero None"


// Section 8.1: Attribute

(*synthesis, parallel_case *) casez (Opcode)
  4'b??01 : action1;
  4'b1?0? : action2;
...


// Section 8.2: Attribute

// Attribute attached to an operator
A = B + (* mode = "cla" *) C; 


// Section 8.3: Attribute

// Attribute attached to a function call
A = add (* mode = "cla" *) (B, C); 


// Section 8.4: Attribute

// Attribute attached to a conditional operator 
A = B ? (* no_glitch *) C : D; 


// Section 8.5: Attribute

// Attribute attached to an interface
(*interface_att = 10*) interface Int1 ... endinterface


// Section 8.6: Attribute

// Attribute attached to a module definition
(* optimize_power *) module M1 (...);


// Section 9.1: Begin

initial
begin
  Load = 0;              // Time 0
  Enable = 0;
  Reset = 0;
  #10  Reset = 1;        // Time 10
  #25  Enable = 1;       // Time 35
  #100 Load = 1;         // Time 135
end

initial
begin : AssignInputs
  for (int I = 0; I < 8; I = I + 1)
    #Period {A, B, C} = I;
end : AssignInputs


// Section 10.1: Bind

// Binding a module to a module and a module instance
module Test (input bit[7:0] Addr, Data);
  ...
endmodule

module CheckAddr (input bit[7:0] Addr, Max);
    A1: assert property (Addr <= Max)
        else $error("Address is out of range");
endmodule

module RAM (input bit[7:0] Addr, Data, ...);
  ...
endmodule

module TestRAM;
  ...
  RAM RAM_inst (Addr, Data, ...);
endmodule

// Binds an instance of the module Test to the testbench
bind TestRAM Test Test_inst(Addr, Data);

// Binds an instance of the module CheckAddr to the RAM instance
bind TestRAM.RAM_inst CheckAddr CA_inst(Addr, Data);

// Alternative syntax for the above
bind RAM: RAM_inst CheckAddr CA_inst(Addr, Data);


// Section 11.1: Bind (Operator Overload)

typedef struct {
  bit  A;
  real B;
} A_Struct;
A_Struct X, Y, Z, Q;

bind + function A_Struct fadds(A_Struct, A_Struct);
bind + function A_Struct faddr(A_Struct, real);
bind + function A_Struct faddi(A_Struct, int);

assign Q = X + 2.0; // Equivalent to Q = faddr (X, 2.0)
assign Y = X + 5;   // Equivalent to Y = faddi (X, 5)
always @(posedge clk) Z += X;   // Equivalent to Z = Z + X,
                                // i.e. Z = fadds (Z, X)


// Section 12.1: Case

case (Address)
  0 : A <= 1;        // Select a single Address value
  1 : begin          // Execute more than one statement
        A <= 1;
        B <= 1;
      end
  2, 3, 4 : C <= 1;  // Pick out several Address values
  default :          // Mop up the rest
    $display("Illegal Address value %h in %m at %t",
             Address, $realtime);
endcase


// Section 12.2: Case

casez ({A, B, C, D, E[3:0]})
  8'b1??????? : Op <= 2'b00;
  8'b010????? : Op <= 2'b01;
  8'b001???00 : Op <= 2'b10;
  default :     Op <= 2'bxx;
endcase


// Section 12.3: Case

// Pattern-matching case statement
typedef union tagged {
  void Invalid;
  int  Valid;
} VInt;
...
VInt v;
...
case (v) matches
  tagged Invalid  : $display ("v is Invalid");
  tagged Valid .n : $display ("v is Valid with value %d", n);
endcase


// Section 13.1: Casting

typedef struct {
  bit A;
  union packed {int i; bit[31:0] f;} B; 
} Struct1;

typedef bit [$bits(Struct1) - 1 : 0] C_Type; 

Struct1 S[7:0];             // Unpacked array of structures
C_Type C = C_Type'(S[1]);   // Convert structure to array of bits
S[2] = Struct1'(C);         // Convert array of bits back to structure


// Section 14.1: Chandle

// Standard C functions imported in SystemVerilog:
import "DPI-C" function chandle malloc(int size);
import "DPI-C" function void free(chandle ptr); 


// Section 15.1: Class

// Class definition
class Register;
  // Properties
  logic [7:0] data;

  // Methods
  function new (logic[7:0] d = 0); // Constructor
    data = d;
  endfunction

  task load (logic[7:0] d);
    data = d;
  endtask
endclass


// Section 15.2: Class

// Using the Register class
Register accum;  // accum stores a handle to an object of class Register
accum = new;     // Create a new Register object; its handle is in accum
Register accum1 = new;         // Alternative
Register accum2 = new(8'hff);  // Initialize
Register accum3[10];
  foreach (accum3[i]) accum3[i] = new; // Array of 10 Registers

accum.data = 8'h1f;         // Store value in data member
accum.load(8'h1f);          // A better way of doing it


// Section 15.3: Class

// Parameterised classes
class Register #(parameter n = 8);
  logic [n-1:0] data;
  ...
endclass

Register #(8) accum8 = new;           // 8-bit register
Register #(.n(16)) accum16 = new;     // 16-bit register

class Register #(parameter type T);
  T data;
  ...
endclass

Register #(int) accum8 = new;         // int register
Register #(bit [7:0]) accum16 = new;  // bit[7:0] register


// Section 15.4: Class

// Derived class
class ShiftRegister extends Register;
  extern task shiftleft();
  extern task shiftright();
endclass


// Section 15.5: Class

// Out of class method definitions
task ShiftRegister::shiftleft();
  data = data << 1;
endtask

task ShiftRegister::shiftright();
  data = data >> 1;
endtask

ShiftRegister SR = new;
SR.load(8'h55);                        // Inherited method
SR.shiftleft;                          // data now has 8'aa


// Section 16.1: Clocking

clocking CB1 @(negedge Clk);
  default input #1ns output #2ns;
  input Q;
  output Enable, Data;
  output #1step UpDn = top.Counter.UpDn;
  output posedge Load	;
endclocking


// Section 16.2: Clocking

// Synchronization statements - the events are sampled according to the clock domain timing:
@(CB1.Q);            // Wait for the next change of Q from CB1 domain
@(negedge CB1.Load); // Wait for negative edge of signal CB1.Load
@(posedge CB1.Load or negedge CB1.UpDn);
@(CB1.Q[1]);         // Wait for the next change of bit 1 of CB1.Q
@(CB1.Q[2:0]);       // Wait for the next change of the specified slice


// Section 16.3: Clocking

// Clocking Block Drives
CB1.Data[2:0] <= 3'h3;    // Drive 3-bit slice of Q in current cycle
##1 CB1.Data <= 4'hz;     // Wait 1 Clk cycle and then drive Q
##3 CB1.Data[3] <= 1'b0;  // Wait 3 Clk cycles, then drive bit 3 of Q
CB1.Data <= ##2 Int_Data; // Remember Int_Data, then drive Data after 2 clocks


// Section 16.4: Clocking

//Multiple clocking blocks:
interface I1 (input bit clock1);  ... endinterface
interface I2 (input bit clock2);  ... endinterface

module tf(I1 A, I2 B);
  clocking cb1 @(posedge A.clock1);
    default input #2 output #5;
    input A.address;
    output data = A.data;
  endclocking

  clocking cb2 @(posedge B.clock2);
    default input #1 output #1;
    output start = B.start, size = B.size;
  endclocking

  initial begin : Test
    cb1.data <= 1;        
    ...
  end

  module CtrlMod;
    default clocking cb1; // Clocking block cb1 set as default 
                          // inside CtrlMod module
    initial begin
        if (cb1.data == 1)
        ## 10;            // Delays execution by 10 cycles using the 
                          // default clocking (A.clock1)
        ...
  endmodule
endmodule


// Section 16.5: Clocking

interface ABus(input logic clk); // Interface with modports
  wire a, b, c, d;
  logic req, gnt;
  clocking cb @(posedge clk);
    input a;
    output b, c;
    inout d;
    property p1; req ##[1:3] gnt; endproperty
  endclocking

  modport DUT (input clk, b, c,// DUT modport
               output a, inout d);
  modport STB (clocking cb);   // Synchronous testbench modport
  modport TB  (input a,        // Asynchronous testbench modport
               output b, c, inout d);
endinterface

module AMod1(ABus.DUT b); 
  ...
endmodule

module TB (ABus.STB b1, ABus.STB b2 ); // 2 synchronous ports
  typedef virtual ABus.STB SYNCTB;
  task ATask(SYNCTB s);
    s.cb.a <= 1;
  endtask
  ...
endmodule

module top;
  logic clk;
  ABus b1(clk);
  ABus b2(clk);
  AMod1 M1(b1);
  TB Test(b1, b2);
  ...
endmodule


// Section 17.1: Comment

// This is a comment
/*
   So is this - across three lines
*/
module ALU /* 8-bit ALU */ (A, B, Opcode, F);


// Section 18.1: Compilation Unit

bit b;
function void AFunc;
  int b;
  b = $unit::b;     // $unit::b is the one outside
endfunction


// Section 19.1: Config

module Top(...);
  ...
  Acc U1(...);
  Acc U2(...);
  ...
module Acc(...);
  ...
  Adder A1(...);
  Adder A2(...);
...
config MyConfig;              // Simple config
  design MyDesign.Top;
  default liblist MyDesign;
  instance Top.U2 use MyGates.Acc;
endconfig

config MyConfig1;             // Hierarchical config - method 1
  design MyDesign.Top;
  instance Top.U2.A1
    use MyLib.Adder;
endconfig

config MyConfig2;             // Hierarchical config - method 2
  design MyDesign.Top;
  instance Top.U2.A1
    use MyLib.Adder;
  instance Top.U1.A2
    use MyGates.CarrySelectAdder : config;
endconfig

config CarrySelectAdder;
  design MyGates.CarrySelectAdder;
  ...
endconfig


// Section 20.1: Const

const int A = 1;

class MyClass;
  const int G = 1; // Global constant
  const int I;     // Instance constant
  function new(int x);
    I = 10;        // Instance constant assigned in constructor.
    ...     
  endfunction
endclass


// Section 21.1: Constraint

constraint c1 {a == 4;}
constraint c2 {b > 3; c > 10;}
constraint valid_parity {parity_ok dist {0:=1, 1:=9};}
constraint c3 {size == BIG -> len > 20;}
constraint c4 {i inside {1,[2:3]};}  // Equiv. to i==1 || i==2 || i==3
constraint c5 {solve b,c before a;}
constraint c6 {unique{a,b,c};}  // (a != b) && (b != c) && (c != a)


// Section 21.2: Constraint

x != 1000;                               // x can't be 1000
x dist {100 := 1, 1000 := 2, 2000 := 5}  // x is equal to 100 
                                         // or 2000 with weighted ratio of 1 - 5
										 
x dist {100 := 1, [4:6] :/ 2, 2000 := 5} // x is equal to one of
                                         // 100, 4, 5, 6 or 2000 with a weighted
                                         // ratio of 1- 2/3 - 2/3 - 2/3 - 5


// Section 21.3: Constraint

constraint c7 {soft a[0]==0; soft b[0]==1;} // lower priority
  randomize() with {soft a[0]==1; b[0]==0;} // higher priority


// Section 21.4: Constraint
  
virtual class Parent;
   pure constraint C;
endclass;

class Child extends Parent;
  int a, b;
  extern constraint C;         // must be overriden
endclass

constraint Child::C {a > b;}   // example of external constraint


// Section 22.1: Covergroup

// Covergroup containing options
covergroup CG (string Comment) @(posedge clk);
  option.comment = Comment;   // Comment for each instance of CG
  type_option.strobe = 1;     // Sample at the end of the time slot
  CP1 : coverpoint A {
    option.auto_bin_max = 8;  // Create 8 automatic bins for 
  }                           // coverpoint CP1 for each instance
endgroup


// Section 22.2: Covergroup

// Setting options and type options procedurally after instantiating a covergroup 
covergroup CG @(posedge clk);
  CP1 : coverpoint A;
  CP2 : coverpoint B;
endgroup
CG C1 = new;
C1.option.comment = "A comment set for the instance C1";
C1.CP1.option.auto_bin_max = 8;  // Create 8 automatic bins for 
                                 // coverpoint CP1 of instance C1
CG::type_option.comment = "A comment set for C1";
CG::CP1::type_option.weight = 10;


// Section 22.3: Covergroup

// Covergroups in classes
class Class1;
  bit AnEv;
endclass

class Class2;
  Class1 C1;                 // Object of Class1
  int Var;
  bit X;
  local logic Y,Z;
  
  covergroup CG1 @(C1.AnEv);   // Sampled on data member of C1
    coverpoint Var;
  endgroup 
  
  covergroup CG2 (int Arg) @X; // Second covergroup in the same
                               // class, now having arguments 
    option.at_least = Arg;    // Sets a coverage option of CG2
    coverpoint Y; 
  endgroup
  
  function new(int p);
    CG2 = new(p);
    C1 = new;  // C1 must be instantiated before CG1, because CG1  
               // uses it
    CG1 = new; 
  endfunction
endclass

initial begin
  Class2 Obj = new(7);
end


// Section 23.1: Coverpoint

//Simple example
bit [3:0] X, Y;
covergroup CG @(posedge clk);
  P1: coverpoint X;
  P2: coverpoint Y;
endgroup


// Section 23.2: Coverpoint

// Example showing bins and transitions
bit [5:0] V;
covergroup CG @(posedge clk);
  coverpoint V
  {
    bins a = {[0:3], 5};           // One bin for these values 
                                   // of V - 0, 1, 2, 3, or 5
    bins b[3] = {[6:11]};          // 3 bins: <6,7>,<8,9>,<10,11>
    bins c[2] = {[13:17]};         // 2 bins: <13,14>,<15,16,17>
    bins d[] = {18, 19};           // 2 bins: d[18], d[19]
    bins e[] = {[20:30], [25:40]}; // Overlapping values - OK
    bins f = (41 => 43), ([50:52],55=>56,57);
       // Associates the following sequences with bin f: 41=>43, or 50=>56, 
       // 51=>56, 52=>56, 55=>56, 50=>57, 51=>57, 52=>57, 55=>57
    bins h = {[60:$]}; // bin h: values from 60 to 63 ($ is max of V)
    ignore_bins ig_vals = {18, 19}; 
                       // ignores values, even though included in bin d
    illegal_bins ill_trans = (47 => 48 => 49); 
       // This sequence will produce a run-time eror
    wildcard bins wb = {5'b11??1}; // 11001 11011 11101 11111
    bins others[] = default;   
       // Any value not maching a, b[3], c[2], d[], e[], f, h, wb, etc.
  }
endgroup


// Section 23.3: Coverpoint

// More examples of transitions
1 => 2       // Single value transition: value of coverage point at 2 
             // successive sample points
1 => 3 => 5  // Sequence of transitions
1,2 => 3, 4  // Set of transitions, equiv. to: 1=>3, 1=>4, 2=>3, 2=>4
2 [* 3]      // Consecutive repetition, equiv. to 2=>2=>2
2 [* 2:4]    // Range of repetition, equiv. to , 2=>2, 2=>2=>2, 2=>2=>2=>2
2 [-> 3]     // Non-consecutive occurrence, equiv. to ...2=>...=>2...=>2
             // where ...  is any transition that does not contain the value 2
2 [= 3]      // Non-consecutive repetition, equiv. to 2=>...=>2...=>2...=>2 
             // excluding the last transition

			
// Section 24.1: Cross

bit [3:0] A, B;
covergroup CG1 @(posedge clk);
  AxB : cross A, B; // Coverpoints are implicitly created for a and b
                    // Each coverpoint has 16 bins, auto[0] to auto[15]
     // AxB has 16*16 cross products, and each cross product is a bin of AxB
  BC  : coverpoint B + C; // Expression defined as coverpoint
  AxBC: cross A, BC;// Cross of an implicit coverpoint and an expression
endgroup


// Section 24.2: Cross

covergroup CG2 @(posedge clk);
  CP_A: coverpoint A
  {
    bins CP_A1 = {[0:4]};
    bins CP_A2 = {[5:8]};
  }
  CP_B: coverpoint B
  {
    bins CP_B1 = {[1:5]};
    bins CP_B2 = {[7:12]};
  }
  Cr  : cross CP_A, CP_B
  {
    ignore_bins  EB = binsof(CP_A) intersect {5, [1:3]};
    illegal_bins IB = binsof(CP_A) intersect {12};
  bins Cr1 = ! binsof(CP_A) intersect {[6:9]}; 
             // 2 cross products: <CP_A1, CP_B1>, <CP_A1,CP_B2>
  bins Cr2 = binsof(CP_A.CP_A2) && binsof(CP_B.CP_B1);
             // 1 cross product: <CP_A2, CP_B1>
  }
endgroup


// Section 27.1: Defparam

module LayoutDelays;
  defparam Design.U1.T_f = 2.7;
  defparam Design.U2.T_f = 3.1;
  ...
endmodule

module Design (...);
  ...
  and_gate U1 (f, a, b);
  and_gate U2 (f, a, b);
  ...
endmodule

module and_gate (f, a, b);
  output f;
  input a, b;
  parameter T_f = 2;
  and #(T_f) (f,a,b);
endmodule


// Section 28.1: Delay

and #(5) a1 (out, in1, in2);         // Only one delay
bufif0 #(1,2,3) b1 (out, in, ctrl);  // Rise, fall and turn-off
                                     // delays
not #5ns n1 (ndata, data);
bufif1 #(1:2:3, 4:6:8, 5:10:12) b2 (io2, io1, dir);


// Section 29.1: Disable

// Using disable to break a loop externally:
initial
  begin : Clockgen
    Clock = 0;
    forever
      #(Period/2) Clock = ~Clock;
  end : Clockgen

initial
  begin : Stimulus
    ...
    disable Clockgen;
  end : Stimulus // Stops the clock


// Section 29.2: Disable

// Using disable fork to terminate spawned processes.
initial
fork             // Spawns two processes by calling two tasks in parallel
  a_task;
  another_task;
join_any         // Blocks until first process completes
disable fork;    // Terminates the other process

  
// Section 30.1: Do-While

int N = 10;
do
  begin
    ...
    N++;
  end
while (N < 100);


// Section 31.1: Dynamic Array

logic [7:0] array [];            // Declare a dynamic array
array = new[100];                // Create an array of100 elements
array = new[200](array);         // Double the size, preserving the existing elements
$display("array has %d elements", array.size());
array.delete();                  // Array now has no elements


// Section 32.1: Enum

// This example shows how some of the enumerated type methods are used.
enum States {Reset, Go1, Go2} State;

initial begin
  $display("The enum States has %0d values: ", State.num);
  State = State.first();
  do begin
    $display("  %s (%0d)", State.name, State);
    State = State.next;
  end while (State != State.first); // next() wraps at the end
end


// Section 33.1: Event

event StartClock, StopClock;

always
fork
  begin : ClockGenerator
    Clock = 0;
    @StartClock forever
      #HalfPeriod Clock = !Clock;
  end
  @StopClock disable ClockGenerator;
join

initial
begin : stimulus
  ...
  -> StartClock;
  ...
  -> StopClock;
  ...
  -> StartClock;
  ...
  -> StopClock;
end


// Section 34.1: Export

package P;
  int a, b;
endpackage : P

package Q;
  export P::*;  // export *::* also ok
  import P::*;
  int c;
endpackage : Q

module m;
  import Q::*; // P::a, P::b and Q::c are all potentially visible


// Section 35.1: Export "DPI-C"
  
// SystemVerilog - Exported DPI Function:
module Bus(input In1, output Out1);
  export "DPI-C" function read;
  // This SystemVerilog function can be called from C
  function void read(int data);
    ...
  endfunction
  ...
endmodule


// Section 35.2: Export "DPI-C"

// C:
#include "svdpi.h"
extern void read(int);   // Imported from SystemVerilog


// Section 36.1: Expression

A + B
!A
(A && B) || C
A[7:0]
B[1]
-4'd12/3               // A large positive number
"Hello" != "Goodbye"   // This is true (1)
$realtobits(r);        // System function call
{A, B, C[1:6]}	         // Concatenation (8 bits)
1:2:3                  // MinTypMax


// Section 36.2: Expression

logic [7:0] Byte7_to_0;
logic [0:7] Byte0_to_7;
Byte7_to_0[2 +: 3]                   // Same as Byte7_to_0[4:2]
Byte0_to_7[2 +: 3]                   // Same as Byte0_to_7[2:4]
Byte7_to_0[6 -: 3]                   // Same as Byte7_to_0[6:4]
Byte0_to_7[6 -: 3]                   // Same as Byte0_to_7[4:6]

input [4:0] shift;
input [31:0] operand;
output [7:0] result;
assign result = operand[shift -: 8];


// Section 36.3: Expression

// Multi-Dimensional Arrays
wire [7:0] A [0:15] [0:15];          // 16x16 array of bytes
assign A[0][0] = 8'b1;               // Element select
assign A[1][5][7:4] = A[5][1][3:0];  // Part-select 
assign W = A[1][2][3];               // Bit-select


// Section 37.1: Extends

class ParentClass;
  int X = 1;
  function int AFunc();
    AFunc = X - 1;
  endfunction
endclass

class ExtendedClass extends ParentClass;
  int X = 2;             // Overridden variable 
  function int AFunc();  // Overridden method
    get = X + 1;
  endfunction
endclass

ExtendedClass EP = new;
ParentClass P = EP;  // Overridden members of ExtendedClass are hidden

Y = P.X;             // Y = 1, not 2
Y = P.AFunc();       // Y = 0, not 3 or 1


// Section 37.1: Extern

// Extern in classes
class AClass;
  // Extern declaration
  extern protected virtual function int AFunc(int x);
endclass

function int AClass::AFunc(int x);
// Removed protected, virtual, added AClass::
// The rest of the declaration matches exactly the prototype
  ...  // Method body
endfunction

class PClass #(type T = int);
  extern function T PFunc(int x);
endclass

function PClass::T PClass::PFunc(int x);  // parameterized
  ...
endfunction


// Section 37.2: Extern

// Extern in Interfaces
interface circbuff_if;
  extern function read (int data);
  extern function write (int data);
endinterface: circbuff_if

module circbuff #(parameter int size)( circbuff_if Interf); 
  function void Interf.write(int data);
    ...
  endfunction
endmodule  


// Section 38.1: Final

final begin
  $display("Simulation ended: %0d errors.", error_count);
end


// Section 39.1: For

V = 0;
for (int I = 0, int J = 3; I < 4; I++, J--)
begin
  F[I] = A[I] & B[J];        // 4 separate and gates
  V = V ^ A[I];              // 4 cascaded xor gates
end


// Section 40.1: Force

force f = a && b;
...
release f;


// Section 41.1: Foreach

string Letters[4] = '{"a", "b", "c", "d"};
foreach(Letters[i])
  $display("Letters[%0d] = %s", i, Letters[i]);

int Mult [0:3][0:7];
foreach (Mult[i,j])
  Mult[i][j] = i * j;    // Initialise

  
// Section 42.1: Forever
  
initial
begin : Clocking
  Clock = 0;
  forever
    #10 Clock = !Clock;
end

initial
begin : Stimulus
  ...
  disable Clocking;         // Stops the clock
end


// Section 43.1: Fork

initial
fork : stimulus
  #20 Data = 8'hae;
  #40 Data = 8'hxx;  // This is executed last
  Reset = 0;         // This is executed first
  #10 Reset = 1;
join                 // Completes at time 40


// Section 43.2: Fork

initial
fork
  first_process;
  second_process;
  wait(interrupt);
join_any             // Completes when either process completes, or
                     // an interrupt occurs

					 
// Section 43.3: Fork

initial
  for(int j = 0; j <= 3; j++)
    fork
      automatic int k = j;
      process1: begin ... end
      process2: begin ... end
      ...
    join_none

	
// Section 44.1: Forkjoin

interface bus #(parameter N = 0) (input logic clock);
  extern forkjoin
    task slave_write(bit[7:0] Addr, bit[7:0] Data);
  extern forkjoin task slave_read(bit[7:0] Addr);
  modport slave_if (export task slave_write(bit[7:0] Addr, 
                      bit[7:0] Data),
                    export task slave_read(bit[7:0] Addr));
  ...
endinterface

module mem (bus busport);
  task busport.slave_write(bit[7:0] Addr, bit[7:0] Data);
   ...
  endtask
  ...
endmodule


// Section 45.1: Function

function [7:0] ReverseBits;
  input [7:0] Byte;
  integer i;
    for (i = 0; i < 8; i = i + 1)
      ReverseBits[7-i] = Byte[i];
endfunction


// Section 45.2: Function

function [15:0][7:0] AFunc(
  int A,                            // A is input by default
  output [15:0][7:0] B, C[15:0]); 
  ...
endfunction


// Section 45.3: Function

function automatic integer fibonacci (input integer n);
  if (n <= 2)
    fibonacci = 1;
  else
    fibonacci = fibonacci(n-1) + fibonacci(n-2);
endfunction


// Section 45.4: Function

module decoder (A, Y);
  parameter NumOuts = 16;
  localparam NumIns = BitsToFit (NumOuts); 
  input [NumIns-1:0] A;
  function integer BitsToFit(integer n);
    ...                            // Depends only on constants
  endfunction
  ...
endmodule


// Section 48.1: Generate

module TriStateSelector #(parameter N = 4)
  (input [N-1:0] D, E,
   output Y);
  
  generate
    genvar I;
    for (I=0; I<N; I=I+1) begin: B
      assign Y = E[I] ? D[I] : 1'bz;
    end
  endgenerate
endmodule


// Section 48.2: Generate

module FF #(parameter ClkPolarity = 1)
  (input Clk, D, output logic Q);

  if (ClkPolarity)                     // generate is not needed
    always @(posedge Clk) 
      Q <= D;
  else
    always @(negedge Clk) 
      Q <= D;
endmodule


// Section 49.1: If

if (C1 && C2)
begin
  V = !V;
  W = 0;
  if (!C3)
    X = A;
  else if (!C4)
    X = B;
  else
    X = C;
end


// Section 50.1: Implements

interface class IF1;
  pure virtual function void f();
endclass

class C implements IF1;
  virtual function void f();
  endfunction
endclass;

class D extends C;
endclass


// Section 51.1: Import

import MyPackage::*;
import MyOtherPackage::AName;

package P;
  typedef enum {ON, OFF} stateT;
endpackage : P

module M       
  import P::*;                      // imports stateT, and its literals
 (input logic Clock, input logic Reset, output logic O,
  output stateT s);


// Section 52.1: Import "DPI-C"

// SystemVerilog - Imported DPI Function:
module Bus();
  import "DPI-C" function void slave_write(input int data);
  function void write(int data);
    // Call C function
    slave_write(data); 
  endfunction
  ...
endmodule


// Section 52.2: Import "DPI-C"

// C:
#include "svdpi.h"
void slave_write (const int I2)
{...}


// Section 53.1: Initial

// Generate vectors in a testbench
logic Clock, Enable, Load, Reset;
logic [7:0] Data;
parameter HalfPeriod = 5;

initial
begin : ClockGenerator
  Clock = 0;
  forever
    #(HalfPeriod) Clock = !Clock;
end

initial
begin
       Load = 0;
       Enable = 0;
       Reset = 0;
  #20  Reset = 1;
  #100 Enable = 1;
  #100 Data = 8'haa;
       Load = 1;
  #10  Load = 0;
  #500 disable ClockGenerator;   // Stops clock generator
end


// Section 54.1: Inside

// Given
logic IsAMember;
logic [1:0] a;
IsAMember = a inside {2'b01, 2'b10};

// then
a = 2'b00                      // Result = 1'b0
a = 2'b01                      // Result = 1'b1
a = 2'b10                      // Result = 1'b1
a = 2'b11                      // Result = 1'b0
a = 2'b0x                      // Result = 1'bx
a = 2'b1x                      // Result = 1'bx
a = 2'bz0                      // Result = 1'bx
a = 2'bz1                      // Result = 1'bx


// Section 54.2: Inside

a inside {2'b?1};              // Matches 2'b01, 2'b11, 2'x1, 2'bz1


// Section 54.3: Inside

int array [$] = '{c, d};
if ( V inside {a, b, array})   // Equiv. to {a, b, c, d}
  ...

  
// Section 54.4: Inside

a inside {[0:5], [8:15]};


// Section 54.5: Inside

string I;
I inside {["abc":"def"]}       // I between "abc" and "def"


// Section 55.1: Instantiation

// UDP instance
Nand2 (weak1,pull0) #(3,4) (F, A, B);


// Section 55.2: Instantiation

//Module instance
Counter U123 (.Clock(Clk), .Reset(Rst), .Count(Q));


// Section 55.3: Instantiation

//In the two following examples, the port QB is unconnected
DFF Ff1 (.Clk(Clk), .D(D), .Q(Q), .QB());
// Equivalent to
DFF Ff1 (.Clk, .D, .Q, .QB());
// or
DFF Ff1 (.*, .QB());
DFF Ff2 (Q,, Clk, D);


// Section 55.4: Instantiation

//The following is an and-nor, showing an expression in port connection list
nor (F, A&&B, C)		// Not recommended


// Section 55.5: Instantiation

//The following example shows an array of instances
module Tristate8 (out, in, ena);
  output [7:0] out;
  input [7:0] in;
  input ena;

  bufif1 U1[7:0] (out, in, ena);

/* Equivalent (except the instance names) to ...
  bufif1 U1_7 (out[7], in[7], ena);
  bufif1 U1_6 (out[6], in[6], ena);
  bufif1 U1_5 (out[5], in[5], ena);
  bufif1 U1_4 (out[4], in[4], ena);
  bufif1 U1_3 (out[3], in[3], ena);
  bufif1 U1_2 (out[2], in[2], ena);
  bufif1 U1_1 (out[1], in[1], ena);
  bufif1 U1_0 (out[0], in[0], ena);
*/
endmodule


// Section 56.1: Interconnect

package nettype_pkg;
  nettype real realnet;
endpackage

module top();
  interconnect [0:1] iBus;
  LDriver L1(iBus[0]);
  RDriver R1(iBus[1]);
  RLMod   m1(iBus);
endmodule : top

module LDriver(output wire logic out);
endmodule : LDriver

module RDriver(output nettype_pkg::realnet out);
endmodule : RDriver

module RLMod(input interconnect [0:1] iBus);
  LDriver L1(iBus[0]);
  RDriver R1(iBus[1]);
endmodule : RLMod


// Section 57.1: Interface

// Using named bundle:
interface FPGAtoDSPInt;               // Interface definition
  logic Start, N_Reset;
  logic N_CS, N_DS, R_NW;
  logic [7:0] AddrBus, DataBus;
  ...
endinterface: FPGAtoDSPInt

module FPGA (FPGAtoDSPInt Interf, input logic Clk);
  ...
endmodule

module DSP (FPGAtoDSPInt Interf, input logic Clk);
  ...
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Interf();
  FPGA FPGAMod(Interf, Clk);          // Positional connection
  DSP DSPMod(.Interf(Interf), .Clk)); // Named and .name 
/* or
  FPGA FPGAMod (.*);              // Implicit port connections
  DSP DSPMod (.*); 
*/
endmodule


// Section 57.2: Interface

// Using generic interface:
module FPGA1 (interface Interf, input logic Clk);
  ...
endmodule

module DSP1(interface Interf, input logic Clk);
  ...
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf();            // Instantiate the interface
  FPGA1 FPGAMod(.Interf(Intf), .Clk(Clk));
  DSP1 DSPMod(.*, .Interf(Intf)); // Partial implicit port connection
endmodule


// Section 57.3: Interface

// Interface ports, tasks in interfaces:
interface FPGAtoDSPInt (input logic Clk); 
  logic Start, Int_Sig;
  ...
  task AddrGen;
    ...
  endtask: AddrGen
endinterface: FPGAtoDSPInt

module FPGA(FPGAtoDSPInt Interf); 
  ...  
always @(Interf.Start)
  Interf.AddrGen;  
  ...
  always @(posedge Interf.clk)
    Interf.Addr[0] <= Int_Sig; 
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf(Clk);             // Instantiate the interface
  FPGA FPGAMod(.Interf(Intf));        // Has access to AddrGen
  ...
endmodule


// Section 57.4: Interface

// Multiple tasks exports using forkjoin:
interface FPGAtoDSPInt (input logic clk); 
  ...
  // Tasks executed concurrently as a fork-join block
  extern forkjoin task do_Reg( );
  extern forkjoin task AddrGen(input logic[7:0] Addr);
  modport Slave( ...,
                export task AddrGen()); // Export from module
                                        // using modport
  modport Master(...,
               import task AddrGen(input logic[7:0] Addr));
                          // Import requires the full task prototype
  initial  do_Reg;
endinterface: FPGAtoDSPInt;

module FPGA(interface GI);
  task GI.do_Reg;
  ...
  endtask
  task GI.AddrGen;
    ...
  endtask
endmodule

module DSP(interface GI);
  logic [7:0] Addr;
  always @(posedge GI.Clk)
    GI.AddrGen(Addr);         // Call slave method via the interface
  ...
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf(Clk); 
  FPGA FPGAMod1(Intf.Slave);  // Exports do_Reg and AddrGen task
  FPGA FPGAMod2(Intf.Slave);  // Exports do_Reg and AddrGen task  
  DSP DSPMod(Intf.Master);    // Imports AddrGen task
endmodule


// Section 57.5: Interface

// Using parameters in interfaces:
interface FPGAtoDSPInt #(AddrWidth = 8, DWidth = 8) (input logic Clk); 
  ...
  logic [AddrWidth-1:0] addr;
  logic [DWidth-1:0] data;
  modport Slave( ...,
                import task AddrGen()); 
  modport Master(...,
     import task DInGen(input logic[DWidth-1:0] DIn));

  task DInGen(input logic[DWidth-1:0] DIn));
    ...
  endtask
  task AddrGen;
    ...
  endtask
endinterface: FPGAtoDSPInt

module FPGA(interface GI); 
  ...  
  if (GI.Start == 0)
    GI.AddrGen;
  ...
endmodule

module DSP(interface GI);
  logic [7:0] DIn;
  always @(posedge GI.Clk)
      GI.DInGen(DIn); 
  ...
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf(Clk);     // Instantiate default interface
  FPGAtoDSPInt #(.DWidth(16)) DIntf(clk);  // Changed data bus width
  FPGA FPGAMod(Intf.Slave);   // Access only to AddrGen task
  DSP DSPMod(Intf.Master);    // Access only to DInGen task
  DSP DSPMod1(DIntf.Master);  // 16-bit wide data bus
endmodule


// Section 58.1: Interface Class

interface class IF1;
  pure virtual function void f();
endclass

interface class IF2;
  pure virtual function void g();
endclass

interface class IF3 extends IF2;
  pure virtual function int h();
endclass

class C;
  function bit i();
  ...
  endfunction
endclass

class D extends C implements IF1, IF3;
  virtual function void f();
  ...
  endfunction

  virtual function void g();
  ...
  endfunction

  virtual function int h();
  ...
  endfunction

  function bit i();
  ...
  endfunction
endclass


// Section 61.1: Let

package p;
  let aTimesB (int a, int b) = 
              ($bits(a) + $bits(b))'(a * b);
endpackage

module m;
  import p::*;
  int a, b;
  initial begin
     a = 2; b = 3;
     $display( aTimesB(.a(a), .b(b)) );  // 6
  end
endmodule


// Section 61.2: Let

module n;
  logic clock, j;
  let Rose(e, j) = $rose(j, @(e));
  ...
  always ...
    if ( Rose( posedge clock, j) ) // event argument
      ... 
  ...
endmodule


// Section 62.1: Library

// All *.v in the directory ../primitives belong to library MyGates
library MyGates
  ../primitives/.v ;

  
// Section 62.2: Library
  
// References any .v source in a project hierarchy, regardless of the directory
// names or structure within it.
// (uncomment the following to use)
// library ProjectLib /usr/design/project/.../*.v ;


// Section 62.3: Library

// All *.v in this directory and in ../archives belong to library MyDesign
// (uncomment the following to use)
// library MyDesign
//   ./*.v,  // equivalently *.v,
//   ../archives/*.v ;


// Section 63.1: Local

class AClass;
  local int i;
  function int AFunc (AClass A);
    AFunc = this.i + A.i; // A.i is a local property referenced outside 
                          // its instance, but within the same class
  endfunction
endclass


// Section 64.1: Localparam

module Decoder (A, Y);
  parameter NumIns = 3;
  localparam NumOuts = 2 ** NumIns;
  input [NumIns -1 : 0] A;
  output[NumOuts-1 : 0] Y;
...


// Section 65.1: Mailbox

mailbox mbox = new;
string message;

mbox.put("This is a message");
mbox.get(message);  // Message now contains "This is a message"


// Section 66.1: Matches

typedef union tagged packed {
  void Invalid;
  int Valid;
} VInt;

VInt v;
int j;

//Pattern-matching case statement:
case (v) matches
  tagged Invalid  : $display("v's value is invalid");
  tagged Valid .n : $display("v is valid: value is %d", n);
endcase

//Pattern-matching if statement:
if (v matches tagged Invalid)
  $display("v's value is invalid");
else if (v matches tagged Valid .n &&& n < 0)
  $display("v is valid, and negative");

// Pattern-matching conditional operator:
j = v matches tagged Valid .n ? n : 'x;


// Section 67.1: Modports

interface FPGAtoDSPInt;
  logic Start, N_Reset;
  logic N_CS, N_DS, R_NW;
  logic [7:0] AddrBus, DataBus;
  modport Master(output AddrBus, ref DataBus);
  modport Slave (input  AddrBus, ref DataBus);
  ...
endinterface: FPGAtoDSPInt

module FPGA (FPGAtoDSPInt.Master Interf, input logic Clk);  // Modport specified in module header
  ...
endmodule

module DSP (FPGAtoDSPInt Interf, input logic Clk);
  ...
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf;
  FPGA FPGAMod(.Interf(Intf), Clk);
  DSP DSPMod(.Interf(Intf.Slave), .Clk(Clk));  // Modport specified in port connection
endmodule


// Section 67.2: Modports

// Hierarchical interface:
interface Intf;
  interface FPGAtoDSPInt;
    ...
    modport Master(...);
    modport Slave (...);
    ...
  endinterface: FPGAtoDSPInt
  FPGAtoDSPInt Intf1, Intf2;
  modport Master2 (Intf1.Master, Intf2.Master);
endinterface


// Section 67.3: Modports

// Generic Interface:
module FPGA(interface Interf);
  ...
endmodule

module DUT;
  FPGAtoDSPInt Intf;
  FPGA FPGAMod(Intf.Slave);  // Connect modport to module instance
 ...
endmodule


// Section 67.4: Modports

// Tasks in modports:
interface FPGAtoDSPInt (input logic Clk); 
  ...
  logic [7:0] AddrBus, DataBus;
  modport Slave( ...);
  modport Master(...,
     import task DInGen(input logic[7:0] DIn));
  task DInGen(input logic[7:0] DIn));
    ...
  endtask
endinterface: FPGAtoDSPInt

module FPGA(interface GI);   // Generic Interface
  ...  
endmodule

module DSP(interface GI);
  logic [7:0] DIn;
  always @(posedge GI.Clk)
    GI.DInGen(DIn); 
  ...
endmodule
 
module DUT;
  logic Clk;
  FPGAtoDSPInt Intf(Clk);    // Instantiate default interface
  FPGA FPGAMod(Intf);        // Access to all Master and Slave tasks
  DSP DSPMod(Intf.Master);   // Access only to DInGen task
endmodule


// Section 67.5: Modports

// Exporting tasks:
interface FPGAtoDSPInt (input logic Clk); 
  ...
  modport Slave(...,
                export task DInGen(input logic[7:0] DIn));
                         // Export from module that uses the modport

  modport Master(...,
                import task DInGen(input logic[7:0] DIn));
endinterface: FPGAtoDSPInt

module FPGA(interface Interf); 
  task Interf.DInGen(input logic[7:0] DIn); // DInGen method
    ...
  endtask
endmodule

module DSP(interface GI);
  logic [7:0] DIn;
  always @(posedge GI.Clk)
    GI.DInGen(DIn);         // Call slave method via the interface
endmodule

module DUT;
  logic Clk;
  FPGAtoDSPInt Intf(Clk); 
  FPGA FPGAMod(Intf.Slave); // Exports DInGen task
  DSP DSPMod(Intf.Master);  // Imports DInGen task
endmodule


// Section 67.6: Modports

// Clocking blocks and modports
interface An_Interf(input bit clk);
  wire a, b;
  clocking CB @(posedge clk);
    input a;
    output b;
    ...
  endclocking
 
  modport CTB (clocking CB); // Synchronous testbench modport
  modport TB ( input a, output b);  // Asynchronous tb modport
endinterface

module T (An_Interf.CTB T1); // Testbench with synchronous port
  initial begin
    T1.CB.b <= 1;
    ...
  end
endmodule


// Section 67.7: Modports

// Modport Expressions
interface I;
  logic [7:0] r;
  const int x=1;
  bit R;
  modport A (output .P(r[3:0]), input .Q(x), R);
  modport B (output .P(r[7:4]), input .Q(2), R);
endinterface

module M ( interface i);
  initial i.P = i.Q;
endmodule

module top;
  I i1();
  M u1 (i1.A);
  M u2 (i1.B);
endmodule


// Section 68.1: Module

macromodule nand2 (f, a, b);
  output f;
  input a, b;

  nand (f, a, b);
endmodule


// Section 68.2: Module

module PYTHAGORAS (X, Y, Z);
  input  [63:0] X, Y;
  output [63:0] Z;

  parameter Epsilon = 1.0E-6;
  real RX, RY, X2Y2, A, B;

  always @(X or Y)
  begin
    RX = $bitstoreal(X);
    RY = $bitstoreal(Y);
    X2Y2 = (RX * RX) + (RY * RY);
    B = X2Y2;
    A = 0.0;
    while ((A - B) > Epsilon || (A - B) < -Epsilon)
    begin
      A = B;
      B = (A + X2Y2 / A) / 2.0;
    end
  end
  assign Z = $realtobits(A);
endmodule


// Section 68.3: Module

module MinMax #(parameter P) (
  input MinMax1,              // ANSI-style port declaration
  input [3:0] X, Y,
  output logic [3:0] Z);
  ...
endmodule


// Section 68.4: Module

// Nested modules
module Mod2(...);
  module and2(input I1, I2, output O);
    ...
  endmodule
  ...
  and2 U1(...), U2(...), U3(...);
  ...
endmodule


// Section 68.5: Module

// Extern module
// Given
extern module Counter #(N = 8)
                      (input Clock, Reset,
                       output logic [N-1:0] Count);

module Counter (.*);

// is equivalent to
module Counter #(N = 8) (input Clock, Reset,
                         output logic [N-1:0] Count);
  ...
endmodule


// Section 69.1: Name

// Legal names
A_99_Z
Reset
_54MHz_Clock$
Module                 // Not the same as 'module'
\$%^&*()               // Escaped identifier


// Section 69.2: Name

// Illegal names
123a                   // Starts with a number
$data                  // Starts with a dollar
module                 // A keyword


// Section 69.3: Name

// Hierarchical names, and an upwards name reference.
module Separate;
  parameter P = 5;     // Separate.P or $root.Separate.P
endmodule

module Top;
  logic R;             // Top.R or $root.Top.R
  Bottom U1();
endmodule

module Bottom;
  logic R;             // Top.U1.R or $root.Top.U1.R 

  task T;              // Top.U1.T or $root.Top.U1.T 
    logic R;           // Top.U1.T.R or $root.Top.U1.T.R
    ...
  endtask

  initial
  begin : InitialBlock
    logic R;             // $root.Top.U1.InitialBlock.R
    $display(Bottom.R);  // Upwards name reference to Top.U1.R
    $display(U1.R);      // Upwards name reference to Top.U1.R
    ...
  end
endmodule


// Section 70.1: Net

wire Clock;
wire [7:0] Address;
wire enum {red, green, blue} light;
tri1 [31:0] Data, Bus;
trireg (large) C1, C2;
wire f = a && b,
     g = a || b;           // Continuous assignments

	 
// Section 71.1: Nettype

typedef struct {
	int x;
	int y;
	real r;
} R;

function automatic R RAvg(input R driver[]);
  RAvg = '{x:0, y:0, r:0.0};

  foreach (driver[i]) begin
    ...
  end
  ...
endfunction

nettype R wRAvg with RAvg;


// Section 72.1: New

class C;
  bit [3:0] size;

  covergroup cov_size;
    coverpoint size;
  endgroup

  function new(input j = 0);    // Class constructor
    size = j;
    cov_size = new;             // Covergroup instance
  endfunction
endclass

C c1, c2, c3;
C c4 = new;                     // Declare and initialize

initial begin
  c1 = new;                     // Size = 0
  c2 = new(10);                 // Size = 10
  c3 = new c2;                  // Size = 10
  ...
  repeat (20) begin
    c2.size = $urandom_range(0, 15);
    c2.cov_size.sample();
  end
  ...
end


// Section 72.2: New

// Dynamic arrays
string Names[] = new[20];       // 20 elements

Names = new[40] (Names);        // Expand to 40 elements;
                                // preserviing the first 20
                                // elements.

Names = new[30];                // Resize to 30 elements.
                                // Initialize all elements to
                                // default value of the
                                // element datatype.


// Section 73.1: Number

-253               // A signed decimal number
'Haf               // An unsized hex number
6'o67              // A 6 bit octal number
8'bx               // An 8 bit unknown number (8'bxxxx_xxxx)
4'bz1              // All but the lsb are Z (4'bzzz1)
reg signed [3:0] S4;
S4 = -4;           // 4'b1100
S4 = S4 >>> 1;     // 4'b1110 = -2
S4 = S4 + 2'sb11;  // 4'b1101 = -3


// Section 73.2: Number

// Broken backward compatibility
reg [63:0] W64;
W64 = 64'bz;       // Verilog-1995: 64'h00000000zzzzzzzz
W64 = 'bz;         // Verilog-2001: 64'hzzzzzzzzzzzzzzzz


// Section 73.3: Number

// Illegal numbers for the reasons given:
_23                // Begins with _
8' HF F	            // Contains two illegal spaces
0ae                // Decimal number with hex digits
x                  // A name, not a number (use 1'bx)
.17                // Should be 0.17


// Section 74.1: Operators

-16'd10                    // An expression, not a signed number!
a + b
x % y
Reset && !Enable           // Same as Reset && (!Enable)
a && b || c && d           // Same as (a && b) || (c && d)
~4'b1101                   // Gives 4'b0010
&8'hff                     // Gives 1'b1 (all bits are 1)
reg signed [3:0] ShftIn, ShftOut;
ShftIn = 4'b1010;
ShftOut = (ShftIn >>> 2);  // ShftOut becomes 4'b1110


// Section 74.2: Operators

// Assignment to RegA when an event occurs on A or B
@(A, B) RegA = RegB;


// Section 74.3: Operators

// Or and , in sensitivity list
always @(A or B, C, D or E)


// Section 74.4: Operators

// Replication operator (or multiple concatenation)
{4{1'b1}}                  // Equivalent to 4'b1111 


// Section 74.5: Operators

// Class scope resolution operator
class BaseClass;
  int x;
  static task ATask(int i, int j);
   ... 
  endtask
endclass
...
BaseClass B = new;
int x = 1;
B.ATask(BaseClass::x, x); // BaseClass::x and x are different


// Section 74.6: Operators

// Pack/unpack streaming operations
int x, y, z;
logic [3:0] v [2:0];
logic [4:1] w1, w2, w3;
bit [96:1] a = {>>{x, y, z}};    // Pack x, y, z, each 32 bits
bit [100:0] c = {>>{ x, y, z }}; // c is padded with 5 bits
{>>{x, y, z}} = 96'b111;         // Unpack x = 0, y = 0, z = 7
{>>{w1, w2, w3}} = v;            // w1 = v[2], w2 = v[1], w3 = v[0]
int b = {>>{x, y, z}};           // Error: b is 32 bits < 96 bits


// Section 75.1: Package

package P0;
  int a;
  const bit c = 0;
endpackage: P0

package P1;
  int b;
  const bit c = 0;
endpackage: P1

module Mod;
  import P0::*;
  wire w1 = P1::b; // no need for import clause
  wire w2 = c;     // The import of P0::c is forced
  import P1::c;    // Error: conflict between P0::c and P1::c
endmodule


// Section 76.1: Parameter

module Shifter #(NBits = 8)     // Keyword parameter is omitted
  (input Clock, In, Load,
   input [NBits-1:0] Data,
   output Out);

  always @(posedge Clock)
    if (Load)
      ShiftReg <= Data;
    else
      ShiftReg <= {ShiftReg[NBits-2:0], In}

  assign Out = ShiftReg[NBits-1];

endmodule

module TestShifter;
  ...

  defparam U2.NBits = 10;

  Shifter #(16) U1 (...);            // 16-bit shift register
  Shifter U2 (...)                   // 10-bit shift register
endmodule


// Section 76.2: Parameter

// Sized parameters
parameter [2:0] Idle = 3'b100, Go1 = 3'b010, Go2 = 3'b001;


// Section 76.3: Parameter

// Typed parameters
parameter integer Size = 1;


// Section 76.4: Parameter

// Named association of parameters
module UseShifter(...);
  Shifter #(.Nbits(10)) MyDecadeShifter(...);


// Section 76.5: Parameter

// Parameter dependence
parameter WordSize = 16, MemSize = WordSize*1024;


// Section 76.6: Parameter

// Type Parameter
module M1 #(int BitNo = 7, 
            localparam P = BitNo*4, // P depends on BitNo
            parameter type ParType = shortreal) 
           (input bit [BitNo:0] In,
            output bit [BitNo:0] Out);
			
  ParType P = 0; // Type of P is set by ParType parameter
                 //(shortreal unless redefined)
  ...
endmodule

module M2;
  bit [15:0] In, Out;
  M1 #(.BitNo(15), .ParType(real)) U1 (In, Out);  
                 // ParType redefined as real
endmodule


// Section 77.1: PATHPULSE$

specify
  (clk => q) = 1.2;
  (rst => q) = 0.8;
  specparam PATHPULSE$clk$q = (0.5,1),
            PATHPULSE$ = (0.5);
endspecify


// Section 78.1: Port

module (A, B, C, D);
  input A;
  inout [7:0] B;
  output [3:0] C, D;


// Section 78.2: Port

module FF8(
  input Clk, Reset,
  input reg [7:0] D,
  output reg [7:0] Q = 8'b0); // Declare and initialize reg


// Section 78.3: Port

typedef struct {
  bit A;
  union {int i, real j} B;
} Struct1; 

module M1 (input int In, output var Struct1 Out); 
  ...
endmodule


// Section 78.4: Port

// Interface ports
interface Interf (input Clk);
  ...
endinterface

module (Interf Int1, ...)
  ...
endmodule

module (interface Int2, ...)   // Generic interface
  ...
endmodule



// Section 79.1: Priority

bit[1:0] S;

priority if(S[1:0] == 2'b01) 
  State = State1;
else 
  if (S[1:0] == 2'b10) 
    State = State2;
  else 
      State = Idle;     // Covers all other possible values, so no
                        // warning is issued


// Section 79.2: Priority

priority casez(S)
  2'b01:   State = State1;
  2'b10:   State = State2;
  default: State = Idle;
endcase


// Section 80.1: Procedural Assignment

always @(Inputs)
begin : CountOnes
  integer I;
  f = 0;
  for (I=0; I<8; I=I+1)
    if (Inputs[I])
      f = f + 1;
end


// Section 80.2: Procedural Assignment

always @Swap
fork           // Swap the values of a and b
  a = #5 b;
  b = #5 a;
join           // Completes after a delay of 5


// Section 80.3: Procedural Assignment

always @(posedge Clock)
begin
  c <= b;      // Uses the 'old' value of 'b'
  b <= a;
end


// Section 80.4: Procedural Assignment

// Delay a nonblocking assignment to overcome clock skew.
always @(posedge Clock)
  Count <= #1 Count + 1;


// Section 80.5: Procedural Assignment

// Assert Reset for one clock period on the fifth negative edge of Clock.
initial
begin
  Reset = repeat(5) @(negedge Clock) 1;
  Reset = @(negedge Clock) 0;
end


// Section 81.1: Process

initial
  begin
    // Declare a process variable
    process p;
    // Spawn a process
    fork
      begin
        // Obtain process's handle
        p = process::self();
        ...
      end
    join_none  // Nonblocking
    // If the process hasn't completed after 100ns, forcibly terminate it
    #100ns if (p != process::FINISHED) p.kill();
  end


// Section 82.1: Program

module Design (input clock, input [7:0] data, addr,
               output [7:0] Q);
  // ...
endmodule

module testbench;

  logic clock = 0;
  logic [7:0] data, addr, Q;

  Design DUT (.*);
  test test_i (.*);

  // Simulation stops when the program finishes
  initial forever #10 clock = !clock;

  program test (input clock, output logic [7:0] data, addr,
                input [7:0] Q);

    clocking cb @(posedge clock);
      default input #2ns output #5ns;
      output data, addr;
      input Q;
    endclocking

    initial
    begin
      cb.addr <= 8'h00;
      cb.data <= 8'haa;
      // ...
    end

  endprogram

endmodule


// Section 84.1: Protected

class BaseClass;
  virtual protected function int AFunc(bit X); // Prototype
  extern protected virtual function int BFunc(int Y);
endclass

class ExtendedClass extends BaseClass;
  protected function int AFunc(bit X);
    ... // Function body
  endfunction
endclass


// Section 85.1: Queue

int Q1[$];                      // An empty queue of ints
int Q2[$] = '{1, 2};            // An initialised queue of ints
bit Q3[$:7];                    // A queue with max size = 8 bits

int I1, e;
I1 = Q2[0];                     // Read the first (left-most) item
I1 = Q2[$];                     // Read the last (right-most) item
Q2 = Q2[0:$-1];                 // Delete the last (right-most) item
Q2 = Q2[1:$-1];                 // Delete the first and last items
Q.delete(i)                     // Equiv. to: Q = '{Q[0:i-1], Q[i+1,$]}
Q1 = Q2;                        // Copy Q2 in Q1
Q2 = '{Q2, 3};                  // Insert 3 at the end
Q2 = '{Q2[0:i-1], j, Q2[i,$] }; // Insert j at position i
Q2 = '{Q2[0:i], j, Q2[i+1,$] }; // Insert j after position i
e = Q.pop_front()               // Equiv. to: e = Q[0]; Q = Q[1,$]
e = Q.pop_back()                // Equiv. to: e = Q[$]; Q = Q[0,$-1]
Q.push_front(e)                 // Equiv. to: Q = '{e, Q}


// Section 86.1: Rand

// Random variables in classes
class C;
  rand bit a, b;
endclass

C c = new;

c.randomize();


// Section 86.2: Rand

// Seeding
class B;
  rand bit a;
  function new (int seed);
    this.srandom(seed);
    ...
  endfunction
  ...
endclass 

B b = new(8);            // Create b with seed = 8
b.srandom(10);           // Re-seed b with seed 10


// Section 86.3: Rand

// The scope randomize function ([std::]randomize)
bit a, b;                // Variables with module scope
bit OK;
OK = randomize(a, b);    // Make a, b random variables
OK = randomize(a, b) with {a != b;};


// Section 87.1: Randcase

bit a, b;
randcase         // self-determined precision of each weight expression
   a+b: x =  8;  // 1-bit precision
     5: x =  3;  // 3-bit precision (3'b101)
  4'h9: x = 10;  // 4-bit precision
                 // Weight selection: unsigned 4-bit sum comparison
endcase

  
// Section 88.1: Randsequence

// The following generates either ABC or ABD. The latter is twice as likely. 
randsequence
   S1 : A B S2;                         // Sequence starts here
   S2 : C | D := 2;
   A  : {$display("A");}
   B  : {$display("B");}
   C  : {$display("C");}
   D  : {$display("D");}
endsequence


// Section 88.2: Randsequence

randsequence(Top)
  Top : One Two Three Four;
  One : S11 | S12;
  // Sequence aborted after S21 if i < 2
  Two : S21 {if (i < 2) break;} S22;
  Three : case (j)
          0    : S31           // If j=0, S31 is generated
          1, 2 : S32           // If j=1 or 2, S32 is generated
          default : S33        // Otherwise, S33 is generated
        endcase ;
  // Repeat S4 a random no. of times in the range [1:3], depending on the
  // value returned by $urandom_range()
  Four : repeat($urandom_range(1, 3)) S4;
  S11 : {$display("S11");} ;
  S12 : {$display("S12");} ;
  S21 : {i--; $display("S21");} ;
  S22 : {i++; $display("S22");} ;
  ...
endsequence


// Section 88.3: Randsequence

// Sequence interleaving
randsequence(Top) 
  Top : rand join S1 S2;
   S1 : A B ;
   S2 : C D ;
   ...
endsequence  // Generates, for example: A B C D.


// Section 89.1: Repeat

initial
begin
  Clock = 0;
  repeat (MaxClockCycles)
  begin
    #10 Clock = 1;
    #10 Clock = 0;
  end
end


// Section 89.2: Repeat

repeat  (3) @(EventExpr) // Will execute EventExpr 3 times.
repeat (-3) @(EventExpr) // Will not execute EventExpression.
repeat  (a) @(EventExpr) // If a is assigned -3, will execute the
                         // EventExpr once if a declared unsigned.
                         // Will not execute if a is signed.


// Section 90.1: Semaphore

semaphore sm = new(2);  // Create semaphore with 2 keys
sm.get();               // Get a key, or block if none available
sm.put(2);              // Return two keys


// Section 91.1: Specify

module M (F, G, Q, Qb, W, A, B, D, V, Clk, Rst, X, Z);
  input A, B, D, Clk, Rst, X;
  input [7:0] V;
  output F, G, Q, Qb, Z;
  output [7:0] W;
  reg C, Err;
// Functional Description ...
  specify
    specparam TLH$Clk$Q    = 3,
              THL$Clk$Q    = 4,
              TLH$Clk$Qb   = 4,
              THL$Clk$Qb   = 5,
              Tsetup$Clk$D = 2.0,
              Thold$Clk$D  = 1.0;
// Simple path, full connection
    (A, B *> F) = (1.2:2.3:3.1, 1.4:2.0:3.2);
// Simple path, parallel connection, positive polarity
    (V + => W) = 3,4,5;
// Edge-sensitive paths, with polarity
    (posedge Clk *> (Q  +: D)) = (TLH$Clk$Q,THL$Clk$Q);
    (posedge Clk *> (Qb -: D)) = (TLH$Clk$Qb,THL$Clk$Qb);
// State dependent paths
    if (C) (X *> Z) = 5;
    if (!C && V == 8'hff) (X *> Z) = 4;
    ifnone (X *> Z) = 6;	// Default SDPD, X to Z
// Timing checks
    $setuphold(posedge Clk, D,
               Tsetup$Clk$D, Thold$Clk$D, Err);
  endspecify
endmodule


// Section 91.2: Specify

//Pulse-Style and showcancelled
specify
  showcancelled Out1, Out2;
  pulsestyle_ondetect Out1, Out2;
  (A => Out1)=(2,3);
  (B => Out1)=(3,4);
  (B => Out2)=(3,4);
  (B => Out2)=(5,6);
endspecify


// Section 92.1: Specparam

specify
  specparam tRise$a$f = 1.0,
            tFall$a$f = 1.0,
            tRise$b$f = 1.0,
            tFall$b$f = 1.0;
  (a *> f) = (tRise$a$f, tFall$a$f);
  (b *> f) = (tRise$b$f, tFall$b$f);
endspecify

module (input I1, I2, output O1);
  specparam Spec = 1.0;
  parameter Par = 1;
  ...
endmodule


// Section 93.1: Statement

LabelA: Statement
LabelB: begin
  ...
end


// Section 96.1: Strength

assign (weak1, weak0) f = a + b;
trireg (large) c1, c2;
and (strong1, weak0) u1 (x, y, z);


// Section 97.1: String

string s1;             // s1 is initially ""
string s2 = "This is a string literal. ";
string s3;

s1 = "So is this."
s2 = {s2,s1};          // s2 is now "This is a string literal. So is this."
s3.itoa(100);
$display(s3);          // "100"
$display(s1.len);      // Returns 11


// Section 98.1: String Literal

logic [23:0] MonthName[1:12];

initial
begin
  MonthName[1] =  "Jan";
  MonthName[2]  = "Feb";
  MonthName[3]  = "Mar";
  MonthName[4]  = "Apr";
  MonthName[5]  = "May";
  MonthName[6]  = "Jun";
  MonthName[7]  = "Jul";
  MonthName[8]  = "Aug";
  MonthName[9]  = "Sep";
  MonthName[10] = "Oct";
  MonthName[11] = "Nov";
  MonthName[12] = "Dec";
end


// Section 99.1: Struct

typedef struct {
  int A;
  union {bit i; byte j;} B;
} Struct1;                    // Named structure
Struct1 S[7:0];               // Array of structures


// Section 99.2: Struct

struct packed signed {
  int A;
  byte B;
  byte C;
} PackedStruct;               // Signed, 2-state


// Section 100.1: Super

class ParentClass;
  int X = 1;
  function int AFunc();
    AFunc = 2*X;
  endfunction
endclass

class DerivedClass extends ParentClass;
  int X = 2;                  // Overridden variable 
  function int AFunc();  
    AFunc = super.AFunc() + 2*X*super.X;
  endfunction
endclass


// Section 101.1: Task

// Simple RTL task, which can be synthesized.
task Counter;
  inout [3:0] Count;
  input Reset;
  if (Reset)         // Synchronous Reset
    Count = 0;       // Must use blocking, or value won't be seen
  else
    Count = Count + 1;
endtask


// Section 101.2: Task

// An automatic task
task automatic PipelinedMult(
  input [7:0] A, B,
  input integer Depth,
  output [15:0] Y
);                   // ANSI-style arguments
logic [15:0] temp;   // a distinct temp for each running instance of
                     // PipelinedMult due to automatic keyword
  begin
    temp = A * B;
    repeat (Depth)
      @(posedge clk)
    Y = temp;
  end
endtask


// Section 101.3: Task

// An automatic task with static variables
task automatic Task();
  int VarA1;            // Automatic by default
  static int VarS;      // Static
  automatic int VarA2;  // Automatic
    ...
endtask


// Section 101.4: Task

// Argument of type array
task ATask(input [15:0][7:0] A, B[15:0],
           output [15:0][7:0] C[1:0]);
  ...
endtask


// Section 101.5: Task

// Tasks in interfaces
interface A (input logic Clk); 
  logic Start;
  ...
  task Task1;
    ...
  endtask: Task1
endinterface: A
module Mod(A Interf); 
  ...  
always @(Interf.Start)
    Interf.Task1;  
endmodule
module DUT;
  logic Clk;
  A Intf(Clk);                  // Interface instantiation
  Mod U1(.Interf(Intf.Task1));  // Only has access to the 
                                // Task1 task
  ...
endmodule


// Section 101.6: Task

// Tasks in a testbench
module TestRAM;

  parameter AddrWidth = 5;
  parameter DataWidth = 8;
  parameter MaxAddr = 1 << AddrBits;

  reg [DataWidth-1:0] Addr;
  reg [AddrWidth-1:0] Data;
  wire [DataWidth-1:0] DataBus = Data;
  reg Ce, Read, Write;

  Ram32x8 Uut (.Ce(Ce), .Rd(Read), .Wr(Write),
               .Data(DataBus), .Addr(Addr));

  initial
  begin : stimulus
    integer NErrors;
    integer i;
    // Initialize the error count
    NErrors = 0;
    // Write the address value to each address
    for ( i=0; i<=MaxAddr; i=i+1 )
      WriteRam(i, i);
    // Read and compare
    for ( i=0; i<=MaxAddr; i=i+1 )
    begin
      ReadRam(i, Data);
      if ( Data !== i )
        RamError(i,i,Data);
    end
    // Summarise the number of errors
    $display(Completed with %0d errors, NErrors);
  end

  task WriteRam;
    input [AddrWidth-1:0] Address;
    input [DataWidth-1:0] RamData;
  
    Ce = 0;
    Addr = Address;
    Data = RamData;
    #10 Write = 1;
    #10 Write = 0;
    Ce = 1;
  endtask

  task ReadRam;
    input  [AddrWidth-1:0] Address;
    output [DataWidth-1:0] RamData;
 
    Ce = 0;
    Addr = Address;
    Data = RamData;
    Read = 1;
    #10 RamData = DataBus;
    Read = 0;
    Ce = 1;
  endtask

  task RamError;
    input [AddrWidth-1:0] Address;
    input [DataWidth-1:0] Expected;
    input [DataWidth-1:0] Actual;
    if ( Expected !== Actual )
    begin
      $display("Error reading address %h", Address);
      $display("  Actual %b, Expected %b", Actual, Expected);
      NErrors = NErrors + 1;
    end
  endtask
endmodule


// Section 102.1: Task Enable

task Counter;
  inout [3:0] Count;
  input Reset;
  ...
endtask

always @(posedge Clock)
  Counter(Count, Reset);

  
// Section 103.1: This
 
class AClass;
  int Var1;               // Var1 is a property of AClass
  function new (int Var1) // Var1 is an argument of the constructor
    this.Var1 = Var1;     // The instance property is accessed using this
  endfunction
endclass


// Section 104.1: Timeunit

timeunit 100ns;
timeprecision 10ps;


// Section 105.1: Timing Control

#10
#10ns
#(Period/2)
#(1.2:3.5:7.1)
@Trigger
@(a or b or c)
@(a, b, c)
@(*)
@(posedge clock or negedge reset)


// Section 105.2: Timing Control

// Delay a nonblocking assignment to overcome clock skew.
always @(posedge Clock)  
  Count <= #1 Count + 1;


// Section 105.3: Timing Control

// Assert Reset for one clock period on the fifth negative edge of Clock.
initial begin
  Reset = repeat(5) @(negedge Clock) 1;
  Reset = @(negedge Clock) 0;
end


// Section 106.1: Typedef

typedef enum {True, False} Bool;
Bool Var; 


// Section 106.2: Typedef

typedef struct {byte Addr; byte Data;} Bus; 
Bus Bus1[0:3];                     // Array of structures 


// Section 106.3: Typedef

typedef union { int X; shortreal Y; } FloatingPoint; 
FloatingPoint N;
N.Y = 0.0; 


// Section 106.4: Typedef

typedef mailbox #(int) MailBox; // Parameterised mailbox
MailBox MB = new;


// Section 107.1: Union

typedef union packed {
  bit [15:0] i;
  shortint   j;
} Un; 

Un N;
N.j = 0;
	

// Section 107.2: Union

typedef struct packed { // Unsigned by default
  bit [ 3:0]  A4;
  bit [ 7:0]  B8;
  bit [15:0] C16;
} Struct1;

typedef union packed {  // Unsigned by default
  Struct1 AStruct;
  bit [27:0]        A28;
  bit [13:0][1:0] A14_2;
} Union1;

Union1 U1;
byte B; 
bit [3:0] Nib;
B = U1.A28[27:26];      // Same as B = U1.A14_2[13];
Nib = U1.A28[27:24];    // Same as Nib = U1.Astruct.A4;


// Section 107.3: Union

typedef union tagged packed {
  void Invalid;
  int i;
} IntOrInvalid;


IntOrInvalid ti;

ti = tagged i 42;                   // Tagged union expression
ti.i = 10                           // OK - tag is "i"
if (ti.i == 10 ) ...                // True
ti = tagged Invalid;                // No value needed
if (ti.i == 10 ) ...                // Error - ti is "Invalid"


// Section 108.1: Unique

bit[1:0] S;

unique if(S[1:0] == 2'b01) 
  State = State1;
else if (S[1:0] == 2'b10) 
  State = State2;        // 2'b00 and 2'b11 cause a run-time warning

// Section 108.2: Unique
  
unique casez(S)
  2'b01: State = State1;
  2'b10: State = State2; // 2'b00 and 2'b11 cause a run-time warning
endcase


// Section 109.1: Unpacked Array Concatenation

int A[1:4] = '{1,2,3,45};     // assignment pattern
int B[4]   = {1,2,3,4};       // unpacked array concatenation
int C[1:8] = {A, 1,2,3,4};    // legal
int D[1:8] = '{A, 1,2,3,4};   // illegal
int E[1:8] = {default:0};     // illegal
int F[1:8] = '{default:0};    // legal


// Section 110.1: User Defined Primitive

primitive Mux2to1 (f, a, b, sel);   // Combinational UDP
  output f;
  input a, b, sel;

  table
//  a b sel : f
    0 ?  0  : 0;
    1 ?  0  : 1;
    ? 0  1  : 0;
    ? 1  1  : 1;
    0 0  ?  : 0;
    1 1  ?  : 1;
  endtable

endprimitive


// Section 110.2: User Defined Primitive

primitive Latch (Q, D, Ena);
  output Q;
  input D, Ena;

  reg Q;                             // Level sensitive UDP

  table
//  D Ena : old Q : Q
    0 0   :   ?   : 0;
    1 0   :   ?   : 1;
    ? 1   :   ?   : -;               // Keeps previous value
    0 ?   :   0   : 0;
    1 ?   :   1   : 1;
  endtable

endprimitive


// Section 110.3: User Defined Primitive

primitive DFF (Q, Clk, D);
  output Q;
  input Clk, D;

  reg Q;                             // Edge sensitive UDP

  initial
    Q = 1;

  table
//  Clk  D  : old Q : Q
     r   0  :   ?   : 0;      // Clock '0'
     r   1  :   ?   : 1;      // Clock '1'
    (0?) 0  :   0   : -;      // Possible Clock
    (0?) 1  :   1   : -;      //    "           "
    (?1) 0  :   0   : -;      //    "           "
    (?1) 1  :   1   : -;      //    "           "
    (?0) ?  :   ?   : -;      // Ignore falling clock
    (1?) ?  :   ?   : -;      //   "   "    "
     ?   *  :   ?   : -;      // Ignore D changes on steady clock
  endtable

endprimitive


// Section 110.4: User Defined Primitive

primitive SRFF (output reg Q = 1'b1, input S, R);
//  initial Q = 1'b1;
  table
 // S R   Q   Q+
    1 0 : ? : 1 ;
    f 0 : 1 : - ;
    0 r : ? : 0 ;
    0 f : 0 : - ;
    1 1 : ? : 0 ;
  endtable
endprimitive


// Section 111.1: Variable

reg a, b, c;
logic [7:0] mem[1:1024], Byte; // Byte is not a memory array
integer i, j, k;
time now;
real r;
shortint ShInt[7];             // Same as ShInt[0:6]
bit[7:0] B;                    // Same as byte B;
logic signed [31:0] L;         // Same as integer L;
byte C = "A";


// Section 111.2: Variable

logic [15:0] V;
logic Parity = 0;
always @(V)
  for ( int i = 0; i <= 15; i++ )
    Parity ^= V[i];


// Section 112.1: Virtual

virtual class BaseClass;  // Class that cannot be instantiated
  pure virtual function int AFunc(int x);
endclass

class ExtendClass extends BaseClass;   // Subclass
  function int AFunc(int x); // Prototype identical to the Base Class
    AFunc = x - 1;
  endfunction
endclass


// Section 112.2: Virtual

// Polymorphism example:
BaseClass Bases[2];     // Declare a variable of abstract BaseClass
ExtendClass ExCl = new; // Instance of an ExtendedClass object
Bases[0] = ExCl;        // Legal
shortint x;
...
if (Bases[0].AFunc(x) == 1)     // Invokes the AFunc method 
                                // from ExtendClass
  ...


// Section 113.1: Virtual Interface

interface Bus;
  logic passenger;
endinterface

class BusTransactor;
  virtual interface Bus bus;

  function new (virtual Bus b);
    bus = b;
  endfunction

  task do_something (i);
    bus.passenger = i;
  endtask
endclass

module Slave (Bus bus); ... endmodule

module Test;
  Bus bus1(), bus2();
  Slave slave_inst1 (bus1);
  Slave slave_inst2 (bus2);
  BusTransactor t1, t2;

  initial
    begin
      t1 = new(bus1);
      t2 = new(bus2);
      t1.do_something(0);       // bus1.passenger = 0
      t2.do_something(1);       // bus2.passenger = 1
    end
endmodule


// Section 113.2: Virtual Interface

// Clocking blocks in virtual interfaces
interface AnIntf (input logic clk); 
  wire a, b;
  clocking cb @(posedge clk);
    input b;
    output a;
  endclocking
  modport STB (clocking cb); // Synchronous testbench modport
  modport DUT (input b, output a); // Connects to DUT
endinterface

module Device (interface I);
  ...
endmodule

module Test_Device;
  logic clk;

  AnIntf I1 (clk);
  AnIntf I2 (clk);
  Device Device1 (I1.DUT);
  Device Device2 (I2.DUT);
  Tester test (I1.STB, I2.STB);
endmodule : Test_Device

module Tester (AnIntf i1, AnIntf i2);
  typedef virtual interface AnIntf VI;

  task Drive (VI v);
    v.cb.a <= 1;
  endtask : Drive

  function Sample (VI v);
    return v.cb.b;
  endfunction : Sample

  initial
    begin
      Drive(i1);
      Sample(i1);
      Drive(i2);
      Sample(i2);
    end
endmodule : Tester


// Section 114.1: Wait

wait (count == 10) $display("Count is ten");


// Section 114.2: Wait

// Wait until the sequence seq1 is successfully completed
wait (seq1.triggered)
  $display("Sequence seq1 has completed");


// Section 114.3: Wait
  
// Wait until the events e1, e2 and e3 are triggered in that sequence.
// When this happens, success is set to one.
// If the events trigger out of sequence, success is set to 0.
wait_order (e1, e2, e3) success = 1; else success = 0;


// Section 114.4: Wait

// Example using wait fork
initial
  begin         // Parent process
    fork
      ...
    join_none
    wait fork;  // Blocks (waits) until all process spawned by this
                // process have finished
  end


// Section 115.1: While

reg [15:0] Word;
bit [ 5:0] CountOnes;

while (Word)
begin
  if (Word[0])
    CountOnes = CountOnes + 1;
  Word = Word >> 1;
end


// Section 116.1: `begin_keywords

`begin_keywords "1364-2001-noconfig
module design;         // design is a keyword in Verilog-2001
  reg logic;           // logic is a keyword in SystemVerilog
endmodule
`end_keywords


// Section 117.1: `define

`define SUBBLOCK1 subblock1_rtl
`define SUBBLOCK2 subblock2_rtl
`define SUBBLOCK3 subblock3_gates

module TopLevel ...

  `SUBBLOCK1 sub1_inst (...);
  `SUBBLOCK2 sub2_inst (...);
  `SUBBLOCK3 sub3_inst (...);
  ...
endmodule


// Section 117.2: `define

// Text macro with arguments
`define nand(delay) nand #(delay)

`nand(3) (f,a,b);
`nand(4) (g,f,c);


// Section 118.1: `ifdef

`define primitiveModel

module Test1;
...
`ifdef primitiveModel
  MyDesign_primitives UUT (...);
`else
  MyDesign_RTL UUT (...);
`endif
endmodule


// Section 118.2: `ifdef

// Chained nested conditional directives
module Test2;
...
`ifdef Block1
  `ifndef Block2
    initial $display ("Block1 is defined");
  `else
    initial $display ("Block1 and Block2 defined");
  `endif
`elsif Block3
  initial $display ("Block3 defined, Block1 is not");
`else
  initial $display ("Block1, Block3 not defined.");
`endif
endmodule


// Section 119.1: `pragma

`pragma resetall
`pragma protect encoding=(enctype="uuencode")
 

// Section 120.1: `timescale
 
`timescale 10ns / 1ps


// Section 121.1: And (Sequence Operator)

assert property (sig1 and (sig2 ##1 sig3) |-> sig4);


// Section 122.1: Assert (Property)

// Concurrent assertions
module FlipFlop (input logic clk, D, output logic Q);
  property P2;
    int d;
    @(posedge clk) (1,(d=D)) |-> ##1 (Q == d);
  endproperty

  Label2: assert property (P2);

  always @(posedge clk)
    Q <= D;
endmodule


// Section 122.2: Assert (Property)

// Module Flipflop above is equivalent to 
module FlipFlop (input logic clk, D, output logic Q);
  property P2;
    int d;
    (1,(d=D)) |-> ##1 (Q == d);
  endproperty

  always @(posedge clk)
  begin
    Label2: assert property (P2);
    Q <= D;
  end
endmodule


// Section 123.1: Assume

a1: assume property (@(posedge clk) ack |=> !ack);
a2: assume property (@(posedge clk) req dist {0:=1, 1:=9});


// Section 124.1: Checker

module m;
  default disable iff rst;
  ...
  // inherits disable iff rst from enclosing module
  checker Check1 (logic sig, event clk = $inferred_clock);
    default clocking @clk;
    endclocking;

    property p1(logic psig);
      ...
    endproperty : p1
  
    assert1: assert property (p1(.psig(test_sig)));
  endchecker: Check1
endmodule : m


// Section 125.1: Checker Instantiation

checker c1(event clk, logic s);
   p1: assert property (@clk s);
endchecker: c1

checker c2(event clk, logic s);
  c1 c1Inst (clk, s);  // static
  always @(clk) begin
    c1 c1_procedural(clk, s); // procedural
  end
endchecker: c2

module m (logic clk, logic a);
  always @(posedge clk) begin
    c2: c2_proc(posedge clk, a); // procedural
  end
endmodule : m


// Section 126.1: Cover

module Top(input bit clk);
  logic a, b;
  sequence s1;
    @(posedge clk) a ##1 b;
  endsequence
  Label1: cover property (s1);
  Label2: cover sequence (s1);  // Alternatively
  ...
endmodule


// Section 127.1: default disable iff

module m;
  default disable iff rst;
  ...
  // inherits disable iff rst from enclosing module
  checker Check1 (logic sig, event clk = $inferred_clock);
    default clocking @clk;
    endclocking;

    property p1(logic psig);
      ...
    endproperty : p1
  
    assert1: assert property (p1(.psig(test_sig)));
  endchecker: Check1
endmodule : m


// Section 128.1: Expect

module Test;
  initial begin
    ...
    #100ns expect(@(posedge clk) a ##1 b) 
      else $error( "expect failed" );
    ...
  end
endmodule : Test


// Section 129.1: First_match

// Sequence with variable delay
sequence seq1;
  e1 ## [2:5] e2;
endsequence

// e1 and e2 are expressions. Each attempt of sequence seq1 can result in
// matches for up to four of the following sequences:
e1 ##2 e2
e1 ##3 e2
e1 ##4 e2
e1 ##5 e2

// However, the following sequence seq_first can result in a match for only one
// of the above four sequences. 
sequence seq_first;
  first_match(e1 ## [2:5] e2);
endsequence

// Whichever match of the above four sequences ends first is a match of sequence seq_first.


// Section 130.1: Implication

s1 |-> s2;
// In the example above, if the sequence s1 matches, then sequence s2 must also match.
// If sequence s1 does not match, then the result is true.

s1 |=> s2;
// The expression above is equivalent to:

`define true 1
s1 ##1 `true |-> s2;
// where `true is a boolean expression, used for visual clarity, that always evaluates to true.


// Section 131.1: Intersect

// Intersect is used to "and" two sequences, implying a third sequence
assert property (
  a ##1 b ##1 c intersect 1'b1 ##1 d ##1 1'b1 |=> e );


// Section 132.1: Or (sequence operator)

// Sequence with or where one of the operands is a sequence
assert property ( (sig1 ##1 sig2) or sig3 |=> sig4 );

// The property holds if either of these sequences occur:
sig1 ##1 sig2  |=> sig4
// or
sig3 |=> sig4


// Section 133.1: Property

property P;
  (a ##1 b) |-> (d ##1 e);
endproperty


// Section 133.2: Property

// Clock inferred from procedural block
always @(posedge clk) assert property ((a ##2 b)); 

// Clock from clocking block
clocking cb1 @(posedge clk);
  property P1; (a ##2 b); endproperty
endclocking
assert property (cb1.P1);


// Section 133.3: Property

// Multi-clock property examples:
sequence s1;
  @(posedge clk1) a ##1 b; // Single clock sequence
endsequence

sequence s2;
  @(posedge clk2) c ##1 d; // Single clock sequence
endsequence

sequence MultSeq;          // Multiple clock sequence
  @(posedge clk1) e ##1 @(posedge clk2) s1 ##1
  @(posedge clk3) s2; 
endsequence

property p1;       // Property with a named multiple-clock seq. 
  MultSeq;
endproperty

property p2;       // Property with multiple-clock implication
  @(posedge clk1) a ##1
  @(posedge clk2) s1 |=> @(posedge clk3) s2;
endproperty

property mult_p6;  // Property with implication with named
  MultSeq |=> MultSeq;      // Multi-clocked sequences
endproperty

property p3;      // a, b, cond, e are clocked on posedge clk1
  @(posedge clk1) a ##1 b |-> 
  if (cond)
    (1 |=> @(posedge clk2) d)
  else
    e ##1 @(posedge clk3) f;  
endproperty      


// Section 133.4: Property

// Recursive properties
property RecP1(p);
  p and (1'b1 |=> RecP1(p));
endproperty

property RecP2;   
  s1 |-> (prop2 and (1'b1 |=> RecP3));
endproperty

property RecP3;          // RecP2 and RecP3 are mutually recursive
  s2 |-> (prop3 and (1'b1 |=> RecP2));
endproperty


// Section 133.5: Property

// Case property
property delayExample(logic [1:0] del);
  case (del)
    2'b00 : a && b;
    2'b01 : a ##1 b;
    2'b10 : a ##2 b;
    2'b11 : a ##3 b;
    default : 0; // doesn't hold if x or z 
  endcase
endproperty   


// Section 134.1: Restrict

r1: restrict property (@(posedge clk) mode == 2'b00);


// Section 135.1: Sequence

a ##N b;    // a must be true on the current clock tick, and b on the Nth 
            // clock tick after a is true
a ##[2:5] b // a must be true on the current clock tick, and b must be true 
            // on some clock tick between 2 and 5 after a is true
sequence s1;
  a ##1 b;
endsequence

sequence s2;
  @(posedge clk2)
  // Reference s1 in s2. s1 starts one clock cycle after the occurrence 
  // of d in sequence s2
  c ##1 d ##1 s1 ##1 f;   // Equivalent to c ##1 d ##1 a ##1 b ##1 f;

  // Use ended method in s2. Now  s1 must end successfully one clock tick 
  // after d
  c ##1 d ##1 s1.ended ##1 f;   
endsequence


// Section 135.2: Sequence

// Consecutive repetition
a ##1 b ##1 b ##1 b ##1 c;

// Equivalent to:
a ##1 b [*3] ##1 c; 		

a [*3];	               // Equiv. to a ##1 a ##1 a

(a[*0:2] ##1 b ##1 c);

// Equivalent to:
(b ##1 c) or (a ##1 b ##1 c) or (a ##1 a ##1 b ##1 c);

// Goto repetition
a ##1 b[->1:9] ##1 c // a followed by at most 9 occurrences of b, 
                     // followed by c

// Non-consecutive repetition
a ##1 b [=1:9] ##1 c

// Equivalent to:
a ##1 ((!b [*0:$] ##1 b)) [*1:9]) ##1 !b[*0:$] ##1 c


// Section 135.3: Sequence

// first_match
sequence s1;
  (a ##[1:2] b) or (c ##[2:4] d);
endsequence

sequence s2;
  first_match(s1);
  // s2 results in the earlier match from one of the following:
  // a ##1 b
  // a ##2 b
  // c ##2 d // Ending at the same time with previous. If both match, 
             // first_match results in two sequences.
  // c ##3 d
  // c ##4 d
endsequence


// Section 135.4: Sequence

// Dynamic creation of a variable and its assignment
sequence SubSeq(lv); // Declare lv as formal argument
  a ##1 !a, lv = b ##1 !c*[0:$] ##1 c && (d == lv);
endsequence

sequence Seq;
  int Var;
  c ##1 SubSeq(Var) ##1 (a == Var); // Var is bound to lv
endsequence


// Section 135.5: Sequence

// Clock flow 
property P;
  @(posedge clk) x ##1 y |=>
  if (z)
    j |=> @(posedge clk1) k; // k is clocked at posedge clk1
  else                       // x, y, z, j, m are clocked at posedge clk
    m |=> @(posedge clk2) n; // n is clocked at posedge clk2
endproperty


// Section 135.6: Sequence

// Multi-clock sequences:
sequence s1;
  @(posedge clk1) a ##1 b;          // Single clock sequence
endsequence

sequence s2;                        // Multiple clock sequence
  @(posedge clk2) c ##1 d ## @(posedge clk1) s1;
endsequence

sequence s3;  // Source sequence s1 evaluated on clk1; Destination 
              // sequence s3 is evaluated at clk3
  @(posedge clk3) g ##1 h ##1 s1.matched [->1] ##1 k;
endsequence


// Section 136.1: Throughout

$fell(burst_mode) ##0
  (!burst_mode) throughout (##2((trdy==0)&&(irdy==0)) [*4]);


// Section 137.1: Within

!sig1[*3] within (($fell sig2) ##0 !sig2[*5]) 


// Section 138.1: $cast

typedef enum {A, B, C, D} ABCD;
ABCD Letter;
$cast( Letter, 1+1);  // Equivalent to Letter = ABCD'(1+1);

// Check if the assignment is legal
if (!$cast( Letter, 1 + 4) ) // 5: invalid cast
  $display("Casting Error");


// Section 139.1: $display and $write

$display("Illegal opcode %h in %m at %t",
          Opcode, $realtime);

$writeh("Variable values (hex.): ",
          reg1,, reg2,, reg3,, reg4,"\n");


// Section 140.1: $fopen and $fclose

integer MessagesFile, DiagnosticsFile, AllFiles;

initial
begin
  MessagesFile = $fopen("messages.txt");
  if (!MessagesFile)
  begin
    $display("Could not open \"messages.txt\"");
    $finish;
  end

  DiagnosticsFile = $fopen("diagnostics.txt");
  if (!DiagnosticsFile)
  begin
    $display("Could not open \"diagnostics.txt\"");
    $finish;
  end

  AllFiles = MessagesFile | DiagnosticsFile | 1;

  $fdisplay(AllFiles, "Starting simulation ...");
  $fdisplay(MessagesFile, "Messages from %m");
  $fdisplay(DiagnosticsFile, "Diagnostics from %m");

  ...

  $fclose(MessagesFile);
  $fclose(DiagnosticsFile);
end


// Section 140.2: $fopen and $fclose

fd = $fopen ("file_name", "rb+"); // open for update (reading and writing)


// Section 141.1: $fread

parameter NumPatterns = 100;
integer Pattern;

reg [3:0] StimUp[1:NumPatterns];
reg [3:0] StimDown[NumPatterns:1];

$fread (StimUp, "stimulus.txt", 5);   // First loaded data 
              // is StimUp[5] then StimUp[6]
$fread (StimDown, "stimulus.txt", 5); // First loaded data 
              // is StimDown[5] then StimDown[6]


// Section 142.1: $monitor

initial
  $monitor("%t : a = %b, f = %b", $realtime, a, f);


// Section 143.1: $readmemb/h, $writememb/h

module Test;
  reg a,b,c,d;
  parameter NumPatterns = 100;
  integer Pattern;

  reg [3:0] Stimulus[1:NumPatterns];

  MyDesign UUT (a,b,c,d,f);

  initial
  begin
    $readmemb("Stimulus.txt", Stimulus);
    Pattern = 0;
    repeat (NumPatterns)
    begin
      Pattern = Pattern + 1;
      {a,b,c,d} = Stimulus[Pattern];
      #110;
    end
  end

  initial
    $monitor("%t a=%b b=%b c=%b d=%b : f=%b",
             $realtime, a, b, c, d, f);

endmodule
 

// Section 144.1: $root

$root.MyModule.U1 // Absolute name


// Section 145.1: $strobe

initial
begin
  a = 0;
  $display(a);                // Displays 0
  $strobe(a);                 // Displays 1 ...
  a = 1;                      // ... because of this statement


// Section 146.1: $timeformat

$timeformat(-10, 2, " x100ps", 20);  // 20.12 x100ps


// Section 147.1: $typename

package a_pkg;
  enum {INIT, START, RUNNING, STOP = 5} state;
endpackage

module m;
  import a_pkg::*;
  typedef logic [15:1] word_t;
  struct {bit s; bit [14:0] m;} arr[];
  string s = $typename(word_t);
  word_t wdata;

  initial begin
    $display($typename(state));
    $display($typename(word_t));
    $display($typename(wdata));
    $display($typename(arr));
    $display($typename(s));
  end
endmodule


// Section 148.1: $unit

$unit.semi_global_sig // Compilation unit name


// Section 149.1: Stochastic Modelling

module Queues;

  parameter Queue = 1;  // Q_id
  parameter Fifo = 1, Lifo = 2;
  parameter QueueMaxLen = 8;
  integer Status, Code, Job, Value, Info;
  reg IsFull;

  task Error;           // Write error message and quit
    ...
  endtask

  initial
  begin
// Create the queue
    $q_initialize(Queue, Lifo, QueueMaxLen, Status);
    if ( Status )
      Error("Couldn't initialize the queue");

// Add jobs
    for (Job = 1; Job <= QueueMaxLen; Job = Job + 1)
    begin
      #10 Info = Job + 100;
      $q_add(Queue, Job, Info, Status);
      if ( Status )
        Error("Couldn't add to the queue");
      $display("Added Job %0d, Info = %0d", Job, Info);
      $write("Statistics: ");
      for ( Code = 1; Code <= 6; Code = Code + 1 )
      begin
        $q_exam(Queue, Code, Value, Status);
        if ( Status )
          Error("Couldn't examine the queue");
        $write("%8d", Value);
      end
      $display("");
    end

// Queue should now be full
    IsFull = $q_full(Queue, Status);
    if ( Status )
      Error("Couldn't see if queue is full");
    if ( !IsFull )
      Error("Queue is NOT full");

// Remove jobs
    repeat ( 10 ) begin
      #5 $q_remove(Queue, Job, Info, Status);
      if ( Status )
        Error("Couldn't remove from the queue");
      $display("Removed Job %0d, Info = %0d", Job,Info);
      $write("Statistics: ");
      for ( Code = 1; Code <= 6; Code = Code + 1 )
      begin
        $q_exam(Queue, Code, Value, Status);
        if ( Status )
          Error("Couldn't examine the queue");
        $write("%8d", Value);
      end
      $display("");
    end
  end
endmodule


// Section 150.1: Timing Checks

reg Err, FastClock;          // Notifier variables

specify
  specparam Tsetup = 3.5, Thold = 1.5,
            Trecover = 2.0, Tskew = 2.0,
            Tpulse = 10.5, Tspike = 0.5,
            Tremoval = 1.5;

  $hold(posedge Clk, Data, Thold);
  $nochange(posedge Clock, Data, 0, 0 );
  $period(posedge Clk, 20, FastClock]);
  $recovery(posedge Clk, Rst, Trecover);
  $setup(Data, posedge Clk, Tsetup);
  $setuphold(posedge Clk &&& !Reset, Data,
             Tsetup, Thold, Err);
  $skew(posedge Clk1, posedge Clk2, Tskew);
  $width(negedge Clk, Tpulse, Tspike);

  $removal(posedge Clear, posedge Clk, Tremoval);
  $recovery(posedge Clear, posedge Clk, Trecover);
  // Equivalent to the previous two lines
  $recrem(posedge Clear, posedge Clk, Trecover, Tremoval);

  $timeskew(posedge Rst &&& Clk1, negedge Clk2, 50);
  $fullskew(posedge Rst &&& Clk1, negedge Clk2, 50, 70);
endspecify


// Section 151.1: Value Change Dump

module Test;
  ...
  initial
  begin
    $dumpfile("results.vcd");
    $dumpvars(1, Test);
  end

// Perform periodic checkpointing of the design.
  initial
    forever
      #10000 $dumpall;
endmodule

// EOF
