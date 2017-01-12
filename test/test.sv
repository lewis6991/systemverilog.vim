module a (
  input        clk,
  input        reset_n,
  input        in,
  output logic out
);

  typedef struct {
    int a;
    bit b;
    logic[5:0] c;
  } my_struct;

  module a2;
  endmodule : a2

endmodule

class a;
endclass

typedef class b;

class c;

  pure virtual static function my_func();

  task my_task(bit a);
    wire a = b | c;
  endtask

  function automatic my_func2();
    assert (a< 4)
    else `ERROR("a >= 4")
      ; // TODO: Fixme

    if (b)
      void'(func_call());

    `ERROR("a >= 4")

    func_call();

  endfunction : my_func2

endclass

`define A_MACRO(a, b) assign a <= b & c;

`define A_MACRO(a, b) \
  always_comb begin \
    a <= b & c; \
    `MACRO_ASSIGN(a, b) \
    `MACRO_ASSIGN       \
    $error("Error")     \
    b <= 4'b1001; \
  end

extern module extern_a;

/* comments
comments
begin
module
end
endmodule
comments
*/

// Comment begin

interface a;

  generate
    genvar i;
    for (i = 0; i < 8; i = i+1)
    begin
      always_ff @ (posedge clk or negedge reset_n)
        if (reset_n)
          a <= '0;
        else if (clk)
          a <= b;
    end
  endgenerate

endinterface : a

concurrent_assert_label1 : assert property(
  a |-> b ||
        c
);

concurrent_assert_label2 : assert property(
  a |->
    b || c
);

concurrent_cover : cover property(
  a |-> b
);

concurrent_assume : assume property(
  a |-> b
);

// TODO: module a #(parameter a = 0, parameter b = (1+1), c = `NUM );
module a #(parameter a = 0, parameter b = 1+1, c = `NUM );

  b u_b (
    .clk    (clk       ),
    .reset_n(reset_n   ),
    .in     ({2'b0, in})
  );

  c #(
    .N(10)
  ) u_c (
    .clk    (clk       ),
    .reset_n(reset_n   ),
    .in     ({2'b0, in})
  );

  always_ff @ (posedge clk or negedge reset_n)
    if (reset_n)
      a <= '0;
    else if (clk)
      a <= b;

  always_comb
    a = b;

endmodule

begin
  if (1)
    if(1)
      something();
    else begin
      if ( multi_line_condition1 ||
        multi_line_condition2 ||
        multi_line_condition3 ||
      )
        if (1)
          a = a || b ||
              c;
        else if (1)
          if (1)
            for (int i = 0; i < 8; ++i)
              case (a)
                1'b1: something();
                1'b0:
                  something;
                const: begin
                end
                const2:
                  case (b)
                    1'b1: fork
                      something1();
                      begin
                        something1();
                      end
                    join
                  endcase
                default : `MACRO(a)
              endcase
    end
end

wire e = a ? b :
         c ? d :
             e;

wire e = (a == 2 ? b : 1'b1) &&
         c && d;

assert_delays: assert property (
  ##'1 a ##[1:0] b
);

assign item.array[19].field1.field1 = 1'b1;

for (genvar i = 0; i < 8; i = i + 1) begin : g1
  assign item.array[i].field1.field1 = 1'b1;
end
