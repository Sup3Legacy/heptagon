...;

entity countbits is
  port (signal clk_1 : in std_logic;
        signal hw_rst_3 : in std_logic;
        signal rst_2 : in std_logic;
        ...);
end entity countbits;

architecture rtl of countbits is
  ...;
  component int_of_bool
    port (signal clk_1 : in std_logic;
          signal hw_rst_3 : in std_logic;
          signal rst_2 : in std_logic;
          signal b : in std_logic;
          signal o_o : out integer);
  end component;
  for int_of_bool3: int_of_bool
    use entity work.int_of_bool;
  ...;
begin
  update : process (clk_1, hw_rst_3, z_135, ...)
    variable h_v_116 : std_logic_vector (0 to 2);
    ...;
  begin
