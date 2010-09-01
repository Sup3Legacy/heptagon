use work.types.all;

library ieee;
use ieee.std_logic_1164.all;

entity count_23 is
  port (signal clk_1 : in std_logic; signal hw_rst_3 : in std_logic;
        signal rst_2 : in std_logic;
        signal event : in std_logic_vector (0 to 3);
        signal rst : in std_logic; signal o_count : out integer);
end entity count_23;

architecture rtl of count_23 is
  signal z_24 : integer;
  signal z_27 : integer;
  signal z_26 : integer;
  signal z_25 : integer;
  signal h_v_15 : integer;
  signal arg_ck_4 : std_logic;
  signal arg_v_42 : integer;
  signal arg_v_43 : integer;
  signal arg_ck_3 : std_logic;
  signal arg_v_36 : integer;
  signal arg_v_37 : integer;
  signal arg_ck_2 : std_logic;
  signal arg_v_38 : integer;
  signal arg_v_39 : integer;
  signal arg_ck_1 : std_logic;
  signal arg_v_40 : integer;
  signal arg_v_41 : integer;
  component int_of_bool
    port (signal clk_1 : in std_logic; signal hw_rst_3 : in std_logic;
          signal rst_2 : in std_logic; signal b : in std_logic;
          signal o_o : out integer);
  end component;
  for int_of_bool4: int_of_bool use entity work.int_of_bool;
  for int_of_bool3: int_of_bool use entity work.int_of_bool;
  for int_of_bool2: int_of_bool use entity work.int_of_bool;
  for int_of_bool1: int_of_bool use entity work.int_of_bool;
begin
  update : process (clk_1, hw_rst_3, z_25, z_26, z_27, z_24, rst_2, event,
                    rst)
    variable h_v_17 : std_logic;
    variable h_v_37 : integer;
    variable h_v_39 : integer;
    variable h_v_43 : integer;
    variable h_v_41 : integer;
    variable h_v_18 : std_logic_vector (0 to 3);
    variable h_v_42 : integer;
    variable h_v_36 : integer;
    variable h_v_38 : integer;
    variable h_v_40 : integer;
    variable h_v_19 : integer_vector (0 to 3);
    variable h_v_35 : integer;
    variable h_v_32 : integer;
    variable h_v_33 : integer;
    variable h_v_34 : integer;
    variable z_28 : integer;
    variable z_29 : integer;
    variable z_30 : integer;
    variable z_31 : integer;
    variable h_v_16 : integer;
    variable pres : integer;
    variable count : integer;
  begin
    h_v_17 := (rst_2 or rst);
    h_v_37 := event(3);
    h_v_39 := event(2);
    h_v_43 := event(0);
    h_v_41 := event(1);
    h_v_18 := (others => h_v_17);
    h_v_42 := h_v_18(0);
    h_v_36 := h_v_18(3);
    arg_ck_4 <= clk_1;
    arg_v_42 <= h_v_42;
    arg_v_43 <= h_v_43;
    h_v_38 := h_v_18(2);
    arg_ck_3 <= clk_1;
    arg_v_36 <= h_v_36;
    arg_v_37 <= h_v_37;
    h_v_40 := h_v_18(1);
    arg_ck_2 <= clk_1;
    arg_v_38 <= h_v_38;
    arg_v_39 <= h_v_39;
    arg_ck_1 <= clk_1;
    arg_v_40 <= h_v_40;
    arg_v_41 <= h_v_41;
    h_v_19 := (0 => z_27, 1 => z_26, 2 => z_25, 3 => z_24);
    h_v_35 := h_v_19(0);
    h_v_32 := h_v_19(3);
    h_v_33 := h_v_19(2);
    h_v_34 := h_v_19(1);
    z_28 := (h_v_35 + 0);
    z_29 := (h_v_34 + z_28);
    z_30 := (h_v_33 + z_29);
    z_31 := (h_v_32 + z_30);
    case rst is
      when '1' => h_v_16 := 0;
      when '0' => case rst_2 is
                    when '1' => h_v_16 := 0;
                    when '0' => h_v_16 := h_v_15;
                    when others => null;
                  end case;
      when others => null;
    end case;
    pres := z_31;
    count := (h_v_16 + pres);
    if (hw_rst_3 = '1') then
      h_v_15 <= 0;
    elsif rising_edge(clk_1) then
      h_v_15 <= count;
    end if;
    o_count <= count;
  end process update;
  int_of_bool4: int_of_bool port map (clk_1 => arg_ck_4,
                                      hw_rst_3 => hw_rst_3,
                                      rst_2 => arg_v_42, b => arg_v_43,
                                      o_o => z_24);
  int_of_bool3: int_of_bool port map (clk_1 => arg_ck_3,
                                      hw_rst_3 => hw_rst_3,
                                      rst_2 => arg_v_36, b => arg_v_37,
                                      o_o => z_27);
  int_of_bool2: int_of_bool port map (clk_1 => arg_ck_2,
                                      hw_rst_3 => hw_rst_3,
                                      rst_2 => arg_v_38, b => arg_v_39,
                                      o_o => z_26);
  int_of_bool1: int_of_bool port map (clk_1 => arg_ck_1,
                                      hw_rst_3 => hw_rst_3,
                                      rst_2 => arg_v_40, b => arg_v_41,
                                      o_o => z_25);
end architecture rtl;

