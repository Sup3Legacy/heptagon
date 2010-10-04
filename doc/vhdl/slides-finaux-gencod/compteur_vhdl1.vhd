use work.compteur.all;

library ieee;
use ieee.std_logic_1164.all;

entity compteur is
  port (signal clk_1 : in std_logic; 
        signal hw_rst_3 : in std_logic;
        signal rst_2 : in std_logic; 
        signal tick : in std_logic;
        signal top : in std_logic;
        signal o_o : out integer);
end entity compteur;

architecture rtl of compteur is
  signal h_v_26 : integer;
begin
  update : process (clk_1, hw_rst_3, rst_2,
                    tick, top, h_v_26)
    variable h_v_27 : integer;
    variable h_v_28 : integer;
    variable o : integer;
  begin
    case top is
      when '1' => h_v_27 := 0;
      when '0' => case rst_2 is
                    when '1' => h_v_27 := 0;
                    when '0' => h_v_27 := h_v_26;
                  end case;
    end case;
