use work.types.all;

library ieee;
use ieee.std_logic_1164.all;

entity alloc is
  port (signal clk_1 : in std_logic; signal hw_rst_3 : in std_logic;
        signal rst_2 : in std_logic; signal r0 : in std_logic;
        signal r1 : in std_logic; signal o_g0 : out std_logic;
        signal o_g1 : out std_logic);
end entity alloc;

architecture rtl of alloc is
  signal h_v_35 : std_logic;
  signal h_v_42 : st_2;
  signal h_v_43 : std_logic;
  signal h_v_32 : std_logic;
  signal h_v_33 : std_logic;
  signal h_v_34 : std_logic;
begin
  update : process (clk_1, hw_rst_3, rst_2, r0, r1)
    variable ck_23 : st_2;
    variable r_21 : std_logic;
    variable r_20 : std_logic;
    variable pnr_14 : std_logic;
    variable r_19 : std_logic;
    variable r_22 : std_logic;
    variable h_v_41 : std_logic;
    variable g0 : std_logic;
    variable r_18 : std_logic;
    variable r_17 : std_logic;
    variable r_16 : std_logic;
    variable r_15 : std_logic;
    variable g1 : std_logic;
    variable h_v_36 : std_logic;
    variable h_v_37 : std_logic;
    variable ns_31 : st_2;
    variable nr_30 : std_logic;
    variable h_v_39 : std_logic;
    variable ns_29 : st_2;
    variable nr_28 : std_logic;
    variable h_v_38 : std_logic;
    variable h_v_40 : std_logic;
    variable ns_27 : st_2;
    variable nr_26 : std_logic;
    variable nr_24 : std_logic;
    variable ns_25 : st_2;
    variable nr_13 : std_logic;
    variable ns_11 : st_2;
    variable r_12 : std_logic;
  begin
    case rst_2 is
      when '1' => ck_23 := IDLE0_1;
      when '0' => ck_23 := h_v_42;
      when others => null;
    end case;
    case rst_2 is
      when '1' => r_21 := '1';
      when '0' => r_21 := h_v_33;
      when others => null;
    end case;
    case rst_2 is
      when '1' => r_20 := '1';
      when '0' => r_20 := h_v_34;
      when others => null;
    end case;
    case rst_2 is
      when '1' => pnr_14 := '0';
      when '0' => pnr_14 := h_v_43;
      when others => null;
    end case;
    case rst_2 is
      when '1' => r_19 := '1';
      when '0' => r_19 := h_v_35;
      when others => null;
    end case;
    case rst_2 is
      when '1' => r_22 := '1';
      when '0' => r_22 := h_v_32;
      when others => null;
    end case;
    h_v_41 := r0;
    case ck_23 is
      when ALLOC1_1 => g0 := '0';
      when ALLOC0_1 => g0 := '1';
      when IDLE1_1 => g0 := '0';
      when IDLE0_1 => g0 := '0';
      when others => null;
    end case;
    case ck_23 is
      when ALLOC1_1 => r_18 := '0';
      when ALLOC0_1 => r_18 := r_22;
      when IDLE1_1 => r_18 := r_22;
      when IDLE0_1 => r_18 := r_22;
      when others => null;
    end case;
    case ck_23 is
      when ALLOC1_1 => r_17 := r_21;
      when ALLOC0_1 => r_17 := '0';
      when IDLE1_1 => r_17 := r_21;
      when IDLE0_1 => r_17 := r_21;
      when others => null;
    end case;
    case ck_23 is
      when ALLOC1_1 => r_16 := r_20;
      when ALLOC0_1 => r_16 := r_20;
      when IDLE1_1 => r_16 := '0';
      when IDLE0_1 => r_16 := r_20;
      when others => null;
    end case;
    case ck_23 is
      when ALLOC1_1 => r_15 := r_19;
      when ALLOC0_1 => r_15 := r_19;
      when IDLE1_1 => r_15 := r_19;
      when IDLE0_1 => r_15 := '0';
      when others => null;
    end case;
    case ck_23 is
      when ALLOC1_1 => g1 := '1';
      when ALLOC0_1 => g1 := '0';
      when IDLE1_1 => g1 := '0';
      when IDLE0_1 => g1 := '0';
      when others => null;
    end case;
    h_v_36 := (not r1);
    h_v_37 := (not r0);
    case h_v_36 is
      when '1' => ns_31 := IDLE0_1;
      when '0' => ns_31 := ALLOC1_1;
      when others => null;
    end case;
    case h_v_36 is
      when '1' => nr_30 := '1';
      when '0' => nr_30 := '0';
      when others => null;
    end case;
    h_v_39 := r1;
    case h_v_37 is
      when '1' => ns_29 := IDLE1_1;
      when '0' => ns_29 := ALLOC0_1;
      when others => null;
    end case;
    case h_v_37 is
      when '1' => nr_28 := '1';
      when '0' => nr_28 := '0';
      when others => null;
    end case;
    h_v_38 := (r0 and (not r1));
    h_v_40 := (r1 and (not r0));
    case h_v_39 is
      when '1' => ns_27 := ALLOC1_1;
      when '0' => case h_v_38 is
                    when '1' => ns_27 := ALLOC0_1;
                    when '0' => ns_27 := IDLE1_1;
                    when others => null;
                  end case;
      when others => null;
    end case;
    case h_v_39 is
      when '1' => nr_26 := '1';
      when '0' => case h_v_38 is
                    when '1' => nr_26 := '1';
                    when '0' => nr_26 := '0';
                    when others => null;
                  end case;
      when others => null;
    end case;
    case h_v_41 is
      when '1' => nr_24 := '1';
      when '0' => case h_v_40 is
                    when '1' => nr_24 := '1';
                    when '0' => nr_24 := '0';
                    when others => null;
                  end case;
      when others => null;
    end case;
    case h_v_41 is
      when '1' => ns_25 := ALLOC0_1;
      when '0' => case h_v_40 is
                    when '1' => ns_25 := ALLOC1_1;
                    when '0' => ns_25 := IDLE0_1;
                    when others => null;
                  end case;
      when others => null;
    end case;
    case ck_23 is
      when ALLOC1_1 => nr_13 := nr_30;
      when ALLOC0_1 => nr_13 := nr_28;
      when IDLE1_1 => nr_13 := nr_26;
      when IDLE0_1 => nr_13 := nr_24;
      when others => null;
    end case;
    case ck_23 is
      when ALLOC1_1 => ns_11 := ns_31;
      when ALLOC0_1 => ns_11 := ns_29;
      when IDLE1_1 => ns_11 := ns_27;
      when IDLE0_1 => ns_11 := ns_25;
      when others => null;
    end case;
    if (hw_rst_3 = '1') then
      h_v_35 <= '1';
    elsif rising_edge(clk_1) then
      h_v_35 <= r_15;
    end if;
    if (hw_rst_3 = '1') then
      h_v_42 <= IDLE0_1;
    elsif rising_edge(clk_1) then
      h_v_42 <= ns_11;
    end if;
    if (hw_rst_3 = '1') then
      h_v_43 <= '0';
    elsif rising_edge(clk_1) then
      h_v_43 <= nr_13;
    end if;
    r_12 := pnr_14;
    if (hw_rst_3 = '1') then
      h_v_32 <= '1';
    elsif rising_edge(clk_1) then
      h_v_32 <= r_18;
    end if;
    if (hw_rst_3 = '1') then
      h_v_33 <= '1';
    elsif rising_edge(clk_1) then
      h_v_33 <= r_17;
    end if;
    if (hw_rst_3 = '1') then
      h_v_34 <= '1';
    elsif rising_edge(clk_1) then
      h_v_34 <= r_16;
    end if;
    o_g0 <= g0;
    o_g1 <= g1;
  end process update;
end architecture rtl;

