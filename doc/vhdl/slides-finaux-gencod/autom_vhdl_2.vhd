    ...;
    h_v_114 := (x and mask);
    ...;
    if (hw_rst_3 = '1') then
      h_v_111 <= h_u_Simple_u_2;
    elsif rising_edge(clk_1) then
      h_v_111 <= h_v_110;
    end if;
    ...;
    arg_ck_3 <= clk_1;
    arg_v_143 <= h_v_143;
    arg_v_144 <= h_v_144;
    ...;
    z_137 := (h_v_142 + 0);
    z_138 := (h_v_141 + z_137);
    z_139 := (h_v_140 + z_138);
    o := z_139;
    o_o <= o;
  end process update;
  int_of_bool3: int_of_bool
  port map (clk_1 => arg_ck_3,
            hw_rst_3 => hw_rst_3,
            rst_2 => arg_v_143,
            b => arg_v_144,
            o_o => z_136);
  ...;
end architecture rtl;

