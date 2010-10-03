    case tick is
      when '1' => h_v_28 := 1;
      when '0' => h_v_28 := 0;
    end case;
    o := (h_v_27 + h_v_28);
    if (hw_rst_3 = '1') then
      h_v_26 <= 0;
    elsif rising_edge(clk_1) then
      h_v_26 <= o;
    end if;
    o_o <= o;
  end process update;
end architecture rtl;
