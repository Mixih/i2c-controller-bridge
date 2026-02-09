`define SLICE(i, w) slc_top(i, 0, w):slc_bot(i, 0, w)
`define SLICE_O(i, off, w) slc_top(i, off, w):slc_bot(i, off, w)
`define SLICE_R(t, b, w) slc_top(t, 0, w):slc_bot(b, 0, w)
`define SLICE_RO(t, b, off, w) slc_top(t, off, w):slc_bot(b, off, w)
`define S_EXT(n, w, n_w) {{((n_w) - (w)){n[(w) - 1]}}, n}
`define Z_EXT(n, w, n_w) {{((n_w) - (w)){1'b0}}, n}
`define Z_PAD(n) ({1'b0, (n)})

function automatic integer slc_top;
    input integer i;
    input integer off;
    input integer item_width;
    begin
        slc_top = (((i + 1) * item_width) - 1) + off;
        //$display(slc_top);
    end
endfunction

function automatic integer slc_bot;
    input integer i;
    input integer off;
    input integer item_width;
    begin
        slc_bot = i * item_width + off;
    end
endfunction

function automatic is_pow_2;
    input integer n;
    begin
        is_pow_2 = n == 0 || (n & (n - 1)) == 0;
    end
endfunction

function automatic integer calc_div_fac;
    input integer in_hz;
    input integer target_hz;
    begin
        calc_div_fac = in_hz / target_hz;
    end
endfunction

function automatic validate_div_fac;
    input integer div_fac;
    input integer in_hz;
    input integer target_hz;
    input integer tolerance_100ths_perc;
    begin : val_div_fac_scope
        if ((((in_hz / div_fac) - target_hz) * 10000) / target_hz > tolerance_100ths_perc
            || (((in_hz / div_fac) - target_hz) * 10000) / target_hz < -tolerance_100ths_perc)
            validate_div_fac = 1'b0;
        else
            validate_div_fac = 1'b1;
    end
endfunction
