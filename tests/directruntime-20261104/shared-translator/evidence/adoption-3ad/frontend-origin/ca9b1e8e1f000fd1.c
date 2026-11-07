LEAN_EXPORT uint8_t l_String_anyAux___at_____private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; 
x_6 = lean_string_utf8_get(x_2, x_4);
x_7 = lean_uint32_dec_eq(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_8;
goto _start;
}
else
{
lean_dec(x_4);
return x_7;
}
}
}
}
