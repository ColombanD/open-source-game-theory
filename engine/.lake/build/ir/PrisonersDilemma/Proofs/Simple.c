// Lean compiler output
// Module: PrisonersDilemma.Proofs.Simple
// Imports: public import Init public import PrisonersDilemma.Models.Simple
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (x_2 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_5, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_6, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_2);
x_9 = lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_2);
x_9 = lean_unbox(x_3);
x_10 = lp_PrisonersDilemma___private_PrisonersDilemma_Proofs_Simple_0__PD_payoff_match__1_splitter(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Models_Simple(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Proofs_Simple(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PrisonersDilemma_PrisonersDilemma_Models_Simple(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
