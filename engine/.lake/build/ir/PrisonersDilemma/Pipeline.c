// Lean compiler output
// Module: PrisonersDilemma.Pipeline
// Imports: public import Init public import PrisonersDilemma.Core
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
LEAN_EXPORT uint8_t lp_PrisonersDilemma_PD_ProgramModel_action___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_ProgramModel_action___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_PrisonersDilemma_PD_mkOutcome(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playActions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_ProgramModel_action___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playOutcome___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_PrisonersDilemma_PD_ProgramModel_action(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playOutcome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playOutcome___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playOutcome___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playActions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_PrisonersDilemma_PD_ProgramModel_action___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_4, x_3);
x_7 = lean_apply_2(x_5, x_2, x_6);
x_8 = lean_unbox(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_ProgramModel_action___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_PrisonersDilemma_PD_ProgramModel_action___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_PrisonersDilemma_PD_ProgramModel_action(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_PrisonersDilemma_PD_ProgramModel_action___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_ProgramModel_action___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_PrisonersDilemma_PD_ProgramModel_action(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playActions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_4 = lp_PrisonersDilemma_PD_ProgramModel_action___redArg(x_1, x_2, x_3);
x_5 = lp_PrisonersDilemma_PD_ProgramModel_action___redArg(x_1, x_3, x_2);
x_6 = lean_box(x_4);
x_7 = lean_box(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playActions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_PrisonersDilemma_PD_playActions___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playOutcome___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lp_PrisonersDilemma_PD_playActions___redArg(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = lp_PrisonersDilemma_PD_mkOutcome(x_2, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playOutcome___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_PrisonersDilemma_PD_playOutcome___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playOutcome(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_PrisonersDilemma_PD_playOutcome___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_PrisonersDilemma_PD_playOutcome___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_PrisonersDilemma_PD_playOutcome(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Pipeline(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PrisonersDilemma_PrisonersDilemma_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
