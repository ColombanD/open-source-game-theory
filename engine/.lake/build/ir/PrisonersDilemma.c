// Lean compiler output
// Module: PrisonersDilemma
// Imports: public import Init public import PrisonersDilemma.Core public import PrisonersDilemma.Pipeline public import PrisonersDilemma.Models.Simple public import PrisonersDilemma.Models.OpenSourceBots public import PrisonersDilemma.Proofs.Simple public import PrisonersDilemma.Proofs.WorkflowTemplate public import PrisonersDilemma.Proofs.OpenSourceBots
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Core(uint8_t builtin);
lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Pipeline(uint8_t builtin);
lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Models_Simple(uint8_t builtin);
lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Models_OpenSourceBots(uint8_t builtin);
lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Proofs_Simple(uint8_t builtin);
lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Proofs_WorkflowTemplate(uint8_t builtin);
lean_object* initialize_PrisonersDilemma_PrisonersDilemma_Proofs_OpenSourceBots(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PrisonersDilemma_PrisonersDilemma(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PrisonersDilemma_PrisonersDilemma_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PrisonersDilemma_PrisonersDilemma_Pipeline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PrisonersDilemma_PrisonersDilemma_Models_Simple(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PrisonersDilemma_PrisonersDilemma_Models_OpenSourceBots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PrisonersDilemma_PrisonersDilemma_Proofs_Simple(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PrisonersDilemma_PrisonersDilemma_Proofs_WorkflowTemplate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PrisonersDilemma_PrisonersDilemma_Proofs_OpenSourceBots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
