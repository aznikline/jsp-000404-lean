// Lean compiler output
// Module: Jsp000404.EvenPartition
// Imports: public import Init public meta import Init public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions public import Mathlib.Combinatorics.SimpleGraph.Bipartite public import Mathlib.Data.Fintype.Basic
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
lean_object* l_Fin_succ___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2d000404___private_Jsp000404_EvenPartition_0__Fin_succ_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2d000404___private_Jsp000404_EvenPartition_0__Fin_succ_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2d000404___private_Jsp000404_EvenPartition_0__Fin_succ_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___closed__0 = (const lean_object*)&lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_jsp_x2d000404___private_Jsp000404_EvenPartition_0__Fin_succ_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_2(v_h__1_2_, v_x_1_, lean_box(0));
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2d000404___private_Jsp000404_EvenPartition_0__Fin_succ_match__1_splitter(lean_object* v_n_4_, lean_object* v_motive_5_, lean_object* v_x_6_, lean_object* v_h__1_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_2(v_h__1_7_, v_x_6_, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2d000404___private_Jsp000404_EvenPartition_0__Fin_succ_match__1_splitter___boxed(lean_object* v_n_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_jsp_x2d000404___private_Jsp000404_EvenPartition_0__Fin_succ_match__1_splitter(v_n_9_, v_motive_10_, v_x_11_, v_h__1_12_);
lean_dec(v_n_9_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__0(lean_object* v_i_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__0___boxed(lean_object* v_i_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__0(v_i_16_);
lean_dec(v_i_16_);
return v_res_17_;
}
}
LEAN_EXPORT uint8_t lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__1(lean_object* v_C_18_, lean_object* v_i_19_, lean_object* v_v_20_, lean_object* v_w_21_){
_start:
{
lean_object* v_dec_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v_dec_22_ = lean_ctor_get(v_C_18_, 1);
lean_inc_ref(v_dec_22_);
lean_dec_ref(v_C_18_);
v___x_23_ = l_Fin_succ___redArg(v_i_19_);
v___x_24_ = lean_apply_3(v_dec_22_, v___x_23_, v_v_20_, v_w_21_);
v___x_25_ = lean_unbox(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__1___boxed(lean_object* v_C_26_, lean_object* v_i_27_, lean_object* v_v_28_, lean_object* v_w_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__1(v_C_26_, v_i_27_, v_v_28_, v_w_29_);
lean_dec(v_i_27_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg(lean_object* v_C_33_){
_start:
{
lean_object* v___f_34_; lean_object* v___f_35_; lean_object* v___x_36_; 
v___f_34_ = ((lean_object*)(lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___closed__0));
v___f_35_ = lean_alloc_closure((void*)(lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_35_, 0, v_C_33_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___f_34_);
lean_ctor_set(v___x_36_, 1, v___f_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict(lean_object* v_V_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_n_40_, lean_object* v_C_41_, lean_object* v_s_42_, lean_object* v_h0_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_jsp_x2d000404_Jsp404_EvenCover_restrict___redArg(v_C_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_jsp_x2d000404_Jsp404_EvenCover_restrict___boxed(lean_object* v_V_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_n_48_, lean_object* v_C_49_, lean_object* v_s_50_, lean_object* v_h0_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_jsp_x2d000404_Jsp404_EvenCover_restrict(v_V_45_, v_inst_46_, v_inst_47_, v_n_48_, v_C_49_, v_s_50_, v_h0_51_);
lean_dec(v_s_50_);
lean_dec(v_n_48_);
lean_dec(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_52_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Coloring_Constructions(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Bipartite(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_jsp_x2d000404_Jsp000404_EvenPartition(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Coloring_Constructions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Bipartite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
