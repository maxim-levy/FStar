
open Prims
open FStar_Pervasives

let cache_version_number : Prims.int = (Prims.parse_int "1")


let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let with_tcenv : 'a . FStar_TypeChecker_Env.env  ->  'a FStar_Syntax_DsEnv.withenv  ->  ('a * FStar_TypeChecker_Env.env) = (fun env f -> (

let uu____32 = (f env.FStar_TypeChecker_Env.dsenv)
in (match (uu____32) with
| (a, dsenv1) -> begin
((a), ((

let uu___54_46 = env
in {FStar_TypeChecker_Env.solver = uu___54_46.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___54_46.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___54_46.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___54_46.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___54_46.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___54_46.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___54_46.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___54_46.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___54_46.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___54_46.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___54_46.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___54_46.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___54_46.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___54_46.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___54_46.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___54_46.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___54_46.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___54_46.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___54_46.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___54_46.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___54_46.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___54_46.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___54_46.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___54_46.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___54_46.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___54_46.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___54_46.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___54_46.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___54_46.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___54_46.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___54_46.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___54_46.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___54_46.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___54_46.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.dep_graph = uu___54_46.FStar_TypeChecker_Env.dep_graph})))
end)))


let parse : FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env pre_fn fn -> (

let uu____68 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____68) with
| (ast, uu____84) -> begin
(

let uu____97 = (match (pre_fn) with
| FStar_Pervasives_Native.None -> begin
((ast), (env))
end
| FStar_Pervasives_Native.Some (pre_fn1) -> begin
(

let uu____107 = (FStar_Parser_Driver.parse_file pre_fn1)
in (match (uu____107) with
| (pre_ast, uu____123) -> begin
(match (((pre_ast), (ast))) with
| (FStar_Parser_AST.Interface (lid1, decls1, uu____142), FStar_Parser_AST.Module (lid2, decls2)) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let uu____153 = (

let uu____158 = (FStar_ToSyntax_Interleave.initialize_interface lid1 decls1)
in (FStar_All.pipe_left (with_tcenv env) uu____158))
in (match (uu____153) with
| (uu____175, env1) -> begin
(

let uu____177 = (FStar_ToSyntax_Interleave.interleave_module ast true)
in (FStar_All.pipe_left (with_tcenv env1) uu____177))
end))
end
| uu____190 -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_PreModuleMismatch), ("mismatch between pre-module and module\n")))
end)
end))
end)
in (match (uu____97) with
| (ast1, env1) -> begin
(

let uu____205 = (FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1)
in (FStar_All.pipe_left (with_tcenv env1) uu____205))
end))
end)))


let init_env : FStar_Parser_Dep.deps  ->  FStar_TypeChecker_Env.env = (fun deps -> (

let solver1 = (

let uu____222 = (FStar_Options.lax ())
in (match (uu____222) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____223 -> begin
(

let uu___55_224 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___55_224.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___55_224.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___55_224.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.encode_modul = uu___55_224.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___55_224.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___55_224.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.finish = uu___55_224.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___55_224.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1 FStar_Parser_Const.prims_lid)
in (

let env1 = (

let uu___56_227 = env
in {FStar_TypeChecker_Env.solver = uu___56_227.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___56_227.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___56_227.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___56_227.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___56_227.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___56_227.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___56_227.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___56_227.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___56_227.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___56_227.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___56_227.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___56_227.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___56_227.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___56_227.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___56_227.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___56_227.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___56_227.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___56_227.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___56_227.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___56_227.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___56_227.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___56_227.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___56_227.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___56_227.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___56_227.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___56_227.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___56_227.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___56_227.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___56_227.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = FStar_Tactics_Interpreter.synthesize; FStar_TypeChecker_Env.splice = uu___56_227.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___56_227.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___56_227.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___56_227.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___56_227.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___56_227.FStar_TypeChecker_Env.dep_graph})
in (

let env2 = (

let uu___57_229 = env1
in {FStar_TypeChecker_Env.solver = uu___57_229.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___57_229.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___57_229.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___57_229.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___57_229.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___57_229.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___57_229.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___57_229.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___57_229.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___57_229.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___57_229.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___57_229.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___57_229.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___57_229.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___57_229.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___57_229.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___57_229.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___57_229.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___57_229.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___57_229.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___57_229.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___57_229.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___57_229.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___57_229.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___57_229.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___57_229.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___57_229.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___57_229.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___57_229.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___57_229.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice; FStar_TypeChecker_Env.is_native_tactic = uu___57_229.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___57_229.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___57_229.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___57_229.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___57_229.FStar_TypeChecker_Env.dep_graph})
in (

let env3 = (

let uu___58_231 = env2
in {FStar_TypeChecker_Env.solver = uu___58_231.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___58_231.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___58_231.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___58_231.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___58_231.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___58_231.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___58_231.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___58_231.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___58_231.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___58_231.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___58_231.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___58_231.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___58_231.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___58_231.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___58_231.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___58_231.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___58_231.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___58_231.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___58_231.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___58_231.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___58_231.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___58_231.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___58_231.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___58_231.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___58_231.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___58_231.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___58_231.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___58_231.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___58_231.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___58_231.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___58_231.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___58_231.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___58_231.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___58_231.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___58_231.FStar_TypeChecker_Env.dep_graph})
in ((env3.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env3);
env3;
)))))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun curmod env frag -> (

let acceptable_mod_name = (fun modul -> (

let uu____256 = (

let uu____257 = (

let uu____258 = (FStar_Options.file_list ())
in (FStar_List.hd uu____258))
in (FStar_Parser_Dep.lowercase_module_name uu____257))
in (

let uu____261 = (

let uu____262 = (FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____262))
in (Prims.op_Equality uu____256 uu____261))))
in (

let range_of_first_mod_decl = (fun modul -> (match (modul) with
| FStar_Parser_AST.Module (uu____267, ({FStar_Parser_AST.d = uu____268; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____270; FStar_Parser_AST.quals = uu____271; FStar_Parser_AST.attrs = uu____272})::uu____273) -> begin
d
end
| FStar_Parser_AST.Interface (uu____280, ({FStar_Parser_AST.d = uu____281; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____283; FStar_Parser_AST.quals = uu____284; FStar_Parser_AST.attrs = uu____285})::uu____286, uu____287) -> begin
d
end
| uu____294 -> begin
FStar_Range.dummyRange
end))
in (

let uu____295 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____295) with
| FStar_Parser_Driver.Empty -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Decls ([]) -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____307 = (

let uu____312 = (FStar_ToSyntax_Interleave.interleave_module ast_modul false)
in (FStar_All.pipe_left (with_tcenv env) uu____312))
in (match (uu____307) with
| (ast_modul1, env1) -> begin
(

let uu____333 = (

let uu____338 = (FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod ast_modul1)
in (FStar_All.pipe_left (with_tcenv env1) uu____338))
in (match (uu____333) with
| (modul, env2) -> begin
((

let uu____360 = (

let uu____361 = (acceptable_mod_name modul)
in (not (uu____361)))
in (match (uu____360) with
| true -> begin
(

let msg = (

let uu____363 = (

let uu____364 = (

let uu____365 = (FStar_Options.file_list ())
in (FStar_List.hd uu____365))
in (FStar_Parser_Dep.module_name_of_file uu____364))
in (FStar_Util.format1 "Interactive mode only supports a single module at the top-level. Expected module %s" uu____363))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonSingletonTopLevelModule), (msg)) (range_of_first_mod_decl ast_modul1)))
end
| uu____368 -> begin
()
end));
(

let uu____369 = (

let uu____378 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____378) with
| true -> begin
((modul), ([]), (env2))
end
| uu____389 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env2 modul)
end))
in (match (uu____369) with
| (modul1, uu____397, env3) -> begin
((FStar_Pervasives_Native.Some (modul1)), (env3))
end));
)
end))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(match (curmod) with
| FStar_Pervasives_Native.None -> begin
(

let uu____414 = (FStar_List.hd ast_decls)
in (match (uu____414) with
| {FStar_Parser_AST.d = uu____421; FStar_Parser_AST.drange = rng; FStar_Parser_AST.doc = uu____423; FStar_Parser_AST.quals = uu____424; FStar_Parser_AST.attrs = uu____425} -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleFirstStatement), ("First statement must be a module declaration")) rng)
end))
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____435 = (FStar_Util.fold_map (fun env1 a_decl -> (

let uu____453 = (

let uu____460 = (FStar_ToSyntax_Interleave.prefix_with_interface_decls a_decl)
in (FStar_All.pipe_left (with_tcenv env1) uu____460))
in (match (uu____453) with
| (decls, env2) -> begin
((env2), (decls))
end))) env ast_decls)
in (match (uu____435) with
| (env1, ast_decls_l) -> begin
(

let uu____511 = (

let uu____516 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts (FStar_List.flatten ast_decls_l))
in (FStar_All.pipe_left (with_tcenv env1) uu____516))
in (match (uu____511) with
| (sigelts, env2) -> begin
(

let uu____537 = (

let uu____546 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____546) with
| true -> begin
((modul), ([]), (env2))
end
| uu____557 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env2 modul sigelts)
end))
in (match (uu____537) with
| (modul1, uu____565, env3) -> begin
((FStar_Pervasives_Native.Some (modul1)), (env3))
end))
end))
end))
end)
end)))))


let load_interface_decls : FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.filename  ->  FStar_TypeChecker_Env.env = (fun env interface_file_name -> (

let r = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename (interface_file_name)))
in (match (r) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____582)), uu____583) -> begin
(

let uu____608 = (

let uu____613 = (FStar_ToSyntax_Interleave.initialize_interface l decls)
in (FStar_All.pipe_left (with_tcenv env) uu____613))
in (FStar_Pervasives_Native.snd uu____608))
end
| FStar_Parser_ParseIt.ASTFragment (uu____626) -> begin
(

let uu____637 = (

let uu____642 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in ((FStar_Errors.Fatal_ParseErrors), (uu____642)))
in (FStar_Errors.raise_err uu____637))
end
| FStar_Parser_ParseIt.ParseError (err, msg, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err), (msg), (rng)))))
end
| FStar_Parser_ParseIt.Term (uu____646) -> begin
(failwith "Impossible: parsing a Toplevel always results in an ASTFragment")
end)))


let load_module_from_cache : FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_Syntax_DsEnv.module_inclusion_info) FStar_Pervasives_Native.option = (

let some_cache_invalid = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let invalidate_cache = (fun fn -> (FStar_ST.op_Colon_Equals some_cache_invalid (FStar_Pervasives_Native.Some (()))))
in (fun env fn -> (

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let fail1 = (fun tag -> ((invalidate_cache ());
(

let uu____790 = (

let uu____791 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____792 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____791 uu____792)))
in (

let uu____793 = (

let uu____798 = (FStar_Util.format3 "%s cache file %s; will recheck %s and all subsequent files" tag cache_file fn)
in ((FStar_Errors.Warning_CachedFile), (uu____798)))
in (FStar_Errors.log_issue uu____790 uu____793)));
FStar_Pervasives_Native.None;
))
in (

let uu____807 = (FStar_ST.op_Bang some_cache_invalid)
in (match (uu____807) with
| FStar_Pervasives_Native.Some (uu____919) -> begin
FStar_Pervasives_Native.None
end
| uu____928 -> begin
(match ((FStar_Util.file_exists cache_file)) with
| true -> begin
(

let uu____941 = (FStar_Util.load_value_from_file cache_file)
in (match (uu____941) with
| FStar_Pervasives_Native.None -> begin
(fail1 "Corrupt")
end
| FStar_Pervasives_Native.Some (vnum, digest, tcmod, tcmod_iface_opt, mii) -> begin
(match ((Prims.op_disEquality vnum cache_version_number)) with
| true -> begin
(fail1 "Stale, because inconsistent cache version")
end
| uu____1057 -> begin
(

let uu____1058 = (FStar_Parser_Dep.hash_dependences env.FStar_TypeChecker_Env.dep_graph fn)
in (match (uu____1058) with
| FStar_Pervasives_Native.Some (digest') -> begin
(match ((Prims.op_Equality digest digest')) with
| true -> begin
FStar_Pervasives_Native.Some (((tcmod), (tcmod_iface_opt), (mii)))
end
| uu____1116 -> begin
((

let uu____1118 = (FStar_Options.debug_any ())
in (match (uu____1118) with
| true -> begin
((

let uu____1120 = (FStar_Util.string_of_int (FStar_List.length digest'))
in (

let uu____1125 = (FStar_Parser_Dep.print_digest digest')
in (

let uu____1126 = (FStar_Util.string_of_int (FStar_List.length digest))
in (

let uu____1131 = (FStar_Parser_Dep.print_digest digest)
in (FStar_Util.print4 "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n" uu____1120 uu____1125 uu____1126 uu____1131)))));
(match ((Prims.op_Equality (FStar_List.length digest) (FStar_List.length digest'))) with
| true -> begin
(FStar_List.iter2 (fun uu____1156 uu____1157 -> (match (((uu____1156), (uu____1157))) with
| ((x, y), (x', y')) -> begin
(match (((Prims.op_disEquality x x') || (Prims.op_disEquality y y'))) with
| true -> begin
(

let uu____1186 = (FStar_Parser_Dep.print_digest ((((x), (y)))::[]))
in (

let uu____1195 = (FStar_Parser_Dep.print_digest ((((x'), (y')))::[]))
in (FStar_Util.print2 "Differ at: Expected %s\n Got %s\n" uu____1186 uu____1195)))
end
| uu____1204 -> begin
()
end)
end)) digest digest')
end
| uu____1205 -> begin
()
end);
)
end
| uu____1206 -> begin
()
end));
(fail1 "Stale");
)
end)
end
| uu____1207 -> begin
(fail1 "Stale")
end))
end)
end))
end
| uu____1216 -> begin
(fail1 "Absent")
end)
end)))))))


let store_module_to_cache : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Syntax_DsEnv.module_inclusion_info  ->  Prims.unit = (fun env fn m modul_iface_opt mii -> (

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let digest = (FStar_Parser_Dep.hash_dependences env.FStar_TypeChecker_Env.dep_graph fn)
in (match (digest) with
| FStar_Pervasives_Native.Some (hashes) -> begin
(FStar_Util.save_value_to_file cache_file ((cache_version_number), (hashes), (m), (modul_iface_opt), (mii)))
end
| uu____1285 -> begin
(

let uu____1294 = (

let uu____1295 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1296 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____1295 uu____1296)))
in (

let uu____1297 = (

let uu____1302 = (FStar_Util.format1 "%s was not written, since some of its dependences were not also checked" cache_file)
in ((FStar_Errors.Warning_FileNotWritten), (uu____1302)))
in (FStar_Errors.log_issue uu____1294 uu____1297)))
end))))


let tc_one_file : FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_TypeChecker_Env.env) = (fun env pre_fn fn -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let tc_source_file = (fun uu____1350 -> (

let uu____1351 = (parse env pre_fn fn)
in (match (uu____1351) with
| (fmod, env1) -> begin
(

let check_mod = (fun uu____1387 -> (

let uu____1388 = (FStar_Util.record_time (fun uu____1410 -> (FStar_TypeChecker_Tc.check_module env1 fmod)))
in (match (uu____1388) with
| ((tcmod, tcmod_iface_opt, env2), time) -> begin
((((tcmod), (time))), (tcmod_iface_opt), (env2))
end)))
in (

let uu____1445 = (

let uu____1458 = ((FStar_Options.should_verify fmod.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ())))
in (match (uu____1458) with
| true -> begin
(

let uu____1471 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____1471 check_mod))
end
| uu____1484 -> begin
(check_mod ())
end))
in (match (uu____1445) with
| (tcmod, tcmod_iface_opt, env2) -> begin
(

let mii = (FStar_Syntax_DsEnv.inclusion_info env2.FStar_TypeChecker_Env.dsenv (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name)
in ((tcmod), (tcmod_iface_opt), (mii), (env2)))
end)))
end)))
in (

let uu____1521 = (FStar_Options.cache_checked_modules ())
in (match (uu____1521) with
| true -> begin
(

let uu____1530 = (load_module_from_cache env fn)
in (match (uu____1530) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1557 = (tc_source_file ())
in (match (uu____1557) with
| (tcmod, tcmod_iface_opt, mii, env1) -> begin
((

let uu____1597 = ((

let uu____1600 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____1600 (Prims.parse_int "0"))) && ((FStar_Options.lax ()) || (FStar_Options.should_verify (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name.FStar_Ident.str)))
in (match (uu____1597) with
| true -> begin
(store_module_to_cache env1 fn (FStar_Pervasives_Native.fst tcmod) tcmod_iface_opt mii)
end
| uu____1601 -> begin
()
end));
((tcmod), (env1));
)
end))
end
| FStar_Pervasives_Native.Some (tcmod, tcmod_iface_opt, mii) -> begin
(

let tcmod1 = (match (tcmod.FStar_Syntax_Syntax.is_interface) with
| true -> begin
tcmod
end
| uu____1622 -> begin
(

let uu____1623 = (FStar_Options.use_extracted_interfaces ())
in (match (uu____1623) with
| true -> begin
(match ((Prims.op_Equality tcmod_iface_opt FStar_Pervasives_Native.None)) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleNotFound), ((Prims.strcat "use_extracted_interfaces option is set but could not find it in the cache for: " tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str))) FStar_Range.dummyRange)
end
| uu____1626 -> begin
(FStar_All.pipe_right tcmod_iface_opt FStar_Util.must)
end)
end
| uu____1629 -> begin
tcmod
end))
end)
in (

let uu____1630 = (

let uu____1635 = (FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1 mii (FStar_TypeChecker_Normalize.erase_universes env))
in (FStar_All.pipe_left (with_tcenv env) uu____1635))
in (match (uu____1630) with
| (uu____1656, env1) -> begin
(

let env2 = (FStar_TypeChecker_Tc.load_checked_module env1 tcmod1)
in ((((tcmod1), ((Prims.parse_int "0")))), (env2)))
end)))
end))
end
| uu____1663 -> begin
(

let uu____1664 = (tc_source_file ())
in (match (uu____1664) with
| (tcmod, tcmod_iface_opt, uu____1689, env1) -> begin
(

let tcmod1 = (match ((FStar_Util.is_some tcmod_iface_opt)) with
| true -> begin
(

let uu____1712 = (FStar_All.pipe_right tcmod_iface_opt FStar_Util.must)
in ((uu____1712), ((FStar_Pervasives_Native.snd tcmod))))
end
| uu____1715 -> begin
tcmod
end)
in ((tcmod1), (env1)))
end))
end)));
))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((Prims.op_Equality m1 m2) && (

let uu____1729 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____1729 (("fsti")::("fsi")::[])))) && (

let uu____1731 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____1731 (("fst")::("fs")::[])))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> (

let uu____1738 = (FStar_TypeChecker_Tc.pop_context env msg)
in (FStar_All.pipe_right uu____1738 FStar_Pervasives.ignore)))


let push_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> (FStar_TypeChecker_Tc.push_context env msg))


let tc_one_file_from_remaining : Prims.string Prims.list  ->  FStar_TypeChecker_Env.env  ->  (Prims.string Prims.list * (FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env) = (fun remaining env -> (

let uu____1769 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____1807 = (tc_one_file env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____1807) with
| (m, env1) -> begin
((remaining1), ((((m)::[]), (env1))))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____1872 = (tc_one_file env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____1872) with
| (m, env1) -> begin
((remaining1), ((((m)::[]), (env1))))
end))
end
| [] -> begin
(([]), ((([]), (env))))
end)
in (match (uu____1769) with
| (remaining1, (nmods, env1)) -> begin
((remaining1), (nmods), (env1))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____2056 -> begin
(

let uu____2059 = acc
in (match (uu____2059) with
| (mods, env) -> begin
(

let uu____2094 = (tc_one_file_from_remaining remaining env)
in (match (uu____2094) with
| (remaining1, nmods, env1) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (env1)) remaining1)
end))
end))
end))


let batch_mode_tc : Prims.string Prims.list  ->  FStar_Parser_Dep.deps  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env) = (fun filenames dep_graph1 -> ((

let uu____2169 = (FStar_Options.debug_any ())
in (match (uu____2169) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____2172 = (

let uu____2173 = (FStar_All.pipe_right filenames (FStar_List.filter FStar_Options.should_verify_file))
in (FStar_String.concat " " uu____2173))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____2172));
)
end
| uu____2180 -> begin
()
end));
(

let env = (init_env dep_graph1)
in (

let uu____2182 = (tc_fold_interleave (([]), (env)) filenames)
in (match (uu____2182) with
| (all_mods, env1) -> begin
((

let uu____2228 = ((FStar_Options.interactive ()) && (

let uu____2230 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____2230 (Prims.parse_int "0"))))
in (match (uu____2228) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____2231 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (env1));
)
end)));
))




