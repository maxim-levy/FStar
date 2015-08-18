
let try_solve = (fun ( env ) ( f ) -> (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env f))

let report = (fun ( env ) ( errs ) -> (let _108_10 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _108_9 = (Microsoft_FStar_Tc_Errors.failed_to_prove_specification errs)
in (Microsoft_FStar_Tc_Errors.report _108_10 _108_9))))

let discharge_guard = (fun ( env ) ( g ) -> (Microsoft_FStar_Tc_Rel.try_discharge_guard env g))

let force_trivial = (fun ( env ) ( g ) -> (discharge_guard env g))

let syn' = (fun ( env ) ( k ) -> (let _108_29 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _108_29 k)))

let is_xvar_free = (fun ( x ) ( t ) -> (let f = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x Microsoft_FStar_Absyn_Syntax.tun) f.Microsoft_FStar_Absyn_Syntax.fxvs)))

let is_tvar_free = (fun ( a ) ( t ) -> (let f = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.kun) f.Microsoft_FStar_Absyn_Syntax.ftvs)))

let check_and_ascribe = (fun ( env ) ( e ) ( t1 ) ( t2 ) -> (let env = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let check = (fun ( env ) ( t1 ) ( t2 ) -> (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(Microsoft_FStar_Tc_Rel.try_teq env t1 t2)
end
| false -> begin
(match ((Microsoft_FStar_Tc_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _108_53 = (Microsoft_FStar_Tc_Rel.apply_guard f e)
in (Support.All.pipe_left (fun ( _108_52 ) -> Some (_108_52)) _108_53))
end)
end))
in (match ((env.Microsoft_FStar_Tc_Env.is_pattern && false)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Rel.try_teq env t1 t2)) with
| None -> begin
(let _108_57 = (let _108_56 = (let _108_55 = (Microsoft_FStar_Tc_Errors.expected_pattern_of_type env t2 e t1)
in (let _108_54 = (Microsoft_FStar_Tc_Env.get_range env)
in (_108_55, _108_54)))
in Microsoft_FStar_Absyn_Syntax.Error (_108_56))
in (raise (_108_57)))
end
| Some (g) -> begin
(e, g)
end)
end
| false -> begin
(match ((check env t1 t2)) with
| None -> begin
(let _108_61 = (let _108_60 = (let _108_59 = (Microsoft_FStar_Tc_Errors.expected_expression_of_type env t2 e t1)
in (let _108_58 = (Microsoft_FStar_Tc_Env.get_range env)
in (_108_59, _108_58)))
in Microsoft_FStar_Absyn_Syntax.Error (_108_60))
in (raise (_108_61)))
end
| Some (g) -> begin
(let _37_51 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _108_62 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Applied guard is %s\n") _108_62))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (let e = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x.Microsoft_FStar_Absyn_Syntax.v t2) (Some (t2)) e.Microsoft_FStar_Absyn_Syntax.pos)
end
| _37_57 -> begin
(let _37_58 = e
in (let _108_63 = (Support.Microsoft.FStar.Util.mk_ref (Some (t2)))
in {Microsoft_FStar_Absyn_Syntax.n = _37_58.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _108_63; Microsoft_FStar_Absyn_Syntax.pos = _37_58.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _37_58.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _37_58.Microsoft_FStar_Absyn_Syntax.uvs}))
end)
in (e, g))))
end)
end))))

let env_binders = (fun ( env ) -> (match ((Support.ST.read Microsoft_FStar_Options.full_context_dependency)) with
| true -> begin
(Microsoft_FStar_Tc_Env.binders env)
end
| false -> begin
(Microsoft_FStar_Tc_Env.t_binders env)
end))

let as_uvar_e = (fun ( _37_1 ) -> (match (_37_1) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _37_73)); Microsoft_FStar_Absyn_Syntax.tk = _37_70; Microsoft_FStar_Absyn_Syntax.pos = _37_68; Microsoft_FStar_Absyn_Syntax.fvs = _37_66; Microsoft_FStar_Absyn_Syntax.uvs = _37_64} -> begin
uv
end
| _37_78 -> begin
(Support.All.failwith "Impossible")
end))

let as_uvar_t = (fun ( t ) -> (match (t) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _37_90)); Microsoft_FStar_Absyn_Syntax.tk = _37_87; Microsoft_FStar_Absyn_Syntax.pos = _37_85; Microsoft_FStar_Absyn_Syntax.fvs = _37_83; Microsoft_FStar_Absyn_Syntax.uvs = _37_81} -> begin
uv
end
| _37_95 -> begin
(Support.All.failwith "Impossible")
end))

let new_kvar = (fun ( env ) -> (let _108_73 = (let _108_72 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _108_71 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_kvar _108_72 _108_71)))
in (Support.All.pipe_right _108_73 Support.Prims.fst)))

let new_tvar = (fun ( env ) ( k ) -> (let _108_80 = (let _108_79 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _108_78 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _108_79 _108_78 k)))
in (Support.All.pipe_right _108_80 Support.Prims.fst)))

let new_evar = (fun ( env ) ( t ) -> (let _108_87 = (let _108_86 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _108_85 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _108_86 _108_85 t)))
in (Support.All.pipe_right _108_87 Support.Prims.fst)))

let new_implicit_tvar = (fun ( env ) ( k ) -> (let _37_105 = (let _108_93 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _108_92 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar _108_93 _108_92 k)))
in (match (_37_105) with
| (t, u) -> begin
(let _108_95 = (let _108_94 = (as_uvar_t u)
in (_108_94, u.Microsoft_FStar_Absyn_Syntax.pos))
in (t, _108_95))
end)))

let new_implicit_evar = (fun ( env ) ( t ) -> (let _37_110 = (let _108_101 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _108_100 = (env_binders env)
in (Microsoft_FStar_Tc_Rel.new_evar _108_101 _108_100 t)))
in (match (_37_110) with
| (e, u) -> begin
(let _108_103 = (let _108_102 = (as_uvar_e u)
in (_108_102, u.Microsoft_FStar_Absyn_Syntax.pos))
in (e, _108_103))
end)))

let force_tk = (fun ( s ) -> (match ((Support.ST.read s.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _108_106 = (let _108_105 = (Support.Microsoft.FStar.Range.string_of_range s.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "Impossible: Forced tk not present (%s)" _108_105))
in (Support.All.failwith _108_106))
end
| Some (tk) -> begin
tk
end))

let tks_of_args = (fun ( args ) -> (Support.All.pipe_right args (Support.List.map (fun ( _37_2 ) -> (match (_37_2) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _108_111 = (let _108_110 = (force_tk t)
in Support.Microsoft.FStar.Util.Inl (_108_110))
in (_108_111, imp))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let _108_113 = (let _108_112 = (force_tk v)
in Support.Microsoft.FStar.Util.Inr (_108_112))
in (_108_113, imp))
end)))))

let is_implicit = (fun ( _37_3 ) -> (match (_37_3) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _37_129 -> begin
false
end))

let destruct_arrow_kind = (fun ( env ) ( tt ) ( k ) ( args ) -> (let ktop = (let _108_124 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (Support.All.pipe_right _108_124 (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env)))
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let rec aux = (fun ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k')) -> begin
(let imp_follows = (match (args) with
| (_37_145, qual)::_37_143 -> begin
(is_implicit qual)
end
| _37_150 -> begin
false
end)
in (let rec mk_implicits = (fun ( vars ) ( subst ) ( bs ) -> (match (bs) with
| b::brest -> begin
(match ((Support.All.pipe_right (Support.Prims.snd b) is_implicit)) with
| true -> begin
(let imp_arg = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _108_137 = (let _108_134 = (let _108_133 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_tvar r vars _108_133))
in (Support.All.pipe_right _108_134 Support.Prims.fst))
in (Support.All.pipe_right _108_137 (fun ( x ) -> (let _108_136 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (x), _108_136)))))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _108_142 = (let _108_139 = (let _108_138 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Rel.new_evar r vars _108_138))
in (Support.All.pipe_right _108_139 Support.Prims.fst))
in (Support.All.pipe_right _108_142 (fun ( x ) -> (let _108_141 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (x), _108_141)))))
end)
in (let subst = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
subst
end
| false -> begin
(let _108_143 = (Microsoft_FStar_Absyn_Util.subst_formal b imp_arg)
in (_108_143)::subst)
end)
in (let _37_169 = (mk_implicits vars subst brest)
in (match (_37_169) with
| (imp_args, bs) -> begin
((imp_arg)::imp_args, bs)
end))))
end
| false -> begin
(let _108_144 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _108_144))
end)
end
| _37_171 -> begin
(let _108_145 = (Microsoft_FStar_Absyn_Util.subst_binders subst bs)
in ([], _108_145))
end))
in (match (imp_follows) with
| true -> begin
([], bs, k')
end
| false -> begin
(let _37_174 = (let _108_146 = (Microsoft_FStar_Tc_Env.binders env)
in (mk_implicits _108_146 [] bs))
in (match (_37_174) with
| (imps, bs) -> begin
(imps, bs, k')
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_37_176, k)) -> begin
(aux k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (_37_181) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_kind k)
in (let binders = (Microsoft_FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _108_147 = (Microsoft_FStar_Tc_Rel.new_kvar r binders)
in (Support.All.pipe_right _108_147 Support.Prims.fst))
in (let bs = (let _108_148 = (tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _108_148))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) r)
in (let _37_188 = (let _108_149 = (Microsoft_FStar_Tc_Rel.keq env None k kar)
in (Support.All.pipe_left (force_trivial env) _108_149))
in ([], bs, kres)))))))
end
| _37_191 -> begin
(let _108_152 = (let _108_151 = (let _108_150 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env tt ktop)
in (_108_150, r))
in Microsoft_FStar_Absyn_Syntax.Error (_108_151))
in (raise (_108_152)))
end))
in (aux ktop)))))

let as_imp = (fun ( _37_4 ) -> (match (_37_4) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
true
end
| _37_196 -> begin
false
end))

let pat_as_exps = (fun ( allow_implicits ) ( env ) ( p ) -> (let pvar_eq = (fun ( x ) ( y ) -> (match ((x, y)) with
| (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_205)), Microsoft_FStar_Tc_Env.Binding_var ((y, _37_210))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| (Microsoft_FStar_Tc_Env.Binding_typ ((x, _37_216)), Microsoft_FStar_Tc_Env.Binding_typ ((y, _37_221))) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _37_226 -> begin
false
end))
in (let vars_of_bindings = (fun ( bs ) -> (Support.All.pipe_right bs (Support.List.map (fun ( _37_5 ) -> (match (_37_5) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, _37_232)) -> begin
Support.Microsoft.FStar.Util.Inr (x)
end
| Microsoft_FStar_Tc_Env.Binding_typ ((x, _37_237)) -> begin
Support.Microsoft.FStar.Util.Inl (x)
end
| _37_241 -> begin
(Support.All.failwith "impos")
end)))))
in (let rec pat_as_arg_with_env = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _37_248)) -> begin
(let t = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (let _37_254 = (Microsoft_FStar_Tc_Rel.new_evar p.Microsoft_FStar_Absyn_Syntax.p [] t)
in (match (_37_254) with
| (e, u) -> begin
(let p = (let _37_255 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)); Microsoft_FStar_Absyn_Syntax.sort = _37_255.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_255.Microsoft_FStar_Absyn_Syntax.p})
in ([], [], [], env, Support.Microsoft.FStar.Util.Inr (e), p))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _37_260)) -> begin
(let k = (new_kvar env)
in (let _37_266 = (let _108_174 = (Microsoft_FStar_Tc_Env.binders env)
in (Microsoft_FStar_Tc_Rel.new_tvar p.Microsoft_FStar_Absyn_Syntax.p _108_174 k))
in (match (_37_266) with
| (t, u) -> begin
(let p = (let _37_267 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)); Microsoft_FStar_Absyn_Syntax.sort = _37_267.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_267.Microsoft_FStar_Absyn_Syntax.p})
in ([], [], [], env, Support.Microsoft.FStar.Util.Inl (t), p))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c None p.Microsoft_FStar_Absyn_Syntax.p)
in ([], [], [], env, Support.Microsoft.FStar.Util.Inr (e), p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let w = (let _108_176 = (let _108_175 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _108_175))
in Microsoft_FStar_Tc_Env.Binding_var (_108_176))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, Support.Microsoft.FStar.Util.Inr (e), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var (x) -> begin
(let b = (let _108_178 = (let _108_177 = (new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (x.Microsoft_FStar_Absyn_Syntax.v, _108_177))
in Microsoft_FStar_Tc_Env.Binding_var (_108_178))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x None p.Microsoft_FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, Support.Microsoft.FStar.Util.Inr (e), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let w = (let _108_180 = (let _108_179 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _108_179))
in Microsoft_FStar_Tc_Env.Binding_typ (_108_180))
in (let env = (match (allow_wc_dependence) with
| true -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env w)
end
| false -> begin
env
end)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in ((w)::[], [], (w)::[], env, Support.Microsoft.FStar.Util.Inl (t), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let b = (let _108_182 = (let _108_181 = (new_kvar env)
in (a.Microsoft_FStar_Absyn_Syntax.v, _108_181))
in Microsoft_FStar_Tc_Env.Binding_typ (_108_182))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a None p.Microsoft_FStar_Absyn_Syntax.p)
in ((b)::[], (b)::[], [], env, Support.Microsoft.FStar.Util.Inl (t), p))))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _37_326 = (Support.All.pipe_right pats (Support.List.fold_left (fun ( _37_304 ) ( _37_307 ) -> (match ((_37_304, _37_307)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(let _37_314 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_37_314) with
| (b', a', w', env, te, pat) -> begin
(let arg = (match (te) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(match (imp) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.itarg t)
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(match (imp) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.ivarg e)
end
| false -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end)
end)
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_37_326) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _108_190 = (let _108_189 = (let _108_188 = (let _108_187 = (let _108_186 = (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) fv.Microsoft_FStar_Absyn_Syntax.v fv.Microsoft_FStar_Absyn_Syntax.p)
in (let _108_185 = (Support.All.pipe_right args Support.List.rev)
in (_108_186, _108_185)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _108_187 None p.Microsoft_FStar_Absyn_Syntax.p))
in (_108_188, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_108_189))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _108_190))
in (let _108_193 = (Support.All.pipe_right (Support.List.rev b) Support.List.flatten)
in (let _108_192 = (Support.All.pipe_right (Support.List.rev a) Support.List.flatten)
in (let _108_191 = (Support.All.pipe_right (Support.List.rev w) Support.List.flatten)
in (_108_193, _108_192, _108_191, env, Support.Microsoft.FStar.Util.Inr (e), (let _37_328 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev pats))); Microsoft_FStar_Absyn_Syntax.sort = _37_328.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_328.Microsoft_FStar_Absyn_Syntax.p}))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_37_331) -> begin
(Support.All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let pats = (Support.List.map (fun ( _37_343 ) -> (match (_37_343) with
| (p, imp) -> begin
(let _108_199 = (elaborate_pat env p)
in (_108_199, imp))
end)) pats)
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env fv.Microsoft_FStar_Absyn_Syntax.v)
in (let pats = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| None -> begin
(match (pats) with
| [] -> begin
[]
end
| _37_349 -> begin
(let _108_202 = (let _108_201 = (let _108_200 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _108_200))
in Microsoft_FStar_Absyn_Syntax.Error (_108_201))
in (raise (_108_202)))
end)
end
| Some ((f, _37_352)) -> begin
(let rec aux = (fun ( formals ) ( pats ) -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _37_365::_37_363) -> begin
(let _108_209 = (let _108_208 = (let _108_207 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in ("Too many pattern arguments", _108_207))
in Microsoft_FStar_Absyn_Syntax.Error (_108_208))
in (raise (_108_209)))
end
| (_37_371::_37_369, []) -> begin
(Support.All.pipe_right formals (Support.List.map (fun ( f ) -> (match (f) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let a = (let _108_211 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _108_211 Microsoft_FStar_Absyn_Syntax.kun))
in (match (allow_implicits) with
| true -> begin
(let _108_213 = (let _108_212 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _108_212))
in (_108_213, (as_imp imp)))
end
| false -> begin
(let _108_215 = (let _108_214 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _108_214))
in (_108_215, (as_imp imp)))
end))
end
| (Support.Microsoft.FStar.Util.Inr (_37_382), Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let _108_217 = (let _108_216 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var (a)) None _108_216))
in (_108_217, true)))
end
| _37_389 -> begin
(let _108_222 = (let _108_221 = (let _108_220 = (let _108_218 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (Support.Microsoft.FStar.Util.format1 "Insufficient pattern arguments (%s)" _108_218))
in (let _108_219 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (_108_220, _108_219)))
in Microsoft_FStar_Absyn_Syntax.Error (_108_221))
in (raise (_108_222)))
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match ((f, p.Microsoft_FStar_Absyn_Syntax.v)) with
| (((Support.Microsoft.FStar.Util.Inl (_), imp), Microsoft_FStar_Absyn_Syntax.Pat_tvar (_))) | (((Support.Microsoft.FStar.Util.Inl (_), imp), Microsoft_FStar_Absyn_Syntax.Pat_twild (_))) -> begin
(let _108_223 = (aux formals' pats')
in ((p, (as_imp imp)))::_108_223)
end
| ((Support.Microsoft.FStar.Util.Inl (_37_417), imp), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_37_422)) when allow_implicits -> begin
(let _108_224 = (aux formals' pats')
in ((p, (as_imp imp)))::_108_224)
end
| ((Support.Microsoft.FStar.Util.Inl (_37_426), imp), _37_431) -> begin
(let a = (let _108_225 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _108_225 Microsoft_FStar_Absyn_Syntax.kun))
in (let p1 = (match (allow_implicits) with
| true -> begin
(let _108_226 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, Microsoft_FStar_Absyn_Syntax.tun))) None _108_226))
end
| false -> begin
(let _108_227 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) None _108_227))
end)
in (let pats' = (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_37_436) -> begin
pats'
end
| _37_439 -> begin
pats
end)
in (let _108_228 = (aux formals' pats')
in ((p1, (as_imp imp)))::_108_228))))
end
| ((Support.Microsoft.FStar.Util.Inr (_37_442), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _37_448) when p_imp -> begin
(let _108_229 = (aux formals' pats')
in ((p, true))::_108_229)
end
| ((Support.Microsoft.FStar.Util.Inr (_37_451), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), _37_457) -> begin
(let a = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Syntax.tun)
in (let p = (let _108_230 = (Microsoft_FStar_Absyn_Syntax.range_of_lid fv.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var (a)) None _108_230))
in (let _108_231 = (aux formals' pats)
in ((p, true))::_108_231)))
end
| ((Support.Microsoft.FStar.Util.Inr (_37_462), imp), _37_467) -> begin
(let _108_232 = (aux formals' pats')
in ((p, (as_imp imp)))::_108_232)
end)
end))
in (aux f pats))
end)
in (let _37_470 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)); Microsoft_FStar_Absyn_Syntax.sort = _37_470.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_470.Microsoft_FStar_Absyn_Syntax.p}))))
end
| _37_473 -> begin
p
end))
in (let one_pat = (fun ( allow_wc_dependence ) ( env ) ( p ) -> (let p = (elaborate_pat env p)
in (let _37_485 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_37_485) with
| (b, a, w, env, arg, p) -> begin
(match ((Support.All.pipe_right b (Support.Microsoft.FStar.Util.find_dup pvar_eq))) with
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_488))) -> begin
(let _108_241 = (let _108_240 = (let _108_239 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inr (x)))
in (_108_239, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_108_240))
in (raise (_108_241)))
end
| Some (Microsoft_FStar_Tc_Env.Binding_typ ((x, _37_494))) -> begin
(let _108_244 = (let _108_243 = (let _108_242 = (Microsoft_FStar_Tc_Errors.nonlinear_pattern_variable (Support.Microsoft.FStar.Util.Inl (x)))
in (_108_242, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_108_243))
in (raise (_108_244)))
end
| _37_499 -> begin
(b, a, w, arg, p)
end)
end))))
in (let as_arg = (fun ( _37_6 ) -> (match (_37_6) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Support.All.failwith "Impossible")
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end))
in (let top_level_pat_as_args = (fun ( env ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(Support.All.failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (q::pats) -> begin
(let _37_521 = (one_pat false env q)
in (match (_37_521) with
| (b, a, _37_518, te, q) -> begin
(let _37_536 = (Support.List.fold_right (fun ( p ) ( _37_526 ) -> (match (_37_526) with
| (w, args, pats) -> begin
(let _37_532 = (one_pat false env p)
in (match (_37_532) with
| (b', a', w', arg, p) -> begin
(match ((not ((Support.Microsoft.FStar.Util.multiset_equiv pvar_eq a a')))) with
| true -> begin
(let _108_258 = (let _108_257 = (let _108_256 = (let _108_254 = (vars_of_bindings a)
in (let _108_253 = (vars_of_bindings a')
in (Microsoft_FStar_Tc_Errors.disjunctive_pattern_vars _108_254 _108_253)))
in (let _108_255 = (Microsoft_FStar_Tc_Env.get_range env)
in (_108_256, _108_255)))
in Microsoft_FStar_Absyn_Syntax.Error (_108_257))
in (raise (_108_258)))
end
| false -> begin
(let _108_260 = (let _108_259 = (as_arg arg)
in (_108_259)::args)
in ((Support.List.append w' w), _108_260, (p)::pats))
end)
end))
end)) pats ([], [], []))
in (match (_37_536) with
| (w, args, pats) -> begin
(let _108_262 = (let _108_261 = (as_arg te)
in (_108_261)::args)
in ((Support.List.append b w), _108_262, (let _37_537 = p
in {Microsoft_FStar_Absyn_Syntax.v = Microsoft_FStar_Absyn_Syntax.Pat_disj ((q)::pats); Microsoft_FStar_Absyn_Syntax.sort = _37_537.Microsoft_FStar_Absyn_Syntax.sort; Microsoft_FStar_Absyn_Syntax.p = _37_537.Microsoft_FStar_Absyn_Syntax.p})))
end))
end))
end
| _37_540 -> begin
(let _37_548 = (one_pat true env p)
in (match (_37_548) with
| (b, _37_543, _37_545, arg, p) -> begin
(let _108_264 = (let _108_263 = (as_arg arg)
in (_108_263)::[])
in (b, _108_264, p))
end))
end))
in (let _37_552 = (top_level_pat_as_args env p)
in (match (_37_552) with
| (b, args, p) -> begin
(let exps = (Support.All.pipe_right args (Support.List.map (fun ( _37_7 ) -> (match (_37_7) with
| (Support.Microsoft.FStar.Util.Inl (_37_555), _37_558) -> begin
(Support.All.failwith "Impossible: top-level pattern must be an expression")
end
| (Support.Microsoft.FStar.Util.Inr (e), _37_563) -> begin
e
end))))
in (b, exps, p))
end))))))))))

let decorate_pattern = (fun ( env ) ( p ) ( exps ) -> (let qq = p
in (let rec aux = (fun ( p ) ( e ) -> (let pkg = (fun ( q ) ( t ) -> (let _108_283 = (Support.All.pipe_left (fun ( _108_282 ) -> Some (_108_282)) (Support.Microsoft.FStar.Util.Inr (t)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _108_283 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, e.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_constant (_37_579), Microsoft_FStar_Absyn_Syntax.Exp_constant (_37_582)) -> begin
(let _108_284 = (force_tk e)
in (pkg p.Microsoft_FStar_Absyn_Syntax.v _108_284))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _37_590 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _108_287 = (let _108_286 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _108_285 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _108_286 _108_285)))
in (Support.All.failwith _108_287))
end
| false -> begin
()
end)
in (let _37_592 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(let _108_289 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _108_288 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern variable %s introduced at type %s\n" _108_289 _108_288)))
end
| false -> begin
()
end)
in (let s = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env y.Microsoft_FStar_Absyn_Syntax.sort)
in (let x = (let _37_595 = x
in {Microsoft_FStar_Absyn_Syntax.v = _37_595.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = _37_595.Microsoft_FStar_Absyn_Syntax.p})
in (let _108_290 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_var (x)) _108_290))))))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) -> begin
(let _37_603 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq x y) Support.Prims.op_Negation)) with
| true -> begin
(let _108_293 = (let _108_292 = (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (let _108_291 = (Microsoft_FStar_Absyn_Print.strBvd y.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _108_292 _108_291)))
in (Support.All.failwith _108_293))
end
| false -> begin
()
end)
in (let x = (let _37_605 = x
in (let _108_294 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _37_605.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _108_294; Microsoft_FStar_Absyn_Syntax.p = _37_605.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) x.Microsoft_FStar_Absyn_Syntax.sort)))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _37_610)), _37_614) -> begin
(let x = (let _37_616 = x
in (let _108_295 = (force_tk e)
in {Microsoft_FStar_Absyn_Syntax.v = _37_616.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _108_295; Microsoft_FStar_Absyn_Syntax.p = _37_616.Microsoft_FStar_Absyn_Syntax.p}))
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) x.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, [])), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _37_626))) -> begin
(let _37_630 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _108_296 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.failwith _108_296))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv', q, []))) fv'.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, argpats)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv', _37_647)); Microsoft_FStar_Absyn_Syntax.tk = _37_644; Microsoft_FStar_Absyn_Syntax.pos = _37_642; Microsoft_FStar_Absyn_Syntax.fvs = _37_640; Microsoft_FStar_Absyn_Syntax.uvs = _37_638}, args))) -> begin
(let _37_655 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.fvar_eq fv fv') Support.Prims.op_Negation)) with
| true -> begin
(let _108_297 = (Support.Microsoft.FStar.Util.format2 "Expected pattern constructor %s; got %s" fv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str fv'.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.failwith _108_297))
end
| false -> begin
()
end)
in (let fv = fv'
in (let rec match_args = (fun ( matched_pats ) ( args ) ( argpats ) -> (match ((args, argpats)) with
| ([], []) -> begin
(let _108_304 = (force_tk e)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, (Support.List.rev matched_pats)))) _108_304))
end
| (arg::args, (argpat, _37_671)::argpats) -> begin
(match ((arg, argpat.Microsoft_FStar_Absyn_Syntax.v)) with
| ((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_37_681)) -> begin
(let x = (let _108_305 = (force_tk t)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _108_305))
in (let q = (let _108_307 = (Support.All.pipe_left (fun ( _108_306 ) -> Some (_108_306)) (Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, t))) _108_307 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inr (e), Some (Microsoft_FStar_Absyn_Syntax.Implicit)), Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_37_692)) -> begin
(let x = (let _108_308 = (force_tk e)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p p.Microsoft_FStar_Absyn_Syntax.p _108_308))
in (let q = (let _108_310 = (Support.All.pipe_left (fun ( _108_309 ) -> Some (_108_309)) (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.sort)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e))) _108_310 p.Microsoft_FStar_Absyn_Syntax.p))
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((Support.Microsoft.FStar.Util.Inl (t), imp), _37_702) -> begin
(let pat = (aux_t argpat t)
in (match_args (((pat, (as_imp imp)))::matched_pats) args argpats))
end
| ((Support.Microsoft.FStar.Util.Inr (e), imp), _37_710) -> begin
(let pat = (let _108_311 = (aux argpat e)
in (_108_311, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _37_714 -> begin
(let _108_314 = (let _108_313 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _108_312 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _108_313 _108_312)))
in (Support.All.failwith _108_314))
end))
in (match_args [] args argpats))))
end
| _37_716 -> begin
(let _108_319 = (let _108_318 = (Support.Microsoft.FStar.Range.string_of_range qq.Microsoft_FStar_Absyn_Syntax.p)
in (let _108_317 = (Microsoft_FStar_Absyn_Print.pat_to_string qq)
in (let _108_316 = (let _108_315 = (Support.All.pipe_right exps (Support.List.map Microsoft_FStar_Absyn_Print.exp_to_string))
in (Support.All.pipe_right _108_315 (Support.String.concat "\n\t")))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _108_318 _108_317 _108_316))))
in (Support.All.failwith _108_319))
end))))
and aux_t = (fun ( p ) ( t0 ) -> (let pkg = (fun ( q ) ( k ) -> (let _108_327 = (Support.All.pipe_left (fun ( _108_326 ) -> Some (_108_326)) (Support.Microsoft.FStar.Util.Inl (k)))
in (Microsoft_FStar_Absyn_Syntax.withinfo q _108_327 p.Microsoft_FStar_Absyn_Syntax.p)))
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t0)
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, t.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _37_728 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _108_330 = (let _108_329 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _108_328 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _108_329 _108_328)))
in (Support.All.failwith _108_330))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_twild (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(let _37_735 = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.bvar_eq a b) Support.Prims.op_Negation)) with
| true -> begin
(let _108_333 = (let _108_332 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _108_331 = (Microsoft_FStar_Absyn_Print.strBvd b.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format2 "Expected pattern variable %s; got %s" _108_332 _108_331)))
in (Support.All.failwith _108_333))
end
| false -> begin
()
end)
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_tvar (b)) b.Microsoft_FStar_Absyn_Syntax.sort))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _37_739)), _37_743) -> begin
(let k0 = (force_tk t0)
in (let a = (let _37_746 = a
in {Microsoft_FStar_Absyn_Syntax.v = _37_746.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k0; Microsoft_FStar_Absyn_Syntax.p = _37_746.Microsoft_FStar_Absyn_Syntax.p})
in (pkg (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t))) a.Microsoft_FStar_Absyn_Syntax.sort)))
end
| _37_750 -> begin
(let _108_337 = (let _108_336 = (Support.Microsoft.FStar.Range.string_of_range p.Microsoft_FStar_Absyn_Syntax.p)
in (let _108_335 = (Microsoft_FStar_Absyn_Print.pat_to_string p)
in (let _108_334 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _108_336 _108_335 _108_334))))
in (Support.All.failwith _108_337))
end))))
in (match ((p.Microsoft_FStar_Absyn_Syntax.v, exps)) with
| (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps), _37_754) when ((Support.List.length ps) = (Support.List.length exps)) -> begin
(let ps = (Support.List.map2 aux ps exps)
in (let _108_339 = (Support.All.pipe_left (fun ( _108_338 ) -> Some (_108_338)) (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.tun)))
in (Microsoft_FStar_Absyn_Syntax.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_disj (ps)) _108_339 p.Microsoft_FStar_Absyn_Syntax.p)))
end
| (_37_758, e::[]) -> begin
(aux p e)
end
| _37_763 -> begin
(Support.All.failwith "Unexpected number of patterns")
end))))

let rec decorated_pattern_as_exp = (fun ( pat ) -> (let topt = (match (pat.Microsoft_FStar_Absyn_Syntax.sort) with
| Some (Support.Microsoft.FStar.Util.Inr (t)) -> begin
Some (t)
end
| None -> begin
None
end
| _37_770 -> begin
(Support.All.failwith "top-level pattern should be decorated with a type")
end)
in (let pkg = (fun ( f ) -> (f topt pat.Microsoft_FStar_Absyn_Syntax.p))
in (let pat_as_arg = (fun ( _37_777 ) -> (match (_37_777) with
| (p, i) -> begin
(let _37_780 = (decorated_pattern_as_either p)
in (match (_37_780) with
| (vars, te) -> begin
(let _108_359 = (let _108_358 = (Microsoft_FStar_Absyn_Syntax.as_implicit i)
in (te, _108_358))
in (vars, _108_359))
end))
end))
in (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_37_782) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _108_362 = (Support.All.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c) pkg)
in ([], _108_362))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_var (x)) -> begin
(let _108_365 = (Support.All.pipe_right (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar x) pkg)
in ((Support.Microsoft.FStar.Util.Inr (x))::[], _108_365))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _37_796 = (let _108_366 = (Support.All.pipe_right pats (Support.List.map pat_as_arg))
in (Support.All.pipe_right _108_366 Support.List.unzip))
in (match (_37_796) with
| (vars, args) -> begin
(let vars = (Support.List.flatten vars)
in (let _108_372 = (let _108_371 = (let _108_370 = (let _108_369 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (fv, q) (Some (fv.Microsoft_FStar_Absyn_Syntax.sort)) fv.Microsoft_FStar_Absyn_Syntax.p)
in (_108_369, args))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _108_370))
in (Support.All.pipe_right _108_371 pkg))
in (vars, _108_372)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)) -> begin
([], e)
end
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(Support.All.failwith "Impossible: expected a term pattern")
end)))))
and decorated_pattern_as_typ = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) -> begin
(let _108_374 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a (Some (a.Microsoft_FStar_Absyn_Syntax.sort)) p.Microsoft_FStar_Absyn_Syntax.p)
in ((Support.Microsoft.FStar.Util.Inl (a))::[], _108_374))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
([], t)
end
| _37_820 -> begin
(Support.All.failwith "Expected a type pattern")
end))
and decorated_pattern_as_either = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
(let _37_833 = (decorated_pattern_as_typ p)
in (match (_37_833) with
| (vars, t) -> begin
(vars, Support.Microsoft.FStar.Util.Inl (t))
end))
end
| _37_835 -> begin
(let _37_838 = (decorated_pattern_as_exp p)
in (match (_37_838) with
| (vars, e) -> begin
(vars, Support.Microsoft.FStar.Util.Inr (e))
end))
end))

let mk_basic_dtuple_type = (fun ( env ) ( n ) -> (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let l = (Microsoft_FStar_Absyn_Util.mk_dtuple_lid n r)
in (let k = (Microsoft_FStar_Tc_Env.lookup_typ_lid env l)
in (let t = (Microsoft_FStar_Absyn_Util.ftv l k)
in (let vars = (Microsoft_FStar_Tc_Env.binders env)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _37_854; Microsoft_FStar_Absyn_Syntax.pos = _37_852; Microsoft_FStar_Absyn_Syntax.fvs = _37_850; Microsoft_FStar_Absyn_Syntax.uvs = _37_848})) -> begin
(let _37_884 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _37_861 ) ( _37_865 ) -> (match ((_37_861, _37_865)) with
| ((out, subst), (b, _37_864)) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inr (_37_867) -> begin
(Support.All.failwith "impossible")
end
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let arg = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(let _108_382 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _108_382 Support.Prims.fst))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _108_385 = (let _108_384 = (let _108_383 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _108_383 Support.Prims.fst))
in (bs, _108_384))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _108_385 (Some (k)) r))
end
| _37_878 -> begin
(Support.All.failwith "Impossible")
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, arg)))::subst
in (let _108_387 = (let _108_386 = (Microsoft_FStar_Absyn_Syntax.targ arg)
in (_108_386)::out)
in (_108_387, subst)))))
end)
end)) ([], [])))
in (match (_37_884) with
| (args, _37_883) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, (Support.List.rev args)) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
end))
end
| _37_886 -> begin
(Support.All.failwith "Impossible")
end)))))))

let extract_lb_annotation = (fun ( env ) ( t ) ( e ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let mk_t_binder = (fun ( scope ) ( a ) -> (match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let k = (let _108_398 = (Microsoft_FStar_Tc_Rel.new_kvar e.Microsoft_FStar_Absyn_Syntax.pos scope)
in (Support.All.pipe_right _108_398 Support.Prims.fst))
in ((let _37_897 = a
in {Microsoft_FStar_Absyn_Syntax.v = _37_897.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _37_897.Microsoft_FStar_Absyn_Syntax.p}), false))
end
| _37_900 -> begin
(a, true)
end))
in (let mk_v_binder = (fun ( scope ) ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let t = (let _108_403 = (Microsoft_FStar_Tc_Rel.new_tvar e.Microsoft_FStar_Absyn_Syntax.pos scope Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _108_403 Support.Prims.fst))
in (match ((Microsoft_FStar_Absyn_Syntax.null_v_binder t)) with
| (Support.Microsoft.FStar.Util.Inr (x), _37_909) -> begin
(x, false)
end
| _37_912 -> begin
(Support.All.failwith "impos")
end))
end
| _37_914 -> begin
(match ((Microsoft_FStar_Absyn_Syntax.null_v_binder x.Microsoft_FStar_Absyn_Syntax.sort)) with
| (Support.Microsoft.FStar.Util.Inr (x), _37_918) -> begin
(x, true)
end
| _37_921 -> begin
(Support.All.failwith "impos")
end)
end))
in (let rec aux = (fun ( vars ) ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _37_927))) -> begin
(aux vars e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _37_934)) -> begin
(e, t, true)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _37_963 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _37_944 ) ( b ) -> (match (_37_944) with
| (scope, bs, check) -> begin
(match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _37_950 = (mk_t_binder scope a)
in (match (_37_950) with
| (tb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inl (tb), (Support.Prims.snd b))
in (let bs = (Support.List.append bs ((b)::[]))
in (let scope = (Support.List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _37_958 = (mk_v_binder scope x)
in (match (_37_958) with
| (vb, c) -> begin
(let b = (Support.Microsoft.FStar.Util.Inr (vb), (Support.Prims.snd b))
in (scope, (Support.List.append bs ((b)::[])), (c || check)))
end))
end)
end)) (vars, [], false)))
in (match (_37_963) with
| (scope, bs, check) -> begin
(let _37_967 = (aux scope body)
in (match (_37_967) with
| (body, res, check_res) -> begin
(let c = (Microsoft_FStar_Absyn_Util.ml_comp res r)
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _37_970 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _108_411 = (Support.Microsoft.FStar.Range.string_of_range r)
in (let _108_410 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using type %s\n" _108_411 _108_410)))
end
| false -> begin
()
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (e, t, (check_res || check))))))
end))
end))
end
| _37_974 -> begin
(let _108_413 = (let _108_412 = (Microsoft_FStar_Tc_Rel.new_tvar r vars Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _108_412 Support.Prims.fst))
in (e, _108_413, false))
end))
in (let _108_414 = (Microsoft_FStar_Tc_Env.t_binders env)
in (aux _108_414 e))))))
end
| _37_976 -> begin
(e, t, false)
end))

type lcomp_with_binder =
(Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp)

let destruct_comp = (fun ( c ) -> (let _37_993 = (match (c.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _37_986)::(Support.Microsoft.FStar.Util.Inl (wlp), _37_981)::[] -> begin
(wp, wlp)
end
| _37_990 -> begin
(let _108_419 = (let _108_418 = (let _108_417 = (Support.List.map Microsoft_FStar_Absyn_Print.arg_to_string c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Support.All.pipe_right _108_417 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str _108_418))
in (Support.All.failwith _108_419))
end)
in (match (_37_993) with
| (wp, wlp) -> begin
(c.Microsoft_FStar_Absyn_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun ( c ) ( m ) ( lift ) -> (let _37_1001 = (destruct_comp c)
in (match (_37_1001) with
| (_37_998, wp, wlp) -> begin
(let _108_441 = (let _108_440 = (let _108_436 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _108_436))
in (let _108_439 = (let _108_438 = (let _108_437 = (lift c.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _108_437))
in (_108_438)::[])
in (_108_440)::_108_439))
in {Microsoft_FStar_Absyn_Syntax.effect_name = m; Microsoft_FStar_Absyn_Syntax.result_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _108_441; Microsoft_FStar_Absyn_Syntax.flags = []})
end)))

let norm_eff_name = (let cache = (Support.Microsoft.FStar.Util.smap_create 20)
in (fun ( env ) ( l ) -> (let rec find = (fun ( l ) -> (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some ((_37_1009, c)) -> begin
(let l = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c).Microsoft_FStar_Absyn_Syntax.effect_name
in (match ((find l)) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end))
end))
in (let res = (match ((Support.Microsoft.FStar.Util.smap_try_find cache l.Microsoft_FStar_Absyn_Syntax.str)) with
| Some (l) -> begin
l
end
| None -> begin
(match ((find l)) with
| None -> begin
l
end
| Some (m) -> begin
(let _37_1023 = (Support.Microsoft.FStar.Util.smap_add cache l.Microsoft_FStar_Absyn_Syntax.str m)
in m)
end)
end)
in res))))

let join_effects = (fun ( env ) ( l1 ) ( l2 ) -> (let _37_1034 = (let _108_455 = (norm_eff_name env l1)
in (let _108_454 = (norm_eff_name env l2)
in (Microsoft_FStar_Tc_Env.join env _108_455 _108_454)))
in (match (_37_1034) with
| (m, _37_1031, _37_1033) -> begin
m
end)))

let join_lcomp = (fun ( env ) ( c1 ) ( c2 ) -> (match (((Microsoft_FStar_Absyn_Syntax.lid_equals c1.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid) && (Microsoft_FStar_Absyn_Syntax.lid_equals c2.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid))) with
| true -> begin
Microsoft_FStar_Absyn_Const.effect_Tot_lid
end
| false -> begin
(join_effects env c1.Microsoft_FStar_Absyn_Syntax.eff_name c2.Microsoft_FStar_Absyn_Syntax.eff_name)
end))

let lift_and_destruct = (fun ( env ) ( c1 ) ( c2 ) -> (let c1 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _37_1046 = (Microsoft_FStar_Tc_Env.join env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (match (_37_1046) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env m)
in (let _37_1052 = (Microsoft_FStar_Tc_Env.wp_signature env md.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_37_1052) with
| (a, kwp) -> begin
(let _108_469 = (destruct_comp m1)
in (let _108_468 = (destruct_comp m2)
in ((md, a, kwp), _108_469, _108_468)))
end)))))
end)))))

let is_pure_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun ( env ) ( l ) -> (let l = (norm_eff_name env l)
in ((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_PURE_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_GHOST_lid))))

let mk_comp = (fun ( md ) ( result ) ( wp ) ( wlp ) ( flags ) -> (let _108_492 = (let _108_491 = (let _108_490 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _108_489 = (let _108_488 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_108_488)::[])
in (_108_490)::_108_489))
in {Microsoft_FStar_Absyn_Syntax.effect_name = md.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.result_typ = result; Microsoft_FStar_Absyn_Syntax.effect_args = _108_491; Microsoft_FStar_Absyn_Syntax.flags = flags})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _108_492)))

let lcomp_of_comp = (fun ( c0 ) -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c0)
in {Microsoft_FStar_Absyn_Syntax.eff_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.res_typ = c.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.cflags = c.Microsoft_FStar_Absyn_Syntax.flags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _37_1066 ) -> (match (()) with
| () -> begin
c0
end))}))

let subst_lcomp = (fun ( subst ) ( lc ) -> (let _37_1069 = lc
in (let _108_502 = (Microsoft_FStar_Absyn_Util.subst_typ subst lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1069.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _108_502; Microsoft_FStar_Absyn_Syntax.cflags = _37_1069.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _37_1071 ) -> (match (()) with
| () -> begin
(let _108_501 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Util.subst_comp subst _108_501))
end))})))

let is_function = (fun ( t ) -> (match ((let _108_505 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _108_505.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_37_1074) -> begin
true
end
| _37_1077 -> begin
false
end))

let return_value = (fun ( env ) ( t ) ( v ) -> (let c = (match ((Microsoft_FStar_Tc_Env.effect_decl_opt env Microsoft_FStar_Absyn_Const.effect_PURE_lid)) with
| None -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Some (m) -> begin
(let _37_1086 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (match (_37_1086) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _108_517 = (let _108_516 = (let _108_515 = (let _108_514 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _108_513 = (let _108_512 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (_108_512)::[])
in (_108_514)::_108_513))
in (m.Microsoft_FStar_Absyn_Syntax.ret, _108_515))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_516 (Some (k)) v.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env) _108_517))
in (let wlp = wp
in (mk_comp m t wp wlp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[])))))
end))
end)
in (let _37_1091 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _108_520 = (Support.Microsoft.FStar.Range.string_of_range v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _108_519 = (Microsoft_FStar_Absyn_Print.exp_to_string v)
in (let _108_518 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) returning %s at comp type %s\n" _108_520 _108_519 _108_518))))
end
| false -> begin
()
end)
in c)))

let bind = (fun ( env ) ( e1opt ) ( lc1 ) ( _37_1098 ) -> (match (_37_1098) with
| (b, lc2) -> begin
(let _37_1109 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_1102))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| _37_1107 -> begin
"??"
end)
in (let _108_530 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc1)
in (let _108_529 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc2)
in (Support.Microsoft.FStar.Util.fprint3 "Before lift: Making bind c1=%s\nb=%s\t\tc2=%s\n" _108_530 bstr _108_529))))
end
| false -> begin
()
end)
in (let bind_it = (fun ( _37_1112 ) -> (match (()) with
| () -> begin
(let c1 = (lc1.Microsoft_FStar_Absyn_Syntax.comp ())
in (let c2 = (lc2.Microsoft_FStar_Absyn_Syntax.comp ())
in (let try_simplify = (fun ( _37_1116 ) -> (match (()) with
| () -> begin
(let aux = (fun ( _37_1118 ) -> (match (()) with
| () -> begin
(match ((Microsoft_FStar_Absyn_Util.is_trivial_wp c1)) with
| true -> begin
(match (b) with
| None -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid (_37_1121)) -> begin
Some (c2)
end
| Some (Microsoft_FStar_Tc_Env.Binding_var (_37_1125)) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_ml_comp c2)) with
| true -> begin
Some (c2)
end
| false -> begin
None
end)
end
| _37_1129 -> begin
None
end)
end
| false -> begin
(match (((Microsoft_FStar_Absyn_Util.is_ml_comp c1) && (Microsoft_FStar_Absyn_Util.is_ml_comp c2))) with
| true -> begin
Some (c2)
end
| false -> begin
None
end)
end)
end))
in (match ((e1opt, b)) with
| (Some (e), Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_1134)))) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp c1) && (not ((Microsoft_FStar_Absyn_Syntax.is_null_bvd x))))) with
| true -> begin
(let _108_538 = (Microsoft_FStar_Absyn_Util.subst_comp ((Support.Microsoft.FStar.Util.Inr ((x, e)))::[]) c2)
in (Support.All.pipe_left (fun ( _108_537 ) -> Some (_108_537)) _108_538))
end
| false -> begin
(aux ())
end)
end
| _37_1140 -> begin
(aux ())
end))
end))
in (match ((try_simplify ())) with
| Some (c) -> begin
(let _37_1158 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("bind")))) with
| true -> begin
(let _108_542 = (match (b) with
| None -> begin
"None"
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, _37_1146))) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, _37_1152))) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| _37_1157 -> begin
"Something else"
end)
in (let _108_541 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _108_540 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (let _108_539 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint4 "bind (%s) %s and %s simplified to %s\n" _108_542 _108_541 _108_540 _108_539)))))
end
| false -> begin
()
end)
in c)
end
| None -> begin
(let _37_1173 = (lift_and_destruct env c1 c2)
in (match (_37_1173) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
(let _108_543 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_108_543)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t1))) -> begin
(let _108_544 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t1))
in (_108_544)::[])
end
| Some (Microsoft_FStar_Tc_Env.Binding_lid ((l, t1))) -> begin
(let _108_545 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t1)
in (_108_545)::[])
end
| _37_1186 -> begin
(Support.All.failwith "Unexpected type-variable binding")
end)
in (let mk_lam = (fun ( wp ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wp_args = (let _108_560 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _108_559 = (let _108_558 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _108_557 = (let _108_556 = (Microsoft_FStar_Absyn_Syntax.targ wp1)
in (let _108_555 = (let _108_554 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _108_553 = (let _108_552 = (let _108_548 = (mk_lam wp2)
in (Microsoft_FStar_Absyn_Syntax.targ _108_548))
in (let _108_551 = (let _108_550 = (let _108_549 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _108_549))
in (_108_550)::[])
in (_108_552)::_108_551))
in (_108_554)::_108_553))
in (_108_556)::_108_555))
in (_108_558)::_108_557))
in (_108_560)::_108_559))
in (let wlp_args = (let _108_568 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _108_567 = (let _108_566 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (let _108_565 = (let _108_564 = (Microsoft_FStar_Absyn_Syntax.targ wlp1)
in (let _108_563 = (let _108_562 = (let _108_561 = (mk_lam wlp2)
in (Microsoft_FStar_Absyn_Syntax.targ _108_561))
in (_108_562)::[])
in (_108_564)::_108_563))
in (_108_566)::_108_565))
in (_108_568)::_108_567))
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t2)))::[]) kwp)
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wp, wp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let wlp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (md.Microsoft_FStar_Absyn_Syntax.bind_wlp, wlp_args) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end))))
end))
in (let _108_569 = (join_lcomp env lc1 lc2)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _108_569; Microsoft_FStar_Absyn_Syntax.res_typ = lc2.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_it})))
end))

let lift_formula = (fun ( env ) ( t ) ( mk_wp ) ( mk_wlp ) ( f ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let _37_1204 = (Microsoft_FStar_Tc_Env.wp_signature env md_pure.Microsoft_FStar_Absyn_Syntax.mname)
in (match (_37_1204) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let wp = (let _108_584 = (let _108_583 = (let _108_582 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _108_581 = (let _108_580 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_108_580)::[])
in (_108_582)::_108_581))
in (mk_wp, _108_583))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_584 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _108_589 = (let _108_588 = (let _108_587 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _108_586 = (let _108_585 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (_108_585)::[])
in (_108_587)::_108_586))
in (mk_wlp, _108_588))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_589 (Some (k)) f.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md_pure Microsoft_FStar_Tc_Recheck.t_unit wp wlp []))))
end))))

let unlabel = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, None, t.Microsoft_FStar_Absyn_Syntax.pos)))))

let refresh_comp_label = (fun ( env ) ( b ) ( lc ) -> (let refresh = (fun ( _37_1213 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_37_1216) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _37_1220 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _108_601 = (let _108_600 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _108_600))
in (Support.Microsoft.FStar.Util.fprint1 "Refreshing label at %s\n" _108_601))
end
| false -> begin
()
end)
in (let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1223 = (match (((Support.All.pipe_left Support.Prims.op_Negation (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name c'.Microsoft_FStar_Absyn_Syntax.effect_name)) && (Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low))) with
| true -> begin
(let _108_604 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _108_603 = (let _108_602 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c')
in (Support.All.pipe_left Microsoft_FStar_Absyn_Print.comp_typ_to_string _108_602))
in (Support.Microsoft.FStar.Util.fprint2 "To refresh, normalized\n\t%s\nto\n\t%s\n" _108_604 _108_603)))
end
| false -> begin
()
end)
in (let _37_1228 = (destruct_comp c')
in (match (_37_1228) with
| (t, wp, wlp) -> begin
(let wp = (let _108_607 = (let _108_606 = (let _108_605 = (Microsoft_FStar_Tc_Env.get_range env)
in (wp, Some (b), _108_605))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_108_606))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _108_607))
in (let wlp = (let _108_610 = (let _108_609 = (let _108_608 = (Microsoft_FStar_Tc_Env.get_range env)
in (wlp, Some (b), _108_608))
in Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_108_609))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _108_610))
in (let _108_615 = (let _37_1231 = c'
in (let _108_614 = (let _108_613 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (let _108_612 = (let _108_611 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_108_611)::[])
in (_108_613)::_108_612))
in {Microsoft_FStar_Absyn_Syntax.effect_name = _37_1231.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _37_1231.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _108_614; Microsoft_FStar_Absyn_Syntax.flags = c'.Microsoft_FStar_Absyn_Syntax.flags}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _108_615))))
end)))))
end)
end))
end))
in (let _37_1233 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1233.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1233.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _37_1233.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = refresh})))

let label = (fun ( reason ) ( r ) ( f ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((f, reason, r, true)))))

let label_opt = (fun ( env ) ( reason ) ( r ) ( f ) -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
(match ((let _108_639 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.pipe_left Support.Prims.op_Negation _108_639))) with
| true -> begin
f
end
| false -> begin
(let _108_640 = (reason ())
in (label _108_640 r f))
end)
end))

let label_guard = (fun ( reason ) ( r ) ( g ) -> (match (g) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
g
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _108_647 = (label reason r f)
in Microsoft_FStar_Tc_Rel.NonTrivial (_108_647))
end))

let weaken_guard = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| (Microsoft_FStar_Tc_Rel.NonTrivial (f1), Microsoft_FStar_Tc_Rel.NonTrivial (f2)) -> begin
(let g = (Microsoft_FStar_Absyn_Util.mk_imp f1 f2)
in Microsoft_FStar_Tc_Rel.NonTrivial (g))
end
| _37_1260 -> begin
g2
end))

let weaken_precondition = (fun ( env ) ( lc ) ( f ) -> (let weaken = (fun ( _37_1265 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match (f) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
c
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1274 = (destruct_comp c)
in (match (_37_1274) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (let _108_666 = (let _108_665 = (let _108_664 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_663 = (let _108_662 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _108_661 = (let _108_660 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_108_660)::[])
in (_108_662)::_108_661))
in (_108_664)::_108_663))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _108_665))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_666 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _108_673 = (let _108_672 = (let _108_671 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_670 = (let _108_669 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _108_668 = (let _108_667 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_108_667)::[])
in (_108_669)::_108_668))
in (_108_671)::_108_670))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _108_672))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_673 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end)))
end)
end))
end))
in (let _37_1278 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1278.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1278.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _37_1278.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = weaken})))

let strengthen_precondition = (fun ( reason ) ( env ) ( e ) ( lc ) ( g0 ) -> (match ((Microsoft_FStar_Tc_Rel.is_trivial g0)) with
| true -> begin
(lc, g0)
end
| false -> begin
(let flags = (Support.All.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _37_8 ) -> (match (_37_8) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _37_1289 -> begin
[]
end))))
in (let strengthen = (fun ( _37_1292 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let g0 = (Microsoft_FStar_Tc_Rel.simplify_guard env g0)
in (match ((Microsoft_FStar_Tc_Rel.guard_f g0)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
c
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let c = (match ((((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp c) && (not ((is_function (Microsoft_FStar_Absyn_Util.comp_result c))))) && (not ((Microsoft_FStar_Absyn_Util.is_partial_return c))))) with
| true -> begin
(let x = (Microsoft_FStar_Absyn_Util.gen_bvar (Microsoft_FStar_Absyn_Util.comp_result c))
in (let xret = (let _108_695 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (return_value env x.Microsoft_FStar_Absyn_Syntax.sort _108_695))
in (let xbinding = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
in (let lc = (let _108_698 = (lcomp_of_comp c)
in (let _108_697 = (let _108_696 = (lcomp_of_comp xret)
in (Some (xbinding), _108_696))
in (bind env (Some (e)) _108_698 _108_697)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ())))))
end
| false -> begin
c
end)
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1307 = (destruct_comp c)
in (match (_37_1307) with
| (res_t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (let _108_707 = (let _108_706 = (let _108_705 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_704 = (let _108_703 = (let _108_700 = (let _108_699 = (Microsoft_FStar_Tc_Env.get_range env)
in (label_opt env reason _108_699 f))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _108_700))
in (let _108_702 = (let _108_701 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_108_701)::[])
in (_108_703)::_108_702))
in (_108_705)::_108_704))
in (md.Microsoft_FStar_Absyn_Syntax.assert_p, _108_706))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_707 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _108_714 = (let _108_713 = (let _108_712 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_711 = (let _108_710 = (Microsoft_FStar_Absyn_Syntax.targ f)
in (let _108_709 = (let _108_708 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_108_708)::[])
in (_108_710)::_108_709))
in (_108_712)::_108_711))
in (md.Microsoft_FStar_Absyn_Syntax.assume_p, _108_713))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_714 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2))))
end))))
end)))
end))
in (let _108_718 = (let _37_1312 = lc
in (let _108_717 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _108_716 = (match (((Microsoft_FStar_Absyn_Util.is_pure_lcomp lc) && (let _108_715 = (Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.All.pipe_left Support.Prims.op_Negation _108_715)))) with
| true -> begin
flags
end
| false -> begin
[]
end)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _108_717; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1312.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _108_716; Microsoft_FStar_Absyn_Syntax.comp = strengthen})))
in (_108_718, (let _37_1314 = g0
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _37_1314.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _37_1314.Microsoft_FStar_Tc_Rel.implicits})))))
end))

let add_equality_to_post_condition = (fun ( env ) ( comp ) ( res_t ) -> (let md_pure = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let y = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _37_1324 = (let _108_726 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (let _108_725 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (_108_726, _108_725)))
in (match (_37_1324) with
| (xexp, yexp) -> begin
(let yret = (let _108_731 = (let _108_730 = (let _108_729 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_728 = (let _108_727 = (Microsoft_FStar_Absyn_Syntax.varg yexp)
in (_108_727)::[])
in (_108_729)::_108_728))
in (md_pure.Microsoft_FStar_Absyn_Syntax.ret, _108_730))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_731 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let x_eq_y_yret = (let _108_739 = (let _108_738 = (let _108_737 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_736 = (let _108_735 = (let _108_732 = (Microsoft_FStar_Absyn_Util.mk_eq res_t res_t xexp yexp)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _108_732))
in (let _108_734 = (let _108_733 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ yret)
in (_108_733)::[])
in (_108_735)::_108_734))
in (_108_737)::_108_736))
in (md_pure.Microsoft_FStar_Absyn_Syntax.assume_p, _108_738))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_739 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let forall_y_x_eq_y_yret = (let _108_750 = (let _108_749 = (let _108_748 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_747 = (let _108_746 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_745 = (let _108_744 = (let _108_743 = (let _108_742 = (let _108_741 = (let _108_740 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_108_740)::[])
in (_108_741, x_eq_y_yret))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _108_742 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _108_743))
in (_108_744)::[])
in (_108_746)::_108_745))
in (_108_748)::_108_747))
in (md_pure.Microsoft_FStar_Absyn_Syntax.close_wp, _108_749))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_750 None res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (let lc = (let _108_753 = (lcomp_of_comp comp)
in (let _108_752 = (let _108_751 = (lcomp_of_comp lc2)
in (Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))), _108_751))
in (bind env None _108_753 _108_752)))
in (lc.Microsoft_FStar_Absyn_Syntax.comp ()))))))
end))))))

let ite = (fun ( env ) ( guard ) ( lcomp_then ) ( lcomp_else ) -> (let comp = (fun ( _37_1335 ) -> (match (()) with
| () -> begin
(let _37_1351 = (let _108_765 = (lcomp_then.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _108_764 = (lcomp_else.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _108_765 _108_764)))
in (match (_37_1351) with
| ((md, _37_1338, _37_1340), (res_t, wp_then, wlp_then), (_37_1347, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _108_785 = (let _108_783 = (let _108_782 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_781 = (let _108_780 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _108_779 = (let _108_778 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _108_777 = (let _108_776 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_108_776)::[])
in (_108_778)::_108_777))
in (_108_780)::_108_779))
in (_108_782)::_108_781))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _108_783))
in (let _108_784 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_785 None _108_784))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end
| false -> begin
(let wp = (let _108_792 = (let _108_791 = (let _108_790 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_789 = (let _108_788 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _108_787 = (let _108_786 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_108_786)::[])
in (_108_788)::_108_787))
in (_108_790)::_108_789))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _108_791))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_792 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _108_797 = (let _108_796 = (let _108_795 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_794 = (let _108_793 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_108_793)::[])
in (_108_795)::_108_794))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _108_796))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_797 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _108_798 = (join_effects env lcomp_then.Microsoft_FStar_Absyn_Syntax.eff_name lcomp_else.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _108_798; Microsoft_FStar_Absyn_Syntax.res_typ = lcomp_then.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = comp})))

let bind_cases = (fun ( env ) ( res_t ) ( lcases ) -> (let eff = (match (lcases) with
| [] -> begin
(Support.All.failwith "Empty cases!")
end
| hd::tl -> begin
(Support.List.fold_left (fun ( eff ) ( _37_1374 ) -> (match (_37_1374) with
| (_37_1372, lc) -> begin
(join_effects env eff lc.Microsoft_FStar_Absyn_Syntax.eff_name)
end)) (Support.Prims.snd hd).Microsoft_FStar_Absyn_Syntax.eff_name tl)
end)
in (let bind_cases = (fun ( _37_1377 ) -> (match (()) with
| () -> begin
(let ifthenelse = (fun ( md ) ( res_t ) ( g ) ( wp_t ) ( wp_e ) -> (let _108_828 = (let _108_826 = (let _108_825 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_824 = (let _108_823 = (Microsoft_FStar_Absyn_Syntax.targ g)
in (let _108_822 = (let _108_821 = (Microsoft_FStar_Absyn_Syntax.targ wp_t)
in (let _108_820 = (let _108_819 = (Microsoft_FStar_Absyn_Syntax.targ wp_e)
in (_108_819)::[])
in (_108_821)::_108_820))
in (_108_823)::_108_822))
in (_108_825)::_108_824))
in (md.Microsoft_FStar_Absyn_Syntax.if_then_else, _108_826))
in (let _108_827 = (Support.Microsoft.FStar.Range.union_ranges wp_t.Microsoft_FStar_Absyn_Syntax.pos wp_e.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_828 None _108_827))))
in (let default_case = (let post_k = (let _108_831 = (let _108_830 = (let _108_829 = (Microsoft_FStar_Absyn_Syntax.null_v_binder res_t)
in (_108_829)::[])
in (_108_830, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _108_831 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let kwp = (let _108_834 = (let _108_833 = (let _108_832 = (Microsoft_FStar_Absyn_Syntax.null_t_binder post_k)
in (_108_832)::[])
in (_108_833, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _108_834 res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let post = (let _108_835 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _108_835 post_k))
in (let wp = (let _108_842 = (let _108_841 = (let _108_836 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_108_836)::[])
in (let _108_840 = (let _108_839 = (let _108_837 = (Microsoft_FStar_Tc_Env.get_range env)
in (label Microsoft_FStar_Tc_Errors.exhaustiveness_check _108_837))
in (let _108_838 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_left _108_839 _108_838)))
in (_108_841, _108_840)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _108_842 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _108_846 = (let _108_845 = (let _108_843 = (Microsoft_FStar_Absyn_Syntax.t_binder post)
in (_108_843)::[])
in (let _108_844 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_108_845, _108_844)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _108_846 (Some (kwp)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (Support.List.fold_right (fun ( _37_1393 ) ( celse ) -> (match (_37_1393) with
| (g, cthen) -> begin
(let _37_1411 = (let _108_849 = (cthen.Microsoft_FStar_Absyn_Syntax.comp ())
in (lift_and_destruct env _108_849 celse))
in (match (_37_1411) with
| ((md, _37_1397, _37_1399), (_37_1402, wp_then, wlp_then), (_37_1407, wp_else, wlp_else)) -> begin
(let _108_851 = (ifthenelse md res_t g wp_then wp_else)
in (let _108_850 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _108_851 _108_850 [])))
end))
end)) lcases default_case)
in (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(add_equality_to_post_condition env comp res_t)
end
| false -> begin
(let comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env comp.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _37_1419 = (destruct_comp comp)
in (match (_37_1419) with
| (_37_1416, wp, wlp) -> begin
(let wp = (let _108_858 = (let _108_857 = (let _108_856 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_855 = (let _108_854 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (let _108_853 = (let _108_852 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_108_852)::[])
in (_108_854)::_108_853))
in (_108_856)::_108_855))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wp, _108_857))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_858 None wp.Microsoft_FStar_Absyn_Syntax.pos))
in (let wlp = (let _108_863 = (let _108_862 = (let _108_861 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_860 = (let _108_859 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_108_859)::[])
in (_108_861)::_108_860))
in (md.Microsoft_FStar_Absyn_Syntax.ite_wlp, _108_862))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_863 None wlp.Microsoft_FStar_Absyn_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {Microsoft_FStar_Absyn_Syntax.eff_name = eff; Microsoft_FStar_Absyn_Syntax.res_typ = res_t; Microsoft_FStar_Absyn_Syntax.cflags = []; Microsoft_FStar_Absyn_Syntax.comp = bind_cases})))

let close_comp = (fun ( env ) ( bindings ) ( lc ) -> (let close = (fun ( _37_1426 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((Microsoft_FStar_Absyn_Util.is_ml_comp c)) with
| true -> begin
c
end
| false -> begin
(let close_wp = (fun ( md ) ( res_t ) ( bindings ) ( wp0 ) -> (Support.List.fold_right (fun ( b ) ( wp ) -> (match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let bs = (let _108_882 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_108_882)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _108_889 = (let _108_888 = (let _108_887 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_886 = (let _108_885 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _108_884 = (let _108_883 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_108_883)::[])
in (_108_885)::_108_884))
in (_108_887)::_108_886))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp, _108_888))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_889 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let bs = (let _108_890 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_108_890)::[])
in (let wp = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, wp) None wp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _108_895 = (let _108_894 = (let _108_893 = (Microsoft_FStar_Absyn_Syntax.targ res_t)
in (let _108_892 = (let _108_891 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_108_891)::[])
in (_108_893)::_108_892))
in (md.Microsoft_FStar_Absyn_Syntax.close_wp_t, _108_894))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_895 None wp0.Microsoft_FStar_Absyn_Syntax.pos))))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((l, t)) -> begin
wp
end
| Microsoft_FStar_Tc_Env.Binding_sig (s) -> begin
(Support.All.failwith "impos")
end)) bindings wp0))
in (let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1457 = (destruct_comp c)
in (match (_37_1457) with
| (t, wp, wlp) -> begin
(let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let wp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wp)
in (let wlp = (close_wp md c.Microsoft_FStar_Absyn_Syntax.result_typ bindings wlp)
in (mk_comp md c.Microsoft_FStar_Absyn_Syntax.result_typ wp wlp c.Microsoft_FStar_Absyn_Syntax.flags))))
end))))
end))
end))
in (let _37_1461 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1461.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1461.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = _37_1461.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term = (fun ( env ) ( e ) ( lc ) -> (let refine = (fun ( _37_1467 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (match ((not ((is_pure_or_ghost_effect env lc.Microsoft_FStar_Absyn_Syntax.eff_name)))) with
| true -> begin
c
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Util.is_partial_return c)) with
| true -> begin
c
end
| false -> begin
(let c = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let t = c.Microsoft_FStar_Absyn_Syntax.result_typ
in (let c = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (let ret = (let _108_904 = (return_value env t xexp)
in (Support.All.pipe_left lcomp_of_comp _108_904))
in (let eq_ret = (let _108_906 = (let _108_905 = (Microsoft_FStar_Absyn_Util.mk_eq t t xexp e)
in Microsoft_FStar_Tc_Rel.NonTrivial (_108_905))
in (weaken_precondition env ret _108_906))
in (let _108_909 = (let _108_908 = (let _108_907 = (lcomp_of_comp c)
in (bind env None _108_907 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, t))), eq_ret)))
in (_108_908.Microsoft_FStar_Absyn_Syntax.comp ()))
in (Microsoft_FStar_Absyn_Util.comp_set_flags _108_909 ((Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::(Microsoft_FStar_Absyn_Util.comp_flags c)))))))))))
end)
end))
end))
in (let flags = (match ((((not ((Microsoft_FStar_Absyn_Util.is_function_typ lc.Microsoft_FStar_Absyn_Syntax.res_typ))) && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp lc)) && (not ((Microsoft_FStar_Absyn_Util.is_lcomp_partial_return lc))))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::lc.Microsoft_FStar_Absyn_Syntax.cflags
end
| false -> begin
lc.Microsoft_FStar_Absyn_Syntax.cflags
end)
in (let _37_1477 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1477.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = _37_1477.Microsoft_FStar_Absyn_Syntax.res_typ; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = refine}))))

let check_comp = (fun ( env ) ( e ) ( c ) ( c' ) -> (match ((Microsoft_FStar_Tc_Rel.sub_comp env c c')) with
| None -> begin
(let _108_921 = (let _108_920 = (let _108_919 = (Microsoft_FStar_Tc_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _108_918 = (Microsoft_FStar_Tc_Env.get_range env)
in (_108_919, _108_918)))
in Microsoft_FStar_Absyn_Syntax.Error (_108_920))
in (raise (_108_921)))
end
| Some (g) -> begin
(e, c', g)
end))

let maybe_instantiate_typ = (fun ( env ) ( t ) ( k ) -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (match ((not ((env.Microsoft_FStar_Tc_Env.instantiate_targs && env.Microsoft_FStar_Tc_Env.instantiate_vargs)))) with
| true -> begin
(t, k, [])
end
| false -> begin
(match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let rec aux = (fun ( subst ) ( _37_9 ) -> (match (_37_9) with
| (Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1507 = (new_implicit_tvar env k)
in (match (_37_1507) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _37_1513 = (aux subst rest)
in (match (_37_1513) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1524 = (new_implicit_evar env t)
in (match (_37_1524) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _37_1530 = (aux subst rest)
in (match (_37_1530) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _37_1536 = (aux [] bs)
in (match (_37_1536) with
| (args, bs, subst, implicits) -> begin
(let k = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow' (bs, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind subst k)
in (let _108_932 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (t, args) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_108_932, k, implicits))))
end)))
end
| _37_1540 -> begin
(t, k, [])
end)
end)))

let maybe_instantiate = (fun ( env ) ( e ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match ((not ((env.Microsoft_FStar_Tc_Env.instantiate_targs && env.Microsoft_FStar_Tc_Env.instantiate_vargs)))) with
| true -> begin
(e, t, [])
end
| false -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let rec aux = (fun ( subst ) ( _37_10 ) -> (match (_37_10) with
| (Support.Microsoft.FStar.Util.Inl (a), _37_1556)::rest -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1562 = (new_implicit_tvar env k)
in (match (_37_1562) with
| (t, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _37_1568 = (aux subst rest)
in (match (_37_1568) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inl (u))::us)
end)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _37_1579 = (new_implicit_evar env t)
in (match (_37_1579) with
| (v, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v)))::subst
in (let _37_1585 = (aux subst rest)
in (match (_37_1585) with
| (args, bs, subst, us) -> begin
(((Support.Microsoft.FStar.Util.Inr (v), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::args, bs, subst, (Support.Microsoft.FStar.Util.Inr (u))::us)
end)))
end)))
end
| bs -> begin
([], bs, subst, [])
end))
in (let _37_1591 = (aux [] bs)
in (match (_37_1591) with
| (args, bs, subst, implicits) -> begin
(let mk_exp_app = (fun ( e ) ( args ) ( t ) -> (match (args) with
| [] -> begin
e
end
| _37_1598 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) t e.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (match (bs) with
| [] -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_comp c)) with
| true -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst (Microsoft_FStar_Absyn_Util.comp_result c))
in (let _108_949 = (mk_exp_app e args (Some (t)))
in (_108_949, t, implicits)))
end
| false -> begin
(e, t, [])
end)
end
| _37_1602 -> begin
(let t = (let _108_950 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _108_950 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _108_951 = (mk_exp_app e args (Some (t)))
in (_108_951, t, implicits)))
end))
end)))
end
| _37_1605 -> begin
(e, t, [])
end)
end)))

let weaken_result_typ = (fun ( env ) ( e ) ( lc ) ( t ) -> (let gopt = (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(let _108_960 = (Microsoft_FStar_Tc_Rel.try_teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_108_960, false))
end
| false -> begin
(let _108_961 = (Microsoft_FStar_Tc_Rel.try_subtype env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
in (_108_961, true))
end)
in (match (gopt) with
| (None, _37_1613) -> begin
(Microsoft_FStar_Tc_Rel.subtype_fail env lc.Microsoft_FStar_Absyn_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(let g = (Microsoft_FStar_Tc_Rel.simplify_guard env g)
in (match ((Microsoft_FStar_Tc_Rel.guard_f g)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
(let lc = (let _37_1621 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _37_1621.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = _37_1621.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = _37_1621.Microsoft_FStar_Absyn_Syntax.comp})
in (e, lc, g))
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let g = (let _37_1626 = g
in {Microsoft_FStar_Tc_Rel.guard_f = Microsoft_FStar_Tc_Rel.Trivial; Microsoft_FStar_Tc_Rel.deferred = _37_1626.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _37_1626.Microsoft_FStar_Tc_Rel.implicits})
in (let strengthen = (fun ( _37_1630 ) -> (match (()) with
| () -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _37_1632 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _108_965 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (let _108_964 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env f)
in (Support.Microsoft.FStar.Util.fprint2 "Strengthening %s with guard %s\n" _108_965 _108_964)))
end
| false -> begin
()
end)
in (let ct = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _37_1637 = (Microsoft_FStar_Tc_Env.wp_signature env Microsoft_FStar_Absyn_Const.effect_PURE_lid)
in (match (_37_1637) with
| (a, kwp) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::[]) kwp)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env ct.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let x = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvd_to_exp x t)
in (let wp = (let _108_970 = (let _108_969 = (let _108_968 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _108_967 = (let _108_966 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_108_966)::[])
in (_108_968)::_108_967))
in (md.Microsoft_FStar_Absyn_Syntax.ret, _108_969))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_970 (Some (k)) xexp.Microsoft_FStar_Absyn_Syntax.pos))
in (let cret = (let _108_971 = (mk_comp md t wp wp ((Microsoft_FStar_Absyn_Syntax.RETURN)::[]))
in (Support.All.pipe_left lcomp_of_comp _108_971))
in (let guard = (match (apply_guard) with
| true -> begin
(let _108_974 = (let _108_973 = (let _108_972 = (Microsoft_FStar_Absyn_Syntax.varg xexp)
in (_108_972)::[])
in (f, _108_973))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_974 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) f.Microsoft_FStar_Absyn_Syntax.pos))
end
| false -> begin
f
end)
in (let _37_1647 = (let _108_982 = (Support.All.pipe_left (fun ( _108_979 ) -> Some (_108_979)) (Microsoft_FStar_Tc_Errors.subtyping_failed env lc.Microsoft_FStar_Absyn_Syntax.res_typ t))
in (let _108_981 = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _108_980 = (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (guard)))
in (strengthen_precondition _108_982 _108_981 e cret _108_980))))
in (match (_37_1647) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let c = (let _108_984 = (let _108_983 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ct)
in (Support.All.pipe_left lcomp_of_comp _108_983))
in (bind env (Some (e)) _108_984 (Some (Microsoft_FStar_Tc_Env.Binding_var ((x, lc.Microsoft_FStar_Absyn_Syntax.res_typ))), eq_ret)))
in (let c = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (let _37_1650 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _108_985 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env c)
in (Support.Microsoft.FStar.Util.fprint1 "Strengthened to %s\n" _108_985))
end
| false -> begin
()
end)
in c)))
end)))))))))
end)))))
end))
in (let flags = (Support.All.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.List.collect (fun ( _37_11 ) -> (match (_37_11) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
(Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN)::[]
end
| _37_1656 -> begin
[]
end))))
in (let lc = (let _37_1658 = lc
in (let _108_987 = (norm_eff_name env lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in {Microsoft_FStar_Absyn_Syntax.eff_name = _108_987; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = flags; Microsoft_FStar_Absyn_Syntax.comp = strengthen}))
in (e, lc, g)))))
end))
end)))

let check_uvars = (fun ( r ) ( t ) -> (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (match ((((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_e) + ((Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_t) + (Support.Microsoft.FStar.Util.set_count uvt.Microsoft_FStar_Absyn_Syntax.uvars_k))) > 0)) with
| true -> begin
(let ue = (let _108_992 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string _108_992))
in (let ut = (let _108_993 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_t_to_string _108_993))
in (let uk = (let _108_994 = (Support.Microsoft.FStar.Util.set_elements uvt.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.List.map Microsoft_FStar_Absyn_Print.uvar_k_to_string _108_994))
in (let union = (Support.String.concat "," (Support.List.append (Support.List.append ue ut) uk))
in (let hide_uvar_nums_saved = (Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (Support.ST.read Microsoft_FStar_Options.print_implicits)
in (let _37_1670 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums false)
in (let _37_1672 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits true)
in (let _37_1674 = (let _108_996 = (let _108_995 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" union _108_995))
in (Microsoft_FStar_Tc_Errors.report r _108_996))
in (let _37_1676 = (Support.ST.op_Colon_Equals Microsoft_FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (Support.ST.op_Colon_Equals Microsoft_FStar_Options.print_implicits print_implicits_saved)))))))))))
end
| false -> begin
()
end)))

let gen = (fun ( verify ) ( env ) ( ecs ) -> (match ((let _108_1004 = (Support.Microsoft.FStar.Util.for_all (fun ( _37_1684 ) -> (match (_37_1684) with
| (_37_1682, c) -> begin
(Microsoft_FStar_Absyn_Util.is_pure_comp c)
end)) ecs)
in (Support.All.pipe_left Support.Prims.op_Negation _108_1004))) with
| true -> begin
None
end
| false -> begin
(let norm = (fun ( c ) -> (let _37_1687 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _108_1007 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizing before generalizing:\n\t %s" _108_1007))
end
| false -> begin
()
end)
in (let steps = (Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::[]
in (let c = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
end
| false -> begin
(Microsoft_FStar_Tc_Normalize.norm_comp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Delta)::[]) env c)
end)
in (let _37_1691 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _108_1008 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.fprint1 "Normalized to:\n\t %s" _108_1008))
end
| false -> begin
()
end)
in c)))))
in (let env_uvars = (Microsoft_FStar_Tc_Env.uvars_in_env env)
in (let gen_uvars = (fun ( uvs ) -> (let _108_1011 = (Support.Microsoft.FStar.Util.set_difference uvs env_uvars.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.All.pipe_right _108_1011 Support.Microsoft.FStar.Util.set_elements)))
in (let should_gen = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _37_1700)) -> begin
(match ((Support.All.pipe_right bs (Support.Microsoft.FStar.Util.for_some (fun ( _37_12 ) -> (match (_37_12) with
| (Support.Microsoft.FStar.Util.Inl (_37_1705), _37_1708) -> begin
true
end
| _37_1711 -> begin
false
end))))) with
| true -> begin
false
end
| false -> begin
true
end)
end
| _37_1713 -> begin
true
end))
in (let uvars = (Support.All.pipe_right ecs (Support.List.map (fun ( _37_1716 ) -> (match (_37_1716) with
| (e, c) -> begin
(let t = (Support.All.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) Microsoft_FStar_Absyn_Util.compress_typ)
in (match ((let _108_1016 = (should_gen t)
in (Support.All.pipe_left Support.Prims.op_Negation _108_1016))) with
| true -> begin
([], e, c)
end
| false -> begin
(let c = (norm c)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let t = ct.Microsoft_FStar_Absyn_Syntax.result_typ
in (let uvt = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let uvs = (gen_uvars uvt.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _37_1732 = (match ((((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str) && verify) && (let _108_1017 = (Microsoft_FStar_Absyn_Util.is_total_comp c)
in (Support.All.pipe_left Support.Prims.op_Negation _108_1017)))) with
| true -> begin
(let _37_1728 = (destruct_comp ct)
in (match (_37_1728) with
| (_37_1724, wp, _37_1727) -> begin
(let binder = (let _108_1018 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_108_1018)::[])
in (let post = (let _108_1022 = (let _108_1019 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (binder, _108_1019))
in (let _108_1021 = (let _108_1020 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binder, Microsoft_FStar_Absyn_Syntax.ktype) t.Microsoft_FStar_Absyn_Syntax.pos)
in Some (_108_1020))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _108_1022 _108_1021 t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let vc = (let _108_1029 = (let _108_1028 = (let _108_1027 = (let _108_1026 = (let _108_1025 = (Microsoft_FStar_Absyn_Syntax.targ post)
in (_108_1025)::[])
in (wp, _108_1026))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_1027))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn wp.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _108_1028))
in (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env _108_1029))
in (let _108_1030 = (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (discharge_guard env _108_1030)))))
end))
end
| false -> begin
()
end)
in (uvs, e, c)))))))
end))
end))))
in (let ecs = (Support.All.pipe_right uvars (Support.List.map (fun ( _37_1738 ) -> (match (_37_1738) with
| (uvs, e, c) -> begin
(let tvars = (Support.All.pipe_right uvs (Support.List.map (fun ( _37_1741 ) -> (match (_37_1741) with
| (u, k) -> begin
(let a = (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) | (Microsoft_FStar_Absyn_Syntax.Fixed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a.Microsoft_FStar_Absyn_Syntax.v k)
end
| Microsoft_FStar_Absyn_Syntax.Fixed (_37_1779) -> begin
(Support.All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _37_1782 -> begin
(let a = (let _108_1035 = (let _108_1034 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_left (fun ( _108_1033 ) -> Some (_108_1033)) _108_1034))
in (Microsoft_FStar_Absyn_Util.new_bvd _108_1035))
in (let t = (let _108_1036 = (Microsoft_FStar_Absyn_Util.bvd_to_typ a Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.close_for_kind _108_1036 k))
in (let _37_1785 = (Microsoft_FStar_Absyn_Util.unchecked_unify u t)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a Microsoft_FStar_Absyn_Syntax.ktype))))
end)
in (Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))
end))))
in (let t = (match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) Microsoft_FStar_Absyn_Util.function_formals)) with
| Some ((bs, cod)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((Support.List.append tvars bs), cod) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
end
| None -> begin
(match (tvars) with
| [] -> begin
(Microsoft_FStar_Absyn_Util.comp_result c)
end
| _37_1796 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (tvars, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
end)
end)
in (let e = (match (tvars) with
| [] -> begin
e
end
| _37_1800 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (tvars, e) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _108_1037 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (e, _108_1037)))))
end))))
in Some (ecs)))))))
end))

let generalize = (fun ( verify ) ( env ) ( lecs ) -> (let _37_1812 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _108_1046 = (let _108_1045 = (Support.List.map (fun ( _37_1811 ) -> (match (_37_1811) with
| (lb, _37_1808, _37_1810) -> begin
(Microsoft_FStar_Absyn_Print.lbname_to_string lb)
end)) lecs)
in (Support.All.pipe_right _108_1045 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Generalizing: %s" _108_1046))
end
| false -> begin
()
end)
in (match ((let _108_1048 = (Support.All.pipe_right lecs (Support.List.map (fun ( _37_1818 ) -> (match (_37_1818) with
| (_37_1815, e, c) -> begin
(e, c)
end))))
in (gen verify env _108_1048))) with
| None -> begin
lecs
end
| Some (ecs) -> begin
(Support.List.map2 (fun ( _37_1827 ) ( _37_1830 ) -> (match ((_37_1827, _37_1830)) with
| ((l, _37_1824, _37_1826), (e, c)) -> begin
(let _37_1831 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _108_1053 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _108_1052 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _108_1051 = (Microsoft_FStar_Absyn_Print.typ_to_string (Microsoft_FStar_Absyn_Util.comp_result c))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Generalized %s to %s" _108_1053 _108_1052 _108_1051))))
end
| false -> begin
()
end)
in (l, e, c))
end)) lecs ecs)
end)))

let unresolved = (fun ( u ) -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Uvar -> begin
true
end
| _37_1836 -> begin
false
end))

let check_top_level = (fun ( env ) ( g ) ( lc ) -> (let discharge = (fun ( g ) -> (let _37_1842 = (Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
in (let _37_1860 = (match ((Support.All.pipe_right g.Microsoft_FStar_Tc_Rel.implicits (Support.List.tryFind (fun ( _37_13 ) -> (match (_37_13) with
| Support.Microsoft.FStar.Util.Inl (u) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr ((u, _37_1849)) -> begin
(unresolved u)
end))))) with
| Some (Support.Microsoft.FStar.Util.Inr ((_37_1853, r))) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unresolved implicit argument", r))))
end
| _37_1859 -> begin
()
end)
in (Microsoft_FStar_Absyn_Util.is_pure_lcomp lc))))
in (let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((Microsoft_FStar_Absyn_Util.is_total_lcomp lc)) with
| true -> begin
(let _108_1065 = (discharge g)
in (let _108_1064 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (_108_1065, _108_1064)))
end
| false -> begin
(let c = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (let steps = (Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::(Microsoft_FStar_Tc_Normalize.DeltaComp)::[]
in (let c = (let _108_1066 = (Microsoft_FStar_Tc_Normalize.norm_comp steps env c)
in (Support.All.pipe_right _108_1066 Microsoft_FStar_Absyn_Util.comp_to_comp_typ))
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _37_1871 = (destruct_comp c)
in (match (_37_1871) with
| (t, wp, _37_1870) -> begin
(let vc = (let _108_1072 = (let _108_1070 = (let _108_1069 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (let _108_1068 = (let _108_1067 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_108_1067)::[])
in (_108_1069)::_108_1068))
in (md.Microsoft_FStar_Absyn_Syntax.trivial, _108_1070))
in (let _108_1071 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_1072 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) _108_1071)))
in (let g = (let _108_1073 = (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula (Microsoft_FStar_Tc_Rel.NonTrivial (vc)))
in (Microsoft_FStar_Tc_Rel.conj_guard g _108_1073))
in (let _108_1075 = (discharge g)
in (let _108_1074 = (Microsoft_FStar_Absyn_Syntax.mk_Comp c)
in (_108_1075, _108_1074)))))
end))))))
end))))

let short_circuit_exp = (fun ( head ) ( seen_args ) -> (let short_bin_op_e = (fun ( f ) -> (fun ( _37_14 ) -> (match (_37_14) with
| [] -> begin
None
end
| (Support.Microsoft.FStar.Util.Inr (fst), _37_1883)::[] -> begin
(let _108_1094 = (f fst)
in (Support.All.pipe_right _108_1094 (fun ( _108_1093 ) -> Some (_108_1093))))
end
| _37_1887 -> begin
(Support.All.failwith "Unexpexted args to binary operator")
end)))
in (let table = (let op_and_e = (fun ( e ) -> (let _108_1100 = (Microsoft_FStar_Absyn_Util.b2t e)
in (_108_1100, Microsoft_FStar_Absyn_Const.exp_false_bool)))
in (let op_or_e = (fun ( e ) -> (let _108_1104 = (let _108_1103 = (Microsoft_FStar_Absyn_Util.b2t e)
in (Microsoft_FStar_Absyn_Util.mk_neg _108_1103))
in (_108_1104, Microsoft_FStar_Absyn_Const.exp_true_bool)))
in ((Microsoft_FStar_Absyn_Const.op_And, (short_bin_op_e op_and_e)))::((Microsoft_FStar_Absyn_Const.op_Or, (short_bin_op_e op_or_e)))::[]))
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _37_1895)) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _37_1901 ) -> (match (_37_1901) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _108_1122 = (mk seen_args)
in Some (_108_1122))
end
| false -> begin
None
end)
end)))) with
| None -> begin
None
end
| Some (g) -> begin
g
end))
end
| _37_1906 -> begin
None
end))))

let short_circuit_typ = (fun ( head ) ( seen_args ) -> (let short_bin_op_t = (fun ( f ) -> (fun ( _37_15 ) -> (match (_37_15) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (fst), _37_1916)::[] -> begin
(f fst)
end
| _37_1920 -> begin
(Support.All.failwith "Unexpexted args to binary operator")
end)))
in (let op_and_t = (fun ( t ) -> (let _108_1143 = (unlabel t)
in (Support.All.pipe_right _108_1143 (fun ( _108_1142 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_108_1142)))))
in (let op_or_t = (fun ( t ) -> (let _108_1148 = (let _108_1146 = (unlabel t)
in (Support.All.pipe_right _108_1146 Microsoft_FStar_Absyn_Util.mk_neg))
in (Support.All.pipe_right _108_1148 (fun ( _108_1147 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_108_1147)))))
in (let op_imp_t = (fun ( t ) -> (let _108_1152 = (unlabel t)
in (Support.All.pipe_right _108_1152 (fun ( _108_1151 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_108_1151)))))
in (let short_op_ite = (fun ( _37_16 ) -> (match (_37_16) with
| [] -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| (Support.Microsoft.FStar.Util.Inl (guard), _37_1932)::[] -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (guard)
end
| _then::(Support.Microsoft.FStar.Util.Inl (guard), _37_1938)::[] -> begin
(let _108_1156 = (Microsoft_FStar_Absyn_Util.mk_neg guard)
in (Support.All.pipe_right _108_1156 (fun ( _108_1155 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_108_1155))))
end
| _37_1943 -> begin
(Support.All.failwith "Unexpected args to ITE")
end))
in (let table = ((Microsoft_FStar_Absyn_Const.and_lid, (short_bin_op_t op_and_t)))::((Microsoft_FStar_Absyn_Const.or_lid, (short_bin_op_t op_or_t)))::((Microsoft_FStar_Absyn_Const.imp_lid, (short_bin_op_t op_imp_t)))::((Microsoft_FStar_Absyn_Const.ite_lid, short_op_ite))::[]
in (match (head) with
| Support.Microsoft.FStar.Util.Inr (head) -> begin
(match ((short_circuit_exp head seen_args)) with
| None -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| Some ((g, _37_1951)) -> begin
Microsoft_FStar_Tc_Rel.NonTrivial (g)
end)
end
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (fv); Microsoft_FStar_Absyn_Syntax.tk = _37_1961; Microsoft_FStar_Absyn_Syntax.pos = _37_1959; Microsoft_FStar_Absyn_Syntax.fvs = _37_1957; Microsoft_FStar_Absyn_Syntax.uvs = _37_1955}) -> begin
(let lid = fv.Microsoft_FStar_Absyn_Syntax.v
in (match ((Support.Microsoft.FStar.Util.find_map table (fun ( _37_1969 ) -> (match (_37_1969) with
| (x, mk) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals x lid)) with
| true -> begin
(let _108_1183 = (mk seen_args)
in Some (_108_1183))
end
| false -> begin
None
end)
end)))) with
| None -> begin
Microsoft_FStar_Tc_Rel.Trivial
end
| Some (g) -> begin
g
end))
end
| _37_1974 -> begin
Microsoft_FStar_Tc_Rel.Trivial
end))))))))

let pure_or_ghost_pre_and_post = (fun ( env ) ( comp ) -> (let mk_post_type = (fun ( res_t ) ( ens ) -> (let x = (Microsoft_FStar_Absyn_Util.gen_bvar res_t)
in (let _108_1197 = (let _108_1196 = (let _108_1195 = (let _108_1194 = (let _108_1193 = (let _108_1192 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Microsoft_FStar_Absyn_Syntax.varg _108_1192))
in (_108_1193)::[])
in (ens, _108_1194))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_1195 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))
in (x, _108_1196))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _108_1197 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) res_t.Microsoft_FStar_Absyn_Syntax.pos))))
in (let norm = (fun ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Delta)::(Microsoft_FStar_Tc_Normalize.Unlabel)::[]) env t))
in (match ((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp comp)) with
| true -> begin
(None, (Microsoft_FStar_Absyn_Util.comp_result comp))
end
| false -> begin
(match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_37_1984) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Pure_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Ghost_lid))) with
| true -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (req), _37_1999)::(Support.Microsoft.FStar.Util.Inl (ens), _37_1993)::_37_1989 -> begin
(let _108_1203 = (let _108_1200 = (norm req)
in Some (_108_1200))
in (let _108_1202 = (let _108_1201 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (Support.All.pipe_left norm _108_1201))
in (_108_1203, _108_1202)))
end
| _37_2003 -> begin
(Support.All.failwith "Impossible")
end)
end
| false -> begin
(let comp = (Microsoft_FStar_Tc_Normalize.norm_comp ((Microsoft_FStar_Tc_Normalize.DeltaComp)::[]) env comp)
in (match (comp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_37_2006) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp), _37_2021)::(Support.Microsoft.FStar.Util.Inl (wlp), _37_2015)::_37_2011 -> begin
(let _37_2033 = (match ((let _108_1205 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_requires)
in (let _108_1204 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env Microsoft_FStar_Absyn_Const.as_ensures)
in (_108_1205, _108_1204)))) with
| (Some (x), Some (y)) -> begin
(x, y)
end
| _37_2030 -> begin
(Support.All.failwith "Impossible")
end)
in (match (_37_2033) with
| (as_req, as_ens) -> begin
(let req = (let _108_1209 = (let _108_1208 = (let _108_1207 = (let _108_1206 = (Microsoft_FStar_Absyn_Syntax.targ wp)
in (_108_1206)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_108_1207)
in (as_req, _108_1208))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_1209 (Some (Microsoft_FStar_Absyn_Syntax.mk_Kind_type)) ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let ens = (let _108_1213 = (let _108_1212 = (let _108_1211 = (let _108_1210 = (Microsoft_FStar_Absyn_Syntax.targ wlp)
in (_108_1210)::[])
in ((Support.Microsoft.FStar.Util.Inl (ct.Microsoft_FStar_Absyn_Syntax.result_typ), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_108_1211)
in (as_ens, _108_1212))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _108_1213 None ct.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _108_1217 = (let _108_1214 = (norm req)
in Some (_108_1214))
in (let _108_1216 = (let _108_1215 = (mk_post_type ct.Microsoft_FStar_Absyn_Syntax.result_typ ens)
in (norm _108_1215))
in (_108_1217, _108_1216)))))
end))
end
| _37_2037 -> begin
(Support.All.failwith "Impossible")
end)
end))
end)
end)
end))))




