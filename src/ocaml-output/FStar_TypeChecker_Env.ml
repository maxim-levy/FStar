open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding 
  | Inlining 
  | DoNotUnfoldPureLets 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldFully of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | PureSubtermsWithinComputations 
  | Simplify 
  | EraseUniverses 
  | AllowUnboundUniverses 
  | Reify 
  | CompressUvars 
  | NoFullNorm 
  | CheckNoUvars 
  | Unmeta 
  | Unascribe 
  | NBE 
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Beta  -> true | uu____35 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____41 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____47 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____54 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____67 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____73 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____79 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____85 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____91 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____97 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____104 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____120 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____142 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____162 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____175 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____181 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____187 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____193 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____199 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____205 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____211 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____217 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____223 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____229 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____235 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____241 -> false 
type steps = step Prims.list
type sig_binding =
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
    FStar_Pervasives_Native.tuple2
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____260 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____266 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____272 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____279 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
    ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
    }
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
  
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
  
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
  
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list
    }
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
  
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
  
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__joins
  
type name_prefix = Prims.string Prims.list
type proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2
type goal = FStar_Syntax_Syntax.term
type env =
  {
  solver: solver_t ;
  range: FStar_Range.range ;
  curmodule: FStar_Ident.lident ;
  gamma: FStar_Syntax_Syntax.binding Prims.list ;
  gamma_sig: sig_binding Prims.list ;
  gamma_cache: cached_elt FStar_Util.smap ;
  modules: FStar_Syntax_Syntax.modul Prims.list ;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap ;
  attrtab: FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap ;
  is_pattern: Prims.bool ;
  instantiate_imp: Prims.bool ;
  effects: effects ;
  generalize: Prims.bool ;
  letrecs:
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
  top_level: Prims.bool ;
  check_uvars: Prims.bool ;
  use_eq: Prims.bool ;
  is_iface: Prims.bool ;
  admit: Prims.bool ;
  lax: Prims.bool ;
  lax_universes: Prims.bool ;
  phase1: Prims.bool ;
  failhard: Prims.bool ;
  nosynth: Prims.bool ;
  nocoerce: Prims.bool ;
  uvar_subtyping: Prims.bool ;
  tc_term:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  check_type_of:
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t
    ;
  use_bv_sorts: Prims.bool ;
  qtbl_name_and_index:
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
                                 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
    ;
  normalized_eff_names: FStar_Ident.lident FStar_Util.smap ;
  proof_ns: proof_namespace ;
  synth_hook:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  splice:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list ;
  is_native_tactic: FStar_Ident.lid -> Prims.bool ;
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref ;
  tc_hooks: tcenv_hooks ;
  dsenv: FStar_Syntax_DsEnv.env ;
  dep_graph: FStar_Parser_Dep.deps ;
  nbe:
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    }
and solver_t =
  {
  init: env -> unit ;
  push: Prims.string -> unit ;
  pop: Prims.string -> unit ;
  snapshot:
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2
    ;
  rollback:
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit
    ;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> unit ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> unit ;
  preprocess:
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
    ;
  solve:
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit
    ;
  finish: unit -> unit ;
  refresh: unit -> unit }
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula ;
  deferred: FStar_TypeChecker_Common.deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2
    ;
  implicits: implicit Prims.list }
and implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range ;
  imp_meta:
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
    }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit
    }
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__attrtab
  
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_pattern
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__generalize
  
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__admit
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} -> __fname__lax
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__nosynth
  
let (__proj__Mkenv__item__nocoerce : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__nocoerce
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__uvar_subtyping
  
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__tc_term
  
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__universe_of
  
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__use_bv_sorts
  
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
                                 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__normalized_eff_names
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__proof_ns
  
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__synth_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__splice
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__dsenv
  
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} ->
        __fname__dep_graph
  
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; nocoerce = __fname__nocoerce;
        uvar_subtyping = __fname__uvar_subtyping; tc_term = __fname__tc_term;
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph; nbe = __fname__nbe;_} -> __fname__nbe
  
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
  
let (__proj__Mksolver_t__item__snapshot :
  solver_t ->
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__snapshot
  
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__rollback
  
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_sig
  
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__preprocess
  
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__refresh
  
let (__proj__Mkguard_t__item__guard_f :
  guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
  
let (__proj__Mkguard_t__item__deferred :
  guard_t -> FStar_TypeChecker_Common.deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicit Prims.list) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_range
  
let (__proj__Mkimplicit__item__imp_meta :
  implicit ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_meta
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
  
type solver_depth_t =
  (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
type implicits = implicit Prims.list
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___220_10026  ->
              match uu___220_10026 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____10029 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____10029  in
                  let uu____10030 =
                    let uu____10031 = FStar_Syntax_Subst.compress y  in
                    uu____10031.FStar_Syntax_Syntax.n  in
                  (match uu____10030 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____10035 =
                         let uu___234_10036 = y1  in
                         let uu____10037 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___234_10036.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___234_10036.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____10037
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____10035
                   | uu____10040 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___235_10052 = env  in
      let uu____10053 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___235_10052.solver);
        range = (uu___235_10052.range);
        curmodule = (uu___235_10052.curmodule);
        gamma = uu____10053;
        gamma_sig = (uu___235_10052.gamma_sig);
        gamma_cache = (uu___235_10052.gamma_cache);
        modules = (uu___235_10052.modules);
        expected_typ = (uu___235_10052.expected_typ);
        sigtab = (uu___235_10052.sigtab);
        attrtab = (uu___235_10052.attrtab);
        is_pattern = (uu___235_10052.is_pattern);
        instantiate_imp = (uu___235_10052.instantiate_imp);
        effects = (uu___235_10052.effects);
        generalize = (uu___235_10052.generalize);
        letrecs = (uu___235_10052.letrecs);
        top_level = (uu___235_10052.top_level);
        check_uvars = (uu___235_10052.check_uvars);
        use_eq = (uu___235_10052.use_eq);
        is_iface = (uu___235_10052.is_iface);
        admit = (uu___235_10052.admit);
        lax = (uu___235_10052.lax);
        lax_universes = (uu___235_10052.lax_universes);
        phase1 = (uu___235_10052.phase1);
        failhard = (uu___235_10052.failhard);
        nosynth = (uu___235_10052.nosynth);
        nocoerce = (uu___235_10052.nocoerce);
        uvar_subtyping = (uu___235_10052.uvar_subtyping);
        tc_term = (uu___235_10052.tc_term);
        type_of = (uu___235_10052.type_of);
        universe_of = (uu___235_10052.universe_of);
        check_type_of = (uu___235_10052.check_type_of);
        use_bv_sorts = (uu___235_10052.use_bv_sorts);
        qtbl_name_and_index = (uu___235_10052.qtbl_name_and_index);
        normalized_eff_names = (uu___235_10052.normalized_eff_names);
        proof_ns = (uu___235_10052.proof_ns);
        synth_hook = (uu___235_10052.synth_hook);
        splice = (uu___235_10052.splice);
        is_native_tactic = (uu___235_10052.is_native_tactic);
        identifier_info = (uu___235_10052.identifier_info);
        tc_hooks = (uu___235_10052.tc_hooks);
        dsenv = (uu___235_10052.dsenv);
        dep_graph = (uu___235_10052.dep_graph);
        nbe = (uu___235_10052.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____10060  -> fun uu____10061  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___236_10081 = env  in
      {
        solver = (uu___236_10081.solver);
        range = (uu___236_10081.range);
        curmodule = (uu___236_10081.curmodule);
        gamma = (uu___236_10081.gamma);
        gamma_sig = (uu___236_10081.gamma_sig);
        gamma_cache = (uu___236_10081.gamma_cache);
        modules = (uu___236_10081.modules);
        expected_typ = (uu___236_10081.expected_typ);
        sigtab = (uu___236_10081.sigtab);
        attrtab = (uu___236_10081.attrtab);
        is_pattern = (uu___236_10081.is_pattern);
        instantiate_imp = (uu___236_10081.instantiate_imp);
        effects = (uu___236_10081.effects);
        generalize = (uu___236_10081.generalize);
        letrecs = (uu___236_10081.letrecs);
        top_level = (uu___236_10081.top_level);
        check_uvars = (uu___236_10081.check_uvars);
        use_eq = (uu___236_10081.use_eq);
        is_iface = (uu___236_10081.is_iface);
        admit = (uu___236_10081.admit);
        lax = (uu___236_10081.lax);
        lax_universes = (uu___236_10081.lax_universes);
        phase1 = (uu___236_10081.phase1);
        failhard = (uu___236_10081.failhard);
        nosynth = (uu___236_10081.nosynth);
        nocoerce = (uu___236_10081.nocoerce);
        uvar_subtyping = (uu___236_10081.uvar_subtyping);
        tc_term = (uu___236_10081.tc_term);
        type_of = (uu___236_10081.type_of);
        universe_of = (uu___236_10081.universe_of);
        check_type_of = (uu___236_10081.check_type_of);
        use_bv_sorts = (uu___236_10081.use_bv_sorts);
        qtbl_name_and_index = (uu___236_10081.qtbl_name_and_index);
        normalized_eff_names = (uu___236_10081.normalized_eff_names);
        proof_ns = (uu___236_10081.proof_ns);
        synth_hook = (uu___236_10081.synth_hook);
        splice = (uu___236_10081.splice);
        is_native_tactic = (uu___236_10081.is_native_tactic);
        identifier_info = (uu___236_10081.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___236_10081.dsenv);
        dep_graph = (uu___236_10081.dep_graph);
        nbe = (uu___236_10081.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___237_10092 = e  in
      {
        solver = (uu___237_10092.solver);
        range = (uu___237_10092.range);
        curmodule = (uu___237_10092.curmodule);
        gamma = (uu___237_10092.gamma);
        gamma_sig = (uu___237_10092.gamma_sig);
        gamma_cache = (uu___237_10092.gamma_cache);
        modules = (uu___237_10092.modules);
        expected_typ = (uu___237_10092.expected_typ);
        sigtab = (uu___237_10092.sigtab);
        attrtab = (uu___237_10092.attrtab);
        is_pattern = (uu___237_10092.is_pattern);
        instantiate_imp = (uu___237_10092.instantiate_imp);
        effects = (uu___237_10092.effects);
        generalize = (uu___237_10092.generalize);
        letrecs = (uu___237_10092.letrecs);
        top_level = (uu___237_10092.top_level);
        check_uvars = (uu___237_10092.check_uvars);
        use_eq = (uu___237_10092.use_eq);
        is_iface = (uu___237_10092.is_iface);
        admit = (uu___237_10092.admit);
        lax = (uu___237_10092.lax);
        lax_universes = (uu___237_10092.lax_universes);
        phase1 = (uu___237_10092.phase1);
        failhard = (uu___237_10092.failhard);
        nosynth = (uu___237_10092.nosynth);
        nocoerce = (uu___237_10092.nocoerce);
        uvar_subtyping = (uu___237_10092.uvar_subtyping);
        tc_term = (uu___237_10092.tc_term);
        type_of = (uu___237_10092.type_of);
        universe_of = (uu___237_10092.universe_of);
        check_type_of = (uu___237_10092.check_type_of);
        use_bv_sorts = (uu___237_10092.use_bv_sorts);
        qtbl_name_and_index = (uu___237_10092.qtbl_name_and_index);
        normalized_eff_names = (uu___237_10092.normalized_eff_names);
        proof_ns = (uu___237_10092.proof_ns);
        synth_hook = (uu___237_10092.synth_hook);
        splice = (uu___237_10092.splice);
        is_native_tactic = (uu___237_10092.is_native_tactic);
        identifier_info = (uu___237_10092.identifier_info);
        tc_hooks = (uu___237_10092.tc_hooks);
        dsenv = (uu___237_10092.dsenv);
        dep_graph = g;
        nbe = (uu___237_10092.nbe)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun e  -> e.dep_graph 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____10115) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____10116,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____10117,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____10118 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____10127 . unit -> 'Auu____10127 FStar_Util.smap =
  fun uu____10134  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____10139 . unit -> 'Auu____10139 FStar_Util.smap =
  fun uu____10146  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
           FStar_Pervasives_Native.tuple3)
      ->
      (env ->
         FStar_Syntax_Syntax.term ->
           (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
             FStar_Pervasives_Native.tuple3)
        ->
        (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
          (Prims.bool ->
             env ->
               FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
            ->
            solver_t ->
              FStar_Ident.lident ->
                (step Prims.list ->
                   env ->
                     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
                  -> env)
  =
  fun deps  ->
    fun tc_term  ->
      fun type_of  ->
        fun universe_of  ->
          fun check_type_of  ->
            fun solver  ->
              fun module_lid  ->
                fun nbe1  ->
                  let uu____10280 = new_gamma_cache ()  in
                  let uu____10283 = new_sigtab ()  in
                  let uu____10286 = new_sigtab ()  in
                  let uu____10293 =
                    let uu____10306 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____10306, FStar_Pervasives_Native.None)  in
                  let uu____10321 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____10324 = FStar_Options.using_facts_from ()  in
                  let uu____10325 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____10328 = FStar_Syntax_DsEnv.empty_env ()  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____10280;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____10283;
                    attrtab = uu____10286;
                    is_pattern = false;
                    instantiate_imp = true;
                    effects = { decls = []; order = []; joins = [] };
                    generalize = true;
                    letrecs = [];
                    top_level = false;
                    check_uvars = false;
                    use_eq = false;
                    is_iface = false;
                    admit = false;
                    lax = false;
                    lax_universes = false;
                    phase1 = false;
                    failhard = false;
                    nosynth = false;
                    nocoerce = false;
                    uvar_subtyping = true;
                    tc_term;
                    type_of;
                    universe_of;
                    check_type_of;
                    use_bv_sorts = false;
                    qtbl_name_and_index = uu____10293;
                    normalized_eff_names = uu____10321;
                    proof_ns = uu____10324;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    is_native_tactic = (fun uu____10364  -> false);
                    identifier_info = uu____10325;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____10328;
                    dep_graph = deps;
                    nbe = nbe1
                  }
  
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env  -> env.dsenv 
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env  -> env.attrtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (query_indices :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____10464  ->
    let uu____10465 = FStar_ST.op_Bang query_indices  in
    match uu____10465 with
    | [] -> failwith "Empty query indices!"
    | uu____10515 ->
        let uu____10524 =
          let uu____10533 =
            let uu____10540 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____10540  in
          let uu____10590 = FStar_ST.op_Bang query_indices  in uu____10533 ::
            uu____10590
           in
        FStar_ST.op_Colon_Equals query_indices uu____10524
  
let (pop_query_indices : unit -> unit) =
  fun uu____10679  ->
    let uu____10680 = FStar_ST.op_Bang query_indices  in
    match uu____10680 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10795  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10825  ->
    match uu____10825 with
    | (l,n1) ->
        let uu____10832 = FStar_ST.op_Bang query_indices  in
        (match uu____10832 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10943 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10962  ->
    let uu____10963 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____10963
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____11036 =
       let uu____11039 = FStar_ST.op_Bang stack  in env :: uu____11039  in
     FStar_ST.op_Colon_Equals stack uu____11036);
    (let uu___238_11088 = env  in
     let uu____11089 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____11092 = FStar_Util.smap_copy (sigtab env)  in
     let uu____11095 = FStar_Util.smap_copy (attrtab env)  in
     let uu____11102 =
       let uu____11115 =
         let uu____11118 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____11118  in
       let uu____11143 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____11115, uu____11143)  in
     let uu____11184 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____11187 =
       let uu____11190 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____11190  in
     {
       solver = (uu___238_11088.solver);
       range = (uu___238_11088.range);
       curmodule = (uu___238_11088.curmodule);
       gamma = (uu___238_11088.gamma);
       gamma_sig = (uu___238_11088.gamma_sig);
       gamma_cache = uu____11089;
       modules = (uu___238_11088.modules);
       expected_typ = (uu___238_11088.expected_typ);
       sigtab = uu____11092;
       attrtab = uu____11095;
       is_pattern = (uu___238_11088.is_pattern);
       instantiate_imp = (uu___238_11088.instantiate_imp);
       effects = (uu___238_11088.effects);
       generalize = (uu___238_11088.generalize);
       letrecs = (uu___238_11088.letrecs);
       top_level = (uu___238_11088.top_level);
       check_uvars = (uu___238_11088.check_uvars);
       use_eq = (uu___238_11088.use_eq);
       is_iface = (uu___238_11088.is_iface);
       admit = (uu___238_11088.admit);
       lax = (uu___238_11088.lax);
       lax_universes = (uu___238_11088.lax_universes);
       phase1 = (uu___238_11088.phase1);
       failhard = (uu___238_11088.failhard);
       nosynth = (uu___238_11088.nosynth);
       nocoerce = (uu___238_11088.nocoerce);
       uvar_subtyping = (uu___238_11088.uvar_subtyping);
       tc_term = (uu___238_11088.tc_term);
       type_of = (uu___238_11088.type_of);
       universe_of = (uu___238_11088.universe_of);
       check_type_of = (uu___238_11088.check_type_of);
       use_bv_sorts = (uu___238_11088.use_bv_sorts);
       qtbl_name_and_index = uu____11102;
       normalized_eff_names = uu____11184;
       proof_ns = (uu___238_11088.proof_ns);
       synth_hook = (uu___238_11088.synth_hook);
       splice = (uu___238_11088.splice);
       is_native_tactic = (uu___238_11088.is_native_tactic);
       identifier_info = uu____11187;
       tc_hooks = (uu___238_11088.tc_hooks);
       dsenv = (uu___238_11088.dsenv);
       dep_graph = (uu___238_11088.dep_graph);
       nbe = (uu___238_11088.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____11236  ->
    let uu____11237 = FStar_ST.op_Bang stack  in
    match uu____11237 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____11291 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2)
  = fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t =
  (Prims.int,Prims.int,solver_depth_t,Prims.int)
    FStar_Pervasives_Native.tuple4
let (snapshot :
  env -> Prims.string -> (tcenv_depth_t,env) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____11363  ->
           let uu____11364 = snapshot_stack env  in
           match uu____11364 with
           | (stack_depth,env1) ->
               let uu____11389 = snapshot_query_indices ()  in
               (match uu____11389 with
                | (query_indices_depth,()) ->
                    let uu____11413 = (env1.solver).snapshot msg  in
                    (match uu____11413 with
                     | (solver_depth,()) ->
                         let uu____11455 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____11455 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___239_11501 = env1  in
                                 {
                                   solver = (uu___239_11501.solver);
                                   range = (uu___239_11501.range);
                                   curmodule = (uu___239_11501.curmodule);
                                   gamma = (uu___239_11501.gamma);
                                   gamma_sig = (uu___239_11501.gamma_sig);
                                   gamma_cache = (uu___239_11501.gamma_cache);
                                   modules = (uu___239_11501.modules);
                                   expected_typ =
                                     (uu___239_11501.expected_typ);
                                   sigtab = (uu___239_11501.sigtab);
                                   attrtab = (uu___239_11501.attrtab);
                                   is_pattern = (uu___239_11501.is_pattern);
                                   instantiate_imp =
                                     (uu___239_11501.instantiate_imp);
                                   effects = (uu___239_11501.effects);
                                   generalize = (uu___239_11501.generalize);
                                   letrecs = (uu___239_11501.letrecs);
                                   top_level = (uu___239_11501.top_level);
                                   check_uvars = (uu___239_11501.check_uvars);
                                   use_eq = (uu___239_11501.use_eq);
                                   is_iface = (uu___239_11501.is_iface);
                                   admit = (uu___239_11501.admit);
                                   lax = (uu___239_11501.lax);
                                   lax_universes =
                                     (uu___239_11501.lax_universes);
                                   phase1 = (uu___239_11501.phase1);
                                   failhard = (uu___239_11501.failhard);
                                   nosynth = (uu___239_11501.nosynth);
                                   nocoerce = (uu___239_11501.nocoerce);
                                   uvar_subtyping =
                                     (uu___239_11501.uvar_subtyping);
                                   tc_term = (uu___239_11501.tc_term);
                                   type_of = (uu___239_11501.type_of);
                                   universe_of = (uu___239_11501.universe_of);
                                   check_type_of =
                                     (uu___239_11501.check_type_of);
                                   use_bv_sorts =
                                     (uu___239_11501.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___239_11501.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___239_11501.normalized_eff_names);
                                   proof_ns = (uu___239_11501.proof_ns);
                                   synth_hook = (uu___239_11501.synth_hook);
                                   splice = (uu___239_11501.splice);
                                   is_native_tactic =
                                     (uu___239_11501.is_native_tactic);
                                   identifier_info =
                                     (uu___239_11501.identifier_info);
                                   tc_hooks = (uu___239_11501.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___239_11501.dep_graph);
                                   nbe = (uu___239_11501.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____11532  ->
             let uu____11533 =
               match depth with
               | FStar_Pervasives_Native.Some (s1,s2,s3,s4) ->
                   ((FStar_Pervasives_Native.Some s1),
                     (FStar_Pervasives_Native.Some s2),
                     (FStar_Pervasives_Native.Some s3),
                     (FStar_Pervasives_Native.Some s4))
               | FStar_Pervasives_Native.None  ->
                   (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None)
                in
             match uu____11533 with
             | (stack_depth,query_indices_depth,solver_depth,dsenv_depth) ->
                 (solver.rollback msg solver_depth;
                  (match () with
                   | () ->
                       (rollback_query_indices query_indices_depth;
                        (match () with
                         | () ->
                             let tcenv = rollback_stack stack_depth  in
                             let dsenv1 =
                               FStar_Syntax_DsEnv.rollback dsenv_depth  in
                             ((let uu____11659 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____11659
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____11670 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____11670
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____11697,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____11729 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11755  ->
                  match uu____11755 with
                  | (m,uu____11761) -> FStar_Ident.lid_equals l m))
           in
        (match uu____11729 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___240_11769 = env  in
               {
                 solver = (uu___240_11769.solver);
                 range = (uu___240_11769.range);
                 curmodule = (uu___240_11769.curmodule);
                 gamma = (uu___240_11769.gamma);
                 gamma_sig = (uu___240_11769.gamma_sig);
                 gamma_cache = (uu___240_11769.gamma_cache);
                 modules = (uu___240_11769.modules);
                 expected_typ = (uu___240_11769.expected_typ);
                 sigtab = (uu___240_11769.sigtab);
                 attrtab = (uu___240_11769.attrtab);
                 is_pattern = (uu___240_11769.is_pattern);
                 instantiate_imp = (uu___240_11769.instantiate_imp);
                 effects = (uu___240_11769.effects);
                 generalize = (uu___240_11769.generalize);
                 letrecs = (uu___240_11769.letrecs);
                 top_level = (uu___240_11769.top_level);
                 check_uvars = (uu___240_11769.check_uvars);
                 use_eq = (uu___240_11769.use_eq);
                 is_iface = (uu___240_11769.is_iface);
                 admit = (uu___240_11769.admit);
                 lax = (uu___240_11769.lax);
                 lax_universes = (uu___240_11769.lax_universes);
                 phase1 = (uu___240_11769.phase1);
                 failhard = (uu___240_11769.failhard);
                 nosynth = (uu___240_11769.nosynth);
                 nocoerce = (uu___240_11769.nocoerce);
                 uvar_subtyping = (uu___240_11769.uvar_subtyping);
                 tc_term = (uu___240_11769.tc_term);
                 type_of = (uu___240_11769.type_of);
                 universe_of = (uu___240_11769.universe_of);
                 check_type_of = (uu___240_11769.check_type_of);
                 use_bv_sorts = (uu___240_11769.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___240_11769.normalized_eff_names);
                 proof_ns = (uu___240_11769.proof_ns);
                 synth_hook = (uu___240_11769.synth_hook);
                 splice = (uu___240_11769.splice);
                 is_native_tactic = (uu___240_11769.is_native_tactic);
                 identifier_info = (uu___240_11769.identifier_info);
                 tc_hooks = (uu___240_11769.tc_hooks);
                 dsenv = (uu___240_11769.dsenv);
                 dep_graph = (uu___240_11769.dep_graph);
                 nbe = (uu___240_11769.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11782,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___241_11791 = env  in
               {
                 solver = (uu___241_11791.solver);
                 range = (uu___241_11791.range);
                 curmodule = (uu___241_11791.curmodule);
                 gamma = (uu___241_11791.gamma);
                 gamma_sig = (uu___241_11791.gamma_sig);
                 gamma_cache = (uu___241_11791.gamma_cache);
                 modules = (uu___241_11791.modules);
                 expected_typ = (uu___241_11791.expected_typ);
                 sigtab = (uu___241_11791.sigtab);
                 attrtab = (uu___241_11791.attrtab);
                 is_pattern = (uu___241_11791.is_pattern);
                 instantiate_imp = (uu___241_11791.instantiate_imp);
                 effects = (uu___241_11791.effects);
                 generalize = (uu___241_11791.generalize);
                 letrecs = (uu___241_11791.letrecs);
                 top_level = (uu___241_11791.top_level);
                 check_uvars = (uu___241_11791.check_uvars);
                 use_eq = (uu___241_11791.use_eq);
                 is_iface = (uu___241_11791.is_iface);
                 admit = (uu___241_11791.admit);
                 lax = (uu___241_11791.lax);
                 lax_universes = (uu___241_11791.lax_universes);
                 phase1 = (uu___241_11791.phase1);
                 failhard = (uu___241_11791.failhard);
                 nosynth = (uu___241_11791.nosynth);
                 nocoerce = (uu___241_11791.nocoerce);
                 uvar_subtyping = (uu___241_11791.uvar_subtyping);
                 tc_term = (uu___241_11791.tc_term);
                 type_of = (uu___241_11791.type_of);
                 universe_of = (uu___241_11791.universe_of);
                 check_type_of = (uu___241_11791.check_type_of);
                 use_bv_sorts = (uu___241_11791.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___241_11791.normalized_eff_names);
                 proof_ns = (uu___241_11791.proof_ns);
                 synth_hook = (uu___241_11791.synth_hook);
                 splice = (uu___241_11791.splice);
                 is_native_tactic = (uu___241_11791.is_native_tactic);
                 identifier_info = (uu___241_11791.identifier_info);
                 tc_hooks = (uu___241_11791.tc_hooks);
                 dsenv = (uu___241_11791.dsenv);
                 dep_graph = (uu___241_11791.dep_graph);
                 nbe = (uu___241_11791.nbe)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___242_11825 = e  in
         {
           solver = (uu___242_11825.solver);
           range = r;
           curmodule = (uu___242_11825.curmodule);
           gamma = (uu___242_11825.gamma);
           gamma_sig = (uu___242_11825.gamma_sig);
           gamma_cache = (uu___242_11825.gamma_cache);
           modules = (uu___242_11825.modules);
           expected_typ = (uu___242_11825.expected_typ);
           sigtab = (uu___242_11825.sigtab);
           attrtab = (uu___242_11825.attrtab);
           is_pattern = (uu___242_11825.is_pattern);
           instantiate_imp = (uu___242_11825.instantiate_imp);
           effects = (uu___242_11825.effects);
           generalize = (uu___242_11825.generalize);
           letrecs = (uu___242_11825.letrecs);
           top_level = (uu___242_11825.top_level);
           check_uvars = (uu___242_11825.check_uvars);
           use_eq = (uu___242_11825.use_eq);
           is_iface = (uu___242_11825.is_iface);
           admit = (uu___242_11825.admit);
           lax = (uu___242_11825.lax);
           lax_universes = (uu___242_11825.lax_universes);
           phase1 = (uu___242_11825.phase1);
           failhard = (uu___242_11825.failhard);
           nosynth = (uu___242_11825.nosynth);
           nocoerce = (uu___242_11825.nocoerce);
           uvar_subtyping = (uu___242_11825.uvar_subtyping);
           tc_term = (uu___242_11825.tc_term);
           type_of = (uu___242_11825.type_of);
           universe_of = (uu___242_11825.universe_of);
           check_type_of = (uu___242_11825.check_type_of);
           use_bv_sorts = (uu___242_11825.use_bv_sorts);
           qtbl_name_and_index = (uu___242_11825.qtbl_name_and_index);
           normalized_eff_names = (uu___242_11825.normalized_eff_names);
           proof_ns = (uu___242_11825.proof_ns);
           synth_hook = (uu___242_11825.synth_hook);
           splice = (uu___242_11825.splice);
           is_native_tactic = (uu___242_11825.is_native_tactic);
           identifier_info = (uu___242_11825.identifier_info);
           tc_hooks = (uu___242_11825.tc_hooks);
           dsenv = (uu___242_11825.dsenv);
           dep_graph = (uu___242_11825.dep_graph);
           nbe = (uu___242_11825.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____11841 =
        let uu____11842 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____11842 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11841
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____11896 =
          let uu____11897 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11897 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11896
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____11951 =
          let uu____11952 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11952 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11951
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____12006 =
        let uu____12007 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____12007 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____12006
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___243_12068 = env  in
      {
        solver = (uu___243_12068.solver);
        range = (uu___243_12068.range);
        curmodule = lid;
        gamma = (uu___243_12068.gamma);
        gamma_sig = (uu___243_12068.gamma_sig);
        gamma_cache = (uu___243_12068.gamma_cache);
        modules = (uu___243_12068.modules);
        expected_typ = (uu___243_12068.expected_typ);
        sigtab = (uu___243_12068.sigtab);
        attrtab = (uu___243_12068.attrtab);
        is_pattern = (uu___243_12068.is_pattern);
        instantiate_imp = (uu___243_12068.instantiate_imp);
        effects = (uu___243_12068.effects);
        generalize = (uu___243_12068.generalize);
        letrecs = (uu___243_12068.letrecs);
        top_level = (uu___243_12068.top_level);
        check_uvars = (uu___243_12068.check_uvars);
        use_eq = (uu___243_12068.use_eq);
        is_iface = (uu___243_12068.is_iface);
        admit = (uu___243_12068.admit);
        lax = (uu___243_12068.lax);
        lax_universes = (uu___243_12068.lax_universes);
        phase1 = (uu___243_12068.phase1);
        failhard = (uu___243_12068.failhard);
        nosynth = (uu___243_12068.nosynth);
        nocoerce = (uu___243_12068.nocoerce);
        uvar_subtyping = (uu___243_12068.uvar_subtyping);
        tc_term = (uu___243_12068.tc_term);
        type_of = (uu___243_12068.type_of);
        universe_of = (uu___243_12068.universe_of);
        check_type_of = (uu___243_12068.check_type_of);
        use_bv_sorts = (uu___243_12068.use_bv_sorts);
        qtbl_name_and_index = (uu___243_12068.qtbl_name_and_index);
        normalized_eff_names = (uu___243_12068.normalized_eff_names);
        proof_ns = (uu___243_12068.proof_ns);
        synth_hook = (uu___243_12068.synth_hook);
        splice = (uu___243_12068.splice);
        is_native_tactic = (uu___243_12068.is_native_tactic);
        identifier_info = (uu___243_12068.identifier_info);
        tc_hooks = (uu___243_12068.tc_hooks);
        dsenv = (uu___243_12068.dsenv);
        dep_graph = (uu___243_12068.dep_graph);
        nbe = (uu___243_12068.nbe)
      }
  
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12095 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____12095
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____12105 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____12105)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____12115 =
      let uu____12116 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____12116  in
    (FStar_Errors.Fatal_VariableNotFound, uu____12115)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____12121  ->
    let uu____12122 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____12122
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
  
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____12206) ->
          let vs = mk_univ_subst formals us  in
          let uu____12230 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____12230)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___221_12246  ->
    match uu___221_12246 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____12272  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    fun t  ->
      let uu____12291 = inst_tscheme t  in
      match uu____12291 with
      | (us,t1) ->
          let uu____12302 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____12302)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____12322  ->
          match uu____12322 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12343 =
                         let uu____12344 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____12345 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____12346 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____12347 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12344 uu____12345 uu____12346 uu____12347
                          in
                       failwith uu____12343)
                    else ();
                    (let uu____12349 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____12349))
               | uu____12358 ->
                   let uu____12359 =
                     let uu____12360 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12360
                      in
                   failwith uu____12359)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____12366 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____12372 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____12378 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env  ->
    fun l  ->
      let cur = current_module env  in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident]
              in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident]  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____12420) -> Maybe
             | (uu____12427,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12446 -> No  in
           aux cur1 lns)
        else No
  
type qninfo =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____12537 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____12537 with
          | FStar_Pervasives_Native.None  ->
              let uu____12560 =
                FStar_Util.find_map env.gamma
                  (fun uu___222_12604  ->
                     match uu___222_12604 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____12643 = FStar_Ident.lid_equals lid l  in
                         if uu____12643
                         then
                           let uu____12664 =
                             let uu____12683 =
                               let uu____12698 = inst_tscheme t  in
                               FStar_Util.Inl uu____12698  in
                             let uu____12713 = FStar_Ident.range_of_lid l  in
                             (uu____12683, uu____12713)  in
                           FStar_Pervasives_Native.Some uu____12664
                         else FStar_Pervasives_Native.None
                     | uu____12765 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____12560
                (fun uu____12803  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___223_12812  ->
                        match uu___223_12812 with
                        | (uu____12815,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____12817);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____12818;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____12819;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____12820;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____12821;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____12841 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____12841
                                 then
                                   cache
                                     ((FStar_Util.Inr
                                         (se, FStar_Pervasives_Native.None)),
                                       (FStar_Syntax_Util.range_of_sigelt se))
                                 else FStar_Pervasives_Native.None)
                        | (lids,s) ->
                            let maybe_cache t =
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_declare_typ
                                  uu____12889 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12896 -> cache t  in
                            let uu____12897 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____12897 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12903 =
                                   let uu____12904 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12904)
                                    in
                                 maybe_cache uu____12903)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12972 = find_in_sigtab env lid  in
         match uu____12972 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (lookup_sigelt :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13052 = lookup_qname env lid  in
      match uu____13052 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____13073,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____13184 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____13184 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____13226 =
          let uu____13229 = lookup_attr env1 attr  in se1 :: uu____13229  in
        FStar_Util.smap_add (attrtab env1) attr uu____13226  in
      FStar_List.iter
        (fun attr  ->
           let uu____13239 =
             let uu____13240 = FStar_Syntax_Subst.compress attr  in
             uu____13240.FStar_Syntax_Syntax.n  in
           match uu____13239 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13244 =
                 let uu____13245 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____13245.FStar_Ident.str  in
               add_one1 env se uu____13244
           | uu____13246 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13268) ->
          add_sigelts env ses
      | uu____13277 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a
                            (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                           in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____13292 -> ()))

and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___224_13323  ->
           match uu___224_13323 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13341 -> FStar_Pervasives_Native.None)
  
let (lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu____13402,lb::[]),uu____13404) ->
            let uu____13411 =
              let uu____13420 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____13429 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____13420, uu____13429)  in
            FStar_Pervasives_Native.Some uu____13411
        | FStar_Syntax_Syntax.Sig_let ((uu____13442,lbs),uu____13444) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13474 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13486 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____13486
                     then
                       let uu____13497 =
                         let uu____13506 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____13515 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____13506, uu____13515)  in
                       FStar_Pervasives_Native.Some uu____13497
                     else FStar_Pervasives_Native.None)
        | uu____13537 -> FStar_Pervasives_Native.None
  
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      let inst_tscheme1 ts =
        match us_opt with
        | FStar_Pervasives_Native.None  -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____13596 =
            let uu____13605 =
              let uu____13610 =
                let uu____13611 =
                  let uu____13614 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13614
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____13611)  in
              inst_tscheme1 uu____13610  in
            (uu____13605, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13596
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____13636,uu____13637) ->
          let uu____13642 =
            let uu____13651 =
              let uu____13656 =
                let uu____13657 =
                  let uu____13660 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____13660  in
                (us, uu____13657)  in
              inst_tscheme1 uu____13656  in
            (uu____13651, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____13642
      | uu____13679 -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term'
                                          FStar_Syntax_Syntax.syntax)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun env  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        let mapper uu____13767 =
          match uu____13767 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13863,uvs,t,uu____13866,uu____13867,uu____13868);
                      FStar_Syntax_Syntax.sigrng = uu____13869;
                      FStar_Syntax_Syntax.sigquals = uu____13870;
                      FStar_Syntax_Syntax.sigmeta = uu____13871;
                      FStar_Syntax_Syntax.sigattrs = uu____13872;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13893 =
                     let uu____13902 = inst_tscheme1 (uvs, t)  in
                     (uu____13902, rng)  in
                   FStar_Pervasives_Native.Some uu____13893
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____13926;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13928;
                      FStar_Syntax_Syntax.sigattrs = uu____13929;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____13946 =
                     let uu____13947 = in_cur_mod env l  in uu____13947 = Yes
                      in
                   if uu____13946
                   then
                     let uu____13958 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____13958
                      then
                        let uu____13971 =
                          let uu____13980 = inst_tscheme1 (uvs, t)  in
                          (uu____13980, rng)  in
                        FStar_Pervasives_Native.Some uu____13971
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____14011 =
                        let uu____14020 = inst_tscheme1 (uvs, t)  in
                        (uu____14020, rng)  in
                      FStar_Pervasives_Native.Some uu____14011)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14045,uu____14046);
                      FStar_Syntax_Syntax.sigrng = uu____14047;
                      FStar_Syntax_Syntax.sigquals = uu____14048;
                      FStar_Syntax_Syntax.sigmeta = uu____14049;
                      FStar_Syntax_Syntax.sigattrs = uu____14050;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____14091 =
                          let uu____14100 = inst_tscheme1 (uvs, k)  in
                          (uu____14100, rng)  in
                        FStar_Pervasives_Native.Some uu____14091
                    | uu____14121 ->
                        let uu____14122 =
                          let uu____14131 =
                            let uu____14136 =
                              let uu____14137 =
                                let uu____14140 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14140
                                 in
                              (uvs, uu____14137)  in
                            inst_tscheme1 uu____14136  in
                          (uu____14131, rng)  in
                        FStar_Pervasives_Native.Some uu____14122)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____14163,uu____14164);
                      FStar_Syntax_Syntax.sigrng = uu____14165;
                      FStar_Syntax_Syntax.sigquals = uu____14166;
                      FStar_Syntax_Syntax.sigmeta = uu____14167;
                      FStar_Syntax_Syntax.sigattrs = uu____14168;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14210 =
                          let uu____14219 = inst_tscheme_with (uvs, k) us  in
                          (uu____14219, rng)  in
                        FStar_Pervasives_Native.Some uu____14210
                    | uu____14240 ->
                        let uu____14241 =
                          let uu____14250 =
                            let uu____14255 =
                              let uu____14256 =
                                let uu____14259 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____14259
                                 in
                              (uvs, uu____14256)  in
                            inst_tscheme_with uu____14255 us  in
                          (uu____14250, rng)  in
                        FStar_Pervasives_Native.Some uu____14241)
               | FStar_Util.Inr se ->
                   let uu____14295 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____14316;
                          FStar_Syntax_Syntax.sigrng = uu____14317;
                          FStar_Syntax_Syntax.sigquals = uu____14318;
                          FStar_Syntax_Syntax.sigmeta = uu____14319;
                          FStar_Syntax_Syntax.sigattrs = uu____14320;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14335 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____14295
                     (FStar_Util.map_option
                        (fun uu____14383  ->
                           match uu____14383 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____14414 =
          let uu____14425 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____14425 mapper  in
        match uu____14414 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____14499 =
              let uu____14510 =
                let uu____14517 =
                  let uu___244_14520 = t  in
                  let uu____14521 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___244_14520.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14521;
                    FStar_Syntax_Syntax.vars =
                      (uu___244_14520.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____14517)  in
              (uu____14510, r)  in
            FStar_Pervasives_Native.Some uu____14499
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14568 = lookup_qname env l  in
      match uu____14568 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____14587 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____14639 = try_lookup_bv env bv  in
      match uu____14639 with
      | FStar_Pervasives_Native.None  ->
          let uu____14654 = variable_not_found bv  in
          FStar_Errors.raise_error uu____14654 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____14669 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____14670 =
            let uu____14671 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____14671  in
          (uu____14669, uu____14670)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____14692 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____14692 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____14758 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____14758  in
          let uu____14759 =
            let uu____14768 =
              let uu____14773 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____14773)  in
            (uu____14768, r1)  in
          FStar_Pervasives_Native.Some uu____14759
  
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun us  ->
      fun l  ->
        let uu____14807 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____14807 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14840,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____14865 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____14865  in
            let uu____14866 =
              let uu____14871 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____14871, r1)  in
            FStar_Pervasives_Native.Some uu____14866
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____14894 = try_lookup_lid env l  in
      match uu____14894 with
      | FStar_Pervasives_Native.None  ->
          let uu____14921 = name_not_found l  in
          let uu____14926 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14921 uu____14926
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___225_14966  ->
              match uu___225_14966 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14968 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____14987 = lookup_qname env lid  in
      match uu____14987 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14996,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____14999;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____15001;
              FStar_Syntax_Syntax.sigattrs = uu____15002;_},FStar_Pervasives_Native.None
            ),uu____15003)
          ->
          let uu____15052 =
            let uu____15059 =
              let uu____15060 =
                let uu____15063 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____15063 t  in
              (uvs, uu____15060)  in
            (uu____15059, q)  in
          FStar_Pervasives_Native.Some uu____15052
      | uu____15076 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15097 = lookup_qname env lid  in
      match uu____15097 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15102,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____15105;
              FStar_Syntax_Syntax.sigquals = uu____15106;
              FStar_Syntax_Syntax.sigmeta = uu____15107;
              FStar_Syntax_Syntax.sigattrs = uu____15108;_},FStar_Pervasives_Native.None
            ),uu____15109)
          ->
          let uu____15158 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15158 (uvs, t)
      | uu____15163 ->
          let uu____15164 = name_not_found lid  in
          let uu____15169 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15164 uu____15169
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15188 = lookup_qname env lid  in
      match uu____15188 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15193,uvs,t,uu____15196,uu____15197,uu____15198);
              FStar_Syntax_Syntax.sigrng = uu____15199;
              FStar_Syntax_Syntax.sigquals = uu____15200;
              FStar_Syntax_Syntax.sigmeta = uu____15201;
              FStar_Syntax_Syntax.sigattrs = uu____15202;_},FStar_Pervasives_Native.None
            ),uu____15203)
          ->
          let uu____15256 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____15256 (uvs, t)
      | uu____15261 ->
          let uu____15262 = name_not_found lid  in
          let uu____15267 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____15262 uu____15267
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____15288 = lookup_qname env lid  in
      match uu____15288 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15295,uu____15296,uu____15297,uu____15298,uu____15299,dcs);
              FStar_Syntax_Syntax.sigrng = uu____15301;
              FStar_Syntax_Syntax.sigquals = uu____15302;
              FStar_Syntax_Syntax.sigmeta = uu____15303;
              FStar_Syntax_Syntax.sigattrs = uu____15304;_},uu____15305),uu____15306)
          -> (true, dcs)
      | uu____15367 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15380 = lookup_qname env lid  in
      match uu____15380 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15381,uu____15382,uu____15383,l,uu____15385,uu____15386);
              FStar_Syntax_Syntax.sigrng = uu____15387;
              FStar_Syntax_Syntax.sigquals = uu____15388;
              FStar_Syntax_Syntax.sigmeta = uu____15389;
              FStar_Syntax_Syntax.sigattrs = uu____15390;_},uu____15391),uu____15392)
          -> l
      | uu____15447 ->
          let uu____15448 =
            let uu____15449 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____15449  in
          failwith uu____15448
  
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun lid  ->
      fun qninfo  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl))))
           in
        match qninfo with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15498)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15549,lbs),uu____15551)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____15573 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____15573
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15605 -> FStar_Pervasives_Native.None)
        | uu____15610 -> FStar_Pervasives_Native.None
  
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____15640 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15640
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15665),uu____15666) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15715 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____15736),uu____15737) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____15786 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____15807 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____15807
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____15826 = lookup_qname env ftv  in
      match uu____15826 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____15830) ->
          let uu____15875 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____15875 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____15896,t),r) ->
               let uu____15911 =
                 let uu____15912 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____15912 t  in
               FStar_Pervasives_Native.Some uu____15911)
      | uu____15913 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____15924 = try_lookup_effect_lid env ftv  in
      match uu____15924 with
      | FStar_Pervasives_Native.None  ->
          let uu____15927 = name_not_found ftv  in
          let uu____15932 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____15927 uu____15932
      | FStar_Pervasives_Native.Some k -> k
  
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____15955 = lookup_qname env lid0  in
        match uu____15955 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____15966);
                FStar_Syntax_Syntax.sigrng = uu____15967;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____15969;
                FStar_Syntax_Syntax.sigattrs = uu____15970;_},FStar_Pervasives_Native.None
              ),uu____15971)
            ->
            let lid1 =
              let uu____16025 =
                let uu____16026 = FStar_Ident.range_of_lid lid  in
                let uu____16027 =
                  let uu____16028 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____16028  in
                FStar_Range.set_use_range uu____16026 uu____16027  in
              FStar_Ident.set_lid_range lid uu____16025  in
            let uu____16029 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___226_16033  ->
                      match uu___226_16033 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____16034 -> false))
               in
            if uu____16029
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____16048 =
                      let uu____16049 =
                        let uu____16050 = get_range env  in
                        FStar_Range.string_of_range uu____16050  in
                      let uu____16051 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____16052 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____16049 uu____16051 uu____16052
                       in
                    failwith uu____16048)
                  in
               match (binders, univs1) with
               | ([],uu____16069) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____16094,uu____16095::uu____16096::uu____16097) ->
                   let uu____16118 =
                     let uu____16119 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____16120 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____16119 uu____16120
                      in
                   failwith uu____16118
               | uu____16127 ->
                   let uu____16142 =
                     let uu____16147 =
                       let uu____16148 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____16148)  in
                     inst_tscheme_with uu____16147 insts  in
                   (match uu____16142 with
                    | (uu____16161,t) ->
                        let t1 =
                          let uu____16164 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____16164 t  in
                        let uu____16165 =
                          let uu____16166 = FStar_Syntax_Subst.compress t1
                             in
                          uu____16166.FStar_Syntax_Syntax.n  in
                        (match uu____16165 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16201 -> failwith "Impossible")))
        | uu____16208 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____16231 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____16231 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16244,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____16251 = find1 l2  in
            (match uu____16251 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____16258 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____16258 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____16262 = find1 l  in
            (match uu____16262 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____16267 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____16267
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____16281 = lookup_qname env l1  in
      match uu____16281 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16284;
              FStar_Syntax_Syntax.sigrng = uu____16285;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16287;
              FStar_Syntax_Syntax.sigattrs = uu____16288;_},uu____16289),uu____16290)
          -> q
      | uu____16341 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____16362 =
          let uu____16363 =
            let uu____16364 = FStar_Util.string_of_int i  in
            let uu____16365 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16364 uu____16365
             in
          failwith uu____16363  in
        let uu____16366 = lookup_datacon env lid  in
        match uu____16366 with
        | (uu____16371,t) ->
            let uu____16373 =
              let uu____16374 = FStar_Syntax_Subst.compress t  in
              uu____16374.FStar_Syntax_Syntax.n  in
            (match uu____16373 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16378) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____16419 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____16419
                      FStar_Pervasives_Native.fst)
             | uu____16430 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16441 = lookup_qname env l  in
      match uu____16441 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16442,uu____16443,uu____16444);
              FStar_Syntax_Syntax.sigrng = uu____16445;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16447;
              FStar_Syntax_Syntax.sigattrs = uu____16448;_},uu____16449),uu____16450)
          ->
          FStar_Util.for_some
            (fun uu___227_16503  ->
               match uu___227_16503 with
               | FStar_Syntax_Syntax.Projector uu____16504 -> true
               | uu____16509 -> false) quals
      | uu____16510 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16521 = lookup_qname env lid  in
      match uu____16521 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16522,uu____16523,uu____16524,uu____16525,uu____16526,uu____16527);
              FStar_Syntax_Syntax.sigrng = uu____16528;
              FStar_Syntax_Syntax.sigquals = uu____16529;
              FStar_Syntax_Syntax.sigmeta = uu____16530;
              FStar_Syntax_Syntax.sigattrs = uu____16531;_},uu____16532),uu____16533)
          -> true
      | uu____16588 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16599 = lookup_qname env lid  in
      match uu____16599 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16600,uu____16601,uu____16602,uu____16603,uu____16604,uu____16605);
              FStar_Syntax_Syntax.sigrng = uu____16606;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16608;
              FStar_Syntax_Syntax.sigattrs = uu____16609;_},uu____16610),uu____16611)
          ->
          FStar_Util.for_some
            (fun uu___228_16672  ->
               match uu___228_16672 with
               | FStar_Syntax_Syntax.RecordType uu____16673 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16682 -> true
               | uu____16691 -> false) quals
      | uu____16692 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16698,uu____16699);
            FStar_Syntax_Syntax.sigrng = uu____16700;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16702;
            FStar_Syntax_Syntax.sigattrs = uu____16703;_},uu____16704),uu____16705)
        ->
        FStar_Util.for_some
          (fun uu___229_16762  ->
             match uu___229_16762 with
             | FStar_Syntax_Syntax.Action uu____16763 -> true
             | uu____16764 -> false) quals
    | uu____16765 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____16776 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____16776
  
let (is_interpreted : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  let interpreted_symbols =
    [FStar_Parser_Const.op_Eq;
    FStar_Parser_Const.op_notEq;
    FStar_Parser_Const.op_LT;
    FStar_Parser_Const.op_LTE;
    FStar_Parser_Const.op_GT;
    FStar_Parser_Const.op_GTE;
    FStar_Parser_Const.op_Subtraction;
    FStar_Parser_Const.op_Minus;
    FStar_Parser_Const.op_Addition;
    FStar_Parser_Const.op_Multiply;
    FStar_Parser_Const.op_Division;
    FStar_Parser_Const.op_Modulus;
    FStar_Parser_Const.op_And;
    FStar_Parser_Const.op_Or;
    FStar_Parser_Const.op_Negation]  in
  fun env  ->
    fun head1  ->
      let uu____16790 =
        let uu____16791 = FStar_Syntax_Util.un_uinst head1  in
        uu____16791.FStar_Syntax_Syntax.n  in
      match uu____16790 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____16795 ->
               true
           | uu____16796 -> false)
      | uu____16797 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16808 = lookup_qname env l  in
      match uu____16808 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____16810),uu____16811) ->
          FStar_Util.for_some
            (fun uu___230_16859  ->
               match uu___230_16859 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____16860 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____16861 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____16932 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____16948) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____16965 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____16972 ->
                 FStar_Pervasives_Native.Some true
             | uu____16989 -> FStar_Pervasives_Native.Some false)
         in
      let uu____16990 =
        let uu____16993 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____16993 mapper  in
      match uu____16990 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____17043 = lookup_qname env lid  in
      match uu____17043 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17044,uu____17045,tps,uu____17047,uu____17048,uu____17049);
              FStar_Syntax_Syntax.sigrng = uu____17050;
              FStar_Syntax_Syntax.sigquals = uu____17051;
              FStar_Syntax_Syntax.sigmeta = uu____17052;
              FStar_Syntax_Syntax.sigattrs = uu____17053;_},uu____17054),uu____17055)
          -> FStar_List.length tps
      | uu____17120 ->
          let uu____17121 = name_not_found lid  in
          let uu____17126 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17121 uu____17126
  
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____17170  ->
              match uu____17170 with
              | (d,uu____17178) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____17193 = effect_decl_opt env l  in
      match uu____17193 with
      | FStar_Pervasives_Native.None  ->
          let uu____17208 = name_not_found l  in
          let uu____17213 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17208 uu____17213
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17235  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17254  ->
            fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17285 = FStar_Ident.lid_equals l1 l2  in
        if uu____17285
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17293 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____17293
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17301 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17354  ->
                        match uu____17354 with
                        | (m1,m2,uu____17367,uu____17368,uu____17369) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____17301 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17386 =
                    let uu____17391 =
                      let uu____17392 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____17393 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17392
                        uu____17393
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17391)
                     in
                  FStar_Errors.raise_error uu____17386 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17400,uu____17401,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____17434 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____17434
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
  
let wp_sig_aux :
  'Auu____17450 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____17450)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____17479 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17505  ->
                match uu____17505 with
                | (d,uu____17511) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____17479 with
      | FStar_Pervasives_Native.None  ->
          let uu____17522 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____17522
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____17535 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____17535 with
           | (uu____17550,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____17568)::(wp,uu____17570)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17626 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (null_wp_for_eff :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          let uu____17681 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____17681
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17683 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____17683
             then
               FStar_Syntax_Syntax.mk_GTotal' res_t
                 (FStar_Pervasives_Native.Some res_u)
             else
               (let eff_name1 = norm_eff_name env eff_name  in
                let ed = get_effect_decl env eff_name1  in
                let null_wp =
                  inst_effect_fun_with [res_u] env ed
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let null_wp_res =
                  let uu____17691 = get_range env  in
                  let uu____17692 =
                    let uu____17699 =
                      let uu____17700 =
                        let uu____17717 =
                          let uu____17728 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____17728]  in
                        (null_wp, uu____17717)  in
                      FStar_Syntax_Syntax.Tm_app uu____17700  in
                    FStar_Syntax_Syntax.mk uu____17699  in
                  uu____17692 FStar_Pervasives_Native.None uu____17691  in
                let uu____17768 =
                  let uu____17769 =
                    let uu____17780 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____17780]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17769;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____17768))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___245_17817 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___245_17817.order);
              joins = (uu___245_17817.joins)
            }  in
          let uu___246_17826 = env  in
          {
            solver = (uu___246_17826.solver);
            range = (uu___246_17826.range);
            curmodule = (uu___246_17826.curmodule);
            gamma = (uu___246_17826.gamma);
            gamma_sig = (uu___246_17826.gamma_sig);
            gamma_cache = (uu___246_17826.gamma_cache);
            modules = (uu___246_17826.modules);
            expected_typ = (uu___246_17826.expected_typ);
            sigtab = (uu___246_17826.sigtab);
            attrtab = (uu___246_17826.attrtab);
            is_pattern = (uu___246_17826.is_pattern);
            instantiate_imp = (uu___246_17826.instantiate_imp);
            effects;
            generalize = (uu___246_17826.generalize);
            letrecs = (uu___246_17826.letrecs);
            top_level = (uu___246_17826.top_level);
            check_uvars = (uu___246_17826.check_uvars);
            use_eq = (uu___246_17826.use_eq);
            is_iface = (uu___246_17826.is_iface);
            admit = (uu___246_17826.admit);
            lax = (uu___246_17826.lax);
            lax_universes = (uu___246_17826.lax_universes);
            phase1 = (uu___246_17826.phase1);
            failhard = (uu___246_17826.failhard);
            nosynth = (uu___246_17826.nosynth);
            nocoerce = (uu___246_17826.nocoerce);
            uvar_subtyping = (uu___246_17826.uvar_subtyping);
            tc_term = (uu___246_17826.tc_term);
            type_of = (uu___246_17826.type_of);
            universe_of = (uu___246_17826.universe_of);
            check_type_of = (uu___246_17826.check_type_of);
            use_bv_sorts = (uu___246_17826.use_bv_sorts);
            qtbl_name_and_index = (uu___246_17826.qtbl_name_and_index);
            normalized_eff_names = (uu___246_17826.normalized_eff_names);
            proof_ns = (uu___246_17826.proof_ns);
            synth_hook = (uu___246_17826.synth_hook);
            splice = (uu___246_17826.splice);
            is_native_tactic = (uu___246_17826.is_native_tactic);
            identifier_info = (uu___246_17826.identifier_info);
            tc_hooks = (uu___246_17826.tc_hooks);
            dsenv = (uu___246_17826.dsenv);
            dep_graph = (uu___246_17826.dep_graph);
            nbe = (uu___246_17826.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____17856 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____17856  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____18014 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____18015 = l1 u t wp e  in
                                l2 u t uu____18014 uu____18015))
                | uu____18016 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____18088 = inst_tscheme_with lift_t [u]  in
            match uu____18088 with
            | (uu____18095,lift_t1) ->
                let uu____18097 =
                  let uu____18104 =
                    let uu____18105 =
                      let uu____18122 =
                        let uu____18133 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18142 =
                          let uu____18153 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____18153]  in
                        uu____18133 :: uu____18142  in
                      (lift_t1, uu____18122)  in
                    FStar_Syntax_Syntax.Tm_app uu____18105  in
                  FStar_Syntax_Syntax.mk uu____18104  in
                uu____18097 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____18265 = inst_tscheme_with lift_t [u]  in
            match uu____18265 with
            | (uu____18272,lift_t1) ->
                let uu____18274 =
                  let uu____18281 =
                    let uu____18282 =
                      let uu____18299 =
                        let uu____18310 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____18319 =
                          let uu____18330 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____18339 =
                            let uu____18350 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____18350]  in
                          uu____18330 :: uu____18339  in
                        uu____18310 :: uu____18319  in
                      (lift_t1, uu____18299)  in
                    FStar_Syntax_Syntax.Tm_app uu____18282  in
                  FStar_Syntax_Syntax.mk uu____18281  in
                uu____18274 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term
             in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            }  in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            }  in
          let print_mlift l =
            let bogus_term s =
              let uu____18452 =
                let uu____18453 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____18453
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____18452  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____18457 =
              let uu____18458 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____18458  in
            let uu____18459 =
              let uu____18460 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____18486 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____18486)
                 in
              FStar_Util.dflt "none" uu____18460  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18457
              uu____18459
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18512  ->
                    match uu____18512 with
                    | (e,uu____18520) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____18543 =
            match uu____18543 with
            | (i,j) ->
                let uu____18554 = FStar_Ident.lid_equals i j  in
                if uu____18554
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____18586 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____18596 = FStar_Ident.lid_equals i k  in
                        if uu____18596
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____18607 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____18607
                                  then []
                                  else
                                    (let uu____18611 =
                                       let uu____18620 =
                                         find_edge order1 (i, k)  in
                                       let uu____18623 =
                                         find_edge order1 (k, j)  in
                                       (uu____18620, uu____18623)  in
                                     match uu____18611 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____18638 =
                                           compose_edges e1 e2  in
                                         [uu____18638]
                                     | uu____18639 -> [])))))
                 in
              FStar_List.append order1 uu____18586  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____18669 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18671 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____18671
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____18669
                   then
                     let uu____18676 =
                       let uu____18681 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18681)
                        in
                     let uu____18682 = get_range env  in
                     FStar_Errors.raise_error uu____18676 uu____18682
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____18759 = FStar_Ident.lid_equals i j
                                   in
                                if uu____18759
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____18808 =
                                              let uu____18817 =
                                                find_edge order2 (i, k)  in
                                              let uu____18820 =
                                                find_edge order2 (j, k)  in
                                              (uu____18817, uu____18820)  in
                                            match uu____18808 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____18862,uu____18863)
                                                     ->
                                                     let uu____18870 =
                                                       let uu____18875 =
                                                         let uu____18876 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18876
                                                          in
                                                       let uu____18879 =
                                                         let uu____18880 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____18880
                                                          in
                                                       (uu____18875,
                                                         uu____18879)
                                                        in
                                                     (match uu____18870 with
                                                      | (true ,true ) ->
                                                          let uu____18891 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____18891
                                                          then
                                                            (FStar_Errors.log_issue
                                                               FStar_Range.dummyRange
                                                               (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                 "Looking multiple times at the same upper bound candidate");
                                                             bopt)
                                                          else
                                                            failwith
                                                              "Found a cycle in the lattice"
                                                      | (false ,false ) ->
                                                          bopt
                                                      | (true ,false ) ->
                                                          FStar_Pervasives_Native.Some
                                                            (k, ik, jk)
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____18916 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___247_18989 = env.effects  in
              { decls = (uu___247_18989.decls); order = order2; joins }  in
            let uu___248_18990 = env  in
            {
              solver = (uu___248_18990.solver);
              range = (uu___248_18990.range);
              curmodule = (uu___248_18990.curmodule);
              gamma = (uu___248_18990.gamma);
              gamma_sig = (uu___248_18990.gamma_sig);
              gamma_cache = (uu___248_18990.gamma_cache);
              modules = (uu___248_18990.modules);
              expected_typ = (uu___248_18990.expected_typ);
              sigtab = (uu___248_18990.sigtab);
              attrtab = (uu___248_18990.attrtab);
              is_pattern = (uu___248_18990.is_pattern);
              instantiate_imp = (uu___248_18990.instantiate_imp);
              effects;
              generalize = (uu___248_18990.generalize);
              letrecs = (uu___248_18990.letrecs);
              top_level = (uu___248_18990.top_level);
              check_uvars = (uu___248_18990.check_uvars);
              use_eq = (uu___248_18990.use_eq);
              is_iface = (uu___248_18990.is_iface);
              admit = (uu___248_18990.admit);
              lax = (uu___248_18990.lax);
              lax_universes = (uu___248_18990.lax_universes);
              phase1 = (uu___248_18990.phase1);
              failhard = (uu___248_18990.failhard);
              nosynth = (uu___248_18990.nosynth);
              nocoerce = (uu___248_18990.nocoerce);
              uvar_subtyping = (uu___248_18990.uvar_subtyping);
              tc_term = (uu___248_18990.tc_term);
              type_of = (uu___248_18990.type_of);
              universe_of = (uu___248_18990.universe_of);
              check_type_of = (uu___248_18990.check_type_of);
              use_bv_sorts = (uu___248_18990.use_bv_sorts);
              qtbl_name_and_index = (uu___248_18990.qtbl_name_and_index);
              normalized_eff_names = (uu___248_18990.normalized_eff_names);
              proof_ns = (uu___248_18990.proof_ns);
              synth_hook = (uu___248_18990.synth_hook);
              splice = (uu___248_18990.splice);
              is_native_tactic = (uu___248_18990.is_native_tactic);
              identifier_info = (uu___248_18990.identifier_info);
              tc_hooks = (uu___248_18990.tc_hooks);
              dsenv = (uu___248_18990.dsenv);
              dep_graph = (uu___248_18990.dep_graph);
              nbe = (uu___248_18990.nbe)
            }))
      | uu____18991 -> env
  
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____19019 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____19031 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____19031 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____19048 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____19048 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____19070 =
                     let uu____19075 =
                       let uu____19076 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____19083 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____19092 =
                         let uu____19093 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____19093  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____19076 uu____19083 uu____19092
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____19075)
                      in
                   FStar_Errors.raise_error uu____19070
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____19098 =
                     let uu____19109 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____19109 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____19146  ->
                        fun uu____19147  ->
                          match (uu____19146, uu____19147) with
                          | ((x,uu____19177),(t,uu____19179)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____19098
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____19210 =
                     let uu___249_19211 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___249_19211.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___249_19211.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___249_19211.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___249_19211.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____19210
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let (effect_repr_aux :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option)
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_c  ->
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____19241 = effect_decl_opt env effect_name  in
          match uu____19241 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____19274 =
                only_reifiable &&
                  (let uu____19276 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____19276)
                 in
              if uu____19274
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____19292 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____19315 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____19352 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____19352
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____19353 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____19353
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____19367 =
                       let uu____19370 = get_range env  in
                       let uu____19371 =
                         let uu____19378 =
                           let uu____19379 =
                             let uu____19396 =
                               let uu____19407 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____19407; wp]  in
                             (repr, uu____19396)  in
                           FStar_Syntax_Syntax.Tm_app uu____19379  in
                         FStar_Syntax_Syntax.mk uu____19378  in
                       uu____19371 FStar_Pervasives_Native.None uu____19370
                        in
                     FStar_Pervasives_Native.Some uu____19367)
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c 
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____19497 =
            let uu____19502 =
              let uu____19503 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____19503
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____19502)  in
          let uu____19504 = get_range env  in
          FStar_Errors.raise_error uu____19497 uu____19504  in
        let uu____19505 = effect_repr_aux true env c u_c  in
        match uu____19505 with
        | FStar_Pervasives_Native.None  ->
            no_reify (FStar_Syntax_Util.comp_effect_name c)
        | FStar_Pervasives_Native.Some tm -> tm
  
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let (is_reifiable : env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____19551 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19562 =
        let uu____19563 = FStar_Syntax_Subst.compress t  in
        uu____19563.FStar_Syntax_Syntax.n  in
      match uu____19562 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19566,c) ->
          is_reifiable_comp env c
      | uu____19588 -> false
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___250_19609 = env  in
        {
          solver = (uu___250_19609.solver);
          range = (uu___250_19609.range);
          curmodule = (uu___250_19609.curmodule);
          gamma = (uu___250_19609.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___250_19609.gamma_cache);
          modules = (uu___250_19609.modules);
          expected_typ = (uu___250_19609.expected_typ);
          sigtab = (uu___250_19609.sigtab);
          attrtab = (uu___250_19609.attrtab);
          is_pattern = (uu___250_19609.is_pattern);
          instantiate_imp = (uu___250_19609.instantiate_imp);
          effects = (uu___250_19609.effects);
          generalize = (uu___250_19609.generalize);
          letrecs = (uu___250_19609.letrecs);
          top_level = (uu___250_19609.top_level);
          check_uvars = (uu___250_19609.check_uvars);
          use_eq = (uu___250_19609.use_eq);
          is_iface = (uu___250_19609.is_iface);
          admit = (uu___250_19609.admit);
          lax = (uu___250_19609.lax);
          lax_universes = (uu___250_19609.lax_universes);
          phase1 = (uu___250_19609.phase1);
          failhard = (uu___250_19609.failhard);
          nosynth = (uu___250_19609.nosynth);
          nocoerce = (uu___250_19609.nocoerce);
          uvar_subtyping = (uu___250_19609.uvar_subtyping);
          tc_term = (uu___250_19609.tc_term);
          type_of = (uu___250_19609.type_of);
          universe_of = (uu___250_19609.universe_of);
          check_type_of = (uu___250_19609.check_type_of);
          use_bv_sorts = (uu___250_19609.use_bv_sorts);
          qtbl_name_and_index = (uu___250_19609.qtbl_name_and_index);
          normalized_eff_names = (uu___250_19609.normalized_eff_names);
          proof_ns = (uu___250_19609.proof_ns);
          synth_hook = (uu___250_19609.synth_hook);
          splice = (uu___250_19609.splice);
          is_native_tactic = (uu___250_19609.is_native_tactic);
          identifier_info = (uu___250_19609.identifier_info);
          tc_hooks = (uu___250_19609.tc_hooks);
          dsenv = (uu___250_19609.dsenv);
          dep_graph = (uu___250_19609.dep_graph);
          nbe = (uu___250_19609.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___251_19622 = env  in
      {
        solver = (uu___251_19622.solver);
        range = (uu___251_19622.range);
        curmodule = (uu___251_19622.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___251_19622.gamma_sig);
        gamma_cache = (uu___251_19622.gamma_cache);
        modules = (uu___251_19622.modules);
        expected_typ = (uu___251_19622.expected_typ);
        sigtab = (uu___251_19622.sigtab);
        attrtab = (uu___251_19622.attrtab);
        is_pattern = (uu___251_19622.is_pattern);
        instantiate_imp = (uu___251_19622.instantiate_imp);
        effects = (uu___251_19622.effects);
        generalize = (uu___251_19622.generalize);
        letrecs = (uu___251_19622.letrecs);
        top_level = (uu___251_19622.top_level);
        check_uvars = (uu___251_19622.check_uvars);
        use_eq = (uu___251_19622.use_eq);
        is_iface = (uu___251_19622.is_iface);
        admit = (uu___251_19622.admit);
        lax = (uu___251_19622.lax);
        lax_universes = (uu___251_19622.lax_universes);
        phase1 = (uu___251_19622.phase1);
        failhard = (uu___251_19622.failhard);
        nosynth = (uu___251_19622.nosynth);
        nocoerce = (uu___251_19622.nocoerce);
        uvar_subtyping = (uu___251_19622.uvar_subtyping);
        tc_term = (uu___251_19622.tc_term);
        type_of = (uu___251_19622.type_of);
        universe_of = (uu___251_19622.universe_of);
        check_type_of = (uu___251_19622.check_type_of);
        use_bv_sorts = (uu___251_19622.use_bv_sorts);
        qtbl_name_and_index = (uu___251_19622.qtbl_name_and_index);
        normalized_eff_names = (uu___251_19622.normalized_eff_names);
        proof_ns = (uu___251_19622.proof_ns);
        synth_hook = (uu___251_19622.synth_hook);
        splice = (uu___251_19622.splice);
        is_native_tactic = (uu___251_19622.is_native_tactic);
        identifier_info = (uu___251_19622.identifier_info);
        tc_hooks = (uu___251_19622.tc_hooks);
        dsenv = (uu___251_19622.dsenv);
        dep_graph = (uu___251_19622.dep_graph);
        nbe = (uu___251_19622.nbe)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  ->
    fun x  -> push_local_binding env (FStar_Syntax_Syntax.Binding_var x)
  
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env  ->
    fun bvs  ->
      FStar_List.fold_left (fun env1  -> fun bv  -> push_bv env1 bv) env bvs
  
let (pop_bv :
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun env  ->
    match env.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___252_19677 = env  in
             {
               solver = (uu___252_19677.solver);
               range = (uu___252_19677.range);
               curmodule = (uu___252_19677.curmodule);
               gamma = rest;
               gamma_sig = (uu___252_19677.gamma_sig);
               gamma_cache = (uu___252_19677.gamma_cache);
               modules = (uu___252_19677.modules);
               expected_typ = (uu___252_19677.expected_typ);
               sigtab = (uu___252_19677.sigtab);
               attrtab = (uu___252_19677.attrtab);
               is_pattern = (uu___252_19677.is_pattern);
               instantiate_imp = (uu___252_19677.instantiate_imp);
               effects = (uu___252_19677.effects);
               generalize = (uu___252_19677.generalize);
               letrecs = (uu___252_19677.letrecs);
               top_level = (uu___252_19677.top_level);
               check_uvars = (uu___252_19677.check_uvars);
               use_eq = (uu___252_19677.use_eq);
               is_iface = (uu___252_19677.is_iface);
               admit = (uu___252_19677.admit);
               lax = (uu___252_19677.lax);
               lax_universes = (uu___252_19677.lax_universes);
               phase1 = (uu___252_19677.phase1);
               failhard = (uu___252_19677.failhard);
               nosynth = (uu___252_19677.nosynth);
               nocoerce = (uu___252_19677.nocoerce);
               uvar_subtyping = (uu___252_19677.uvar_subtyping);
               tc_term = (uu___252_19677.tc_term);
               type_of = (uu___252_19677.type_of);
               universe_of = (uu___252_19677.universe_of);
               check_type_of = (uu___252_19677.check_type_of);
               use_bv_sorts = (uu___252_19677.use_bv_sorts);
               qtbl_name_and_index = (uu___252_19677.qtbl_name_and_index);
               normalized_eff_names = (uu___252_19677.normalized_eff_names);
               proof_ns = (uu___252_19677.proof_ns);
               synth_hook = (uu___252_19677.synth_hook);
               splice = (uu___252_19677.splice);
               is_native_tactic = (uu___252_19677.is_native_tactic);
               identifier_info = (uu___252_19677.identifier_info);
               tc_hooks = (uu___252_19677.tc_hooks);
               dsenv = (uu___252_19677.dsenv);
               dep_graph = (uu___252_19677.dep_graph);
               nbe = (uu___252_19677.nbe)
             }))
    | uu____19678 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____19706  ->
             match uu____19706 with | (x,uu____19714) -> push_bv env1 x) env
        bs
  
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.binding)
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___253_19748 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___253_19748.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___253_19748.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___254_19788 = env  in
       {
         solver = (uu___254_19788.solver);
         range = (uu___254_19788.range);
         curmodule = (uu___254_19788.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___254_19788.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___254_19788.sigtab);
         attrtab = (uu___254_19788.attrtab);
         is_pattern = (uu___254_19788.is_pattern);
         instantiate_imp = (uu___254_19788.instantiate_imp);
         effects = (uu___254_19788.effects);
         generalize = (uu___254_19788.generalize);
         letrecs = (uu___254_19788.letrecs);
         top_level = (uu___254_19788.top_level);
         check_uvars = (uu___254_19788.check_uvars);
         use_eq = (uu___254_19788.use_eq);
         is_iface = (uu___254_19788.is_iface);
         admit = (uu___254_19788.admit);
         lax = (uu___254_19788.lax);
         lax_universes = (uu___254_19788.lax_universes);
         phase1 = (uu___254_19788.phase1);
         failhard = (uu___254_19788.failhard);
         nosynth = (uu___254_19788.nosynth);
         nocoerce = (uu___254_19788.nocoerce);
         uvar_subtyping = (uu___254_19788.uvar_subtyping);
         tc_term = (uu___254_19788.tc_term);
         type_of = (uu___254_19788.type_of);
         universe_of = (uu___254_19788.universe_of);
         check_type_of = (uu___254_19788.check_type_of);
         use_bv_sorts = (uu___254_19788.use_bv_sorts);
         qtbl_name_and_index = (uu___254_19788.qtbl_name_and_index);
         normalized_eff_names = (uu___254_19788.normalized_eff_names);
         proof_ns = (uu___254_19788.proof_ns);
         synth_hook = (uu___254_19788.synth_hook);
         splice = (uu___254_19788.splice);
         is_native_tactic = (uu___254_19788.is_native_tactic);
         identifier_info = (uu___254_19788.identifier_info);
         tc_hooks = (uu___254_19788.tc_hooks);
         dsenv = (uu___254_19788.dsenv);
         dep_graph = (uu___254_19788.dep_graph);
         nbe = (uu___254_19788.nbe)
       })
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun x  ->
             push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ x))
        env xs
  
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____19830 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____19830 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____19858 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____19858)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___255_19873 = env  in
      {
        solver = (uu___255_19873.solver);
        range = (uu___255_19873.range);
        curmodule = (uu___255_19873.curmodule);
        gamma = (uu___255_19873.gamma);
        gamma_sig = (uu___255_19873.gamma_sig);
        gamma_cache = (uu___255_19873.gamma_cache);
        modules = (uu___255_19873.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___255_19873.sigtab);
        attrtab = (uu___255_19873.attrtab);
        is_pattern = (uu___255_19873.is_pattern);
        instantiate_imp = (uu___255_19873.instantiate_imp);
        effects = (uu___255_19873.effects);
        generalize = (uu___255_19873.generalize);
        letrecs = (uu___255_19873.letrecs);
        top_level = (uu___255_19873.top_level);
        check_uvars = (uu___255_19873.check_uvars);
        use_eq = false;
        is_iface = (uu___255_19873.is_iface);
        admit = (uu___255_19873.admit);
        lax = (uu___255_19873.lax);
        lax_universes = (uu___255_19873.lax_universes);
        phase1 = (uu___255_19873.phase1);
        failhard = (uu___255_19873.failhard);
        nosynth = (uu___255_19873.nosynth);
        nocoerce = (uu___255_19873.nocoerce);
        uvar_subtyping = (uu___255_19873.uvar_subtyping);
        tc_term = (uu___255_19873.tc_term);
        type_of = (uu___255_19873.type_of);
        universe_of = (uu___255_19873.universe_of);
        check_type_of = (uu___255_19873.check_type_of);
        use_bv_sorts = (uu___255_19873.use_bv_sorts);
        qtbl_name_and_index = (uu___255_19873.qtbl_name_and_index);
        normalized_eff_names = (uu___255_19873.normalized_eff_names);
        proof_ns = (uu___255_19873.proof_ns);
        synth_hook = (uu___255_19873.synth_hook);
        splice = (uu___255_19873.splice);
        is_native_tactic = (uu___255_19873.is_native_tactic);
        identifier_info = (uu___255_19873.identifier_info);
        tc_hooks = (uu___255_19873.tc_hooks);
        dsenv = (uu___255_19873.dsenv);
        dep_graph = (uu___255_19873.dep_graph);
        nbe = (uu___255_19873.nbe)
      }
  
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  
let (clear_expected_typ :
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun env_  ->
    let uu____19901 = expected_typ env_  in
    ((let uu___256_19907 = env_  in
      {
        solver = (uu___256_19907.solver);
        range = (uu___256_19907.range);
        curmodule = (uu___256_19907.curmodule);
        gamma = (uu___256_19907.gamma);
        gamma_sig = (uu___256_19907.gamma_sig);
        gamma_cache = (uu___256_19907.gamma_cache);
        modules = (uu___256_19907.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___256_19907.sigtab);
        attrtab = (uu___256_19907.attrtab);
        is_pattern = (uu___256_19907.is_pattern);
        instantiate_imp = (uu___256_19907.instantiate_imp);
        effects = (uu___256_19907.effects);
        generalize = (uu___256_19907.generalize);
        letrecs = (uu___256_19907.letrecs);
        top_level = (uu___256_19907.top_level);
        check_uvars = (uu___256_19907.check_uvars);
        use_eq = false;
        is_iface = (uu___256_19907.is_iface);
        admit = (uu___256_19907.admit);
        lax = (uu___256_19907.lax);
        lax_universes = (uu___256_19907.lax_universes);
        phase1 = (uu___256_19907.phase1);
        failhard = (uu___256_19907.failhard);
        nosynth = (uu___256_19907.nosynth);
        nocoerce = (uu___256_19907.nocoerce);
        uvar_subtyping = (uu___256_19907.uvar_subtyping);
        tc_term = (uu___256_19907.tc_term);
        type_of = (uu___256_19907.type_of);
        universe_of = (uu___256_19907.universe_of);
        check_type_of = (uu___256_19907.check_type_of);
        use_bv_sorts = (uu___256_19907.use_bv_sorts);
        qtbl_name_and_index = (uu___256_19907.qtbl_name_and_index);
        normalized_eff_names = (uu___256_19907.normalized_eff_names);
        proof_ns = (uu___256_19907.proof_ns);
        synth_hook = (uu___256_19907.synth_hook);
        splice = (uu___256_19907.splice);
        is_native_tactic = (uu___256_19907.is_native_tactic);
        identifier_info = (uu___256_19907.identifier_info);
        tc_hooks = (uu___256_19907.tc_hooks);
        dsenv = (uu___256_19907.dsenv);
        dep_graph = (uu___256_19907.dep_graph);
        nbe = (uu___256_19907.nbe)
      }), uu____19901)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____19917 =
      let uu____19920 = FStar_Ident.id_of_text ""  in [uu____19920]  in
    FStar_Ident.lid_of_ids uu____19917  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____19926 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____19926
        then
          let uu____19929 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____19929 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___257_19956 = env  in
       {
         solver = (uu___257_19956.solver);
         range = (uu___257_19956.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___257_19956.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___257_19956.expected_typ);
         sigtab = (uu___257_19956.sigtab);
         attrtab = (uu___257_19956.attrtab);
         is_pattern = (uu___257_19956.is_pattern);
         instantiate_imp = (uu___257_19956.instantiate_imp);
         effects = (uu___257_19956.effects);
         generalize = (uu___257_19956.generalize);
         letrecs = (uu___257_19956.letrecs);
         top_level = (uu___257_19956.top_level);
         check_uvars = (uu___257_19956.check_uvars);
         use_eq = (uu___257_19956.use_eq);
         is_iface = (uu___257_19956.is_iface);
         admit = (uu___257_19956.admit);
         lax = (uu___257_19956.lax);
         lax_universes = (uu___257_19956.lax_universes);
         phase1 = (uu___257_19956.phase1);
         failhard = (uu___257_19956.failhard);
         nosynth = (uu___257_19956.nosynth);
         nocoerce = (uu___257_19956.nocoerce);
         uvar_subtyping = (uu___257_19956.uvar_subtyping);
         tc_term = (uu___257_19956.tc_term);
         type_of = (uu___257_19956.type_of);
         universe_of = (uu___257_19956.universe_of);
         check_type_of = (uu___257_19956.check_type_of);
         use_bv_sorts = (uu___257_19956.use_bv_sorts);
         qtbl_name_and_index = (uu___257_19956.qtbl_name_and_index);
         normalized_eff_names = (uu___257_19956.normalized_eff_names);
         proof_ns = (uu___257_19956.proof_ns);
         synth_hook = (uu___257_19956.synth_hook);
         splice = (uu___257_19956.splice);
         is_native_tactic = (uu___257_19956.is_native_tactic);
         identifier_info = (uu___257_19956.identifier_info);
         tc_hooks = (uu___257_19956.tc_hooks);
         dsenv = (uu___257_19956.dsenv);
         dep_graph = (uu___257_19956.dep_graph);
         nbe = (uu___257_19956.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20007)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20011,(uu____20012,t)))::tl1
          ->
          let uu____20033 =
            let uu____20036 = FStar_Syntax_Free.uvars t  in
            ext out uu____20036  in
          aux uu____20033 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20039;
            FStar_Syntax_Syntax.index = uu____20040;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20047 =
            let uu____20050 = FStar_Syntax_Free.uvars t  in
            ext out uu____20050  in
          aux uu____20047 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20107)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20111,(uu____20112,t)))::tl1
          ->
          let uu____20133 =
            let uu____20136 = FStar_Syntax_Free.univs t  in
            ext out uu____20136  in
          aux uu____20133 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20139;
            FStar_Syntax_Syntax.index = uu____20140;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20147 =
            let uu____20150 = FStar_Syntax_Free.univs t  in
            ext out uu____20150  in
          aux uu____20147 tl1
       in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl1 ->
          let uu____20211 = FStar_Util.set_add uname out  in
          aux uu____20211 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____20214,(uu____20215,t)))::tl1
          ->
          let uu____20236 =
            let uu____20239 = FStar_Syntax_Free.univnames t  in
            ext out uu____20239  in
          aux uu____20236 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20242;
            FStar_Syntax_Syntax.index = uu____20243;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20250 =
            let uu____20253 = FStar_Syntax_Free.univnames t  in
            ext out uu____20253  in
          aux uu____20250 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___231_20273  ->
            match uu___231_20273 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20277 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20290 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____20300 =
      let uu____20309 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____20309
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____20300 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____20353 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___232_20363  ->
              match uu___232_20363 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20365 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____20365
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____20368) ->
                  let uu____20385 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____20385))
       in
    FStar_All.pipe_right uu____20353 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___233_20392  ->
    match uu___233_20392 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20394 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____20394
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20414  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____20456) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20475,uu____20476) -> false  in
      let uu____20485 =
        FStar_List.tryFind
          (fun uu____20503  ->
             match uu____20503 with | (p,uu____20511) -> list_prefix p path)
          env.proof_ns
         in
      match uu____20485 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____20522,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20544 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____20544
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___258_20562 = e  in
        {
          solver = (uu___258_20562.solver);
          range = (uu___258_20562.range);
          curmodule = (uu___258_20562.curmodule);
          gamma = (uu___258_20562.gamma);
          gamma_sig = (uu___258_20562.gamma_sig);
          gamma_cache = (uu___258_20562.gamma_cache);
          modules = (uu___258_20562.modules);
          expected_typ = (uu___258_20562.expected_typ);
          sigtab = (uu___258_20562.sigtab);
          attrtab = (uu___258_20562.attrtab);
          is_pattern = (uu___258_20562.is_pattern);
          instantiate_imp = (uu___258_20562.instantiate_imp);
          effects = (uu___258_20562.effects);
          generalize = (uu___258_20562.generalize);
          letrecs = (uu___258_20562.letrecs);
          top_level = (uu___258_20562.top_level);
          check_uvars = (uu___258_20562.check_uvars);
          use_eq = (uu___258_20562.use_eq);
          is_iface = (uu___258_20562.is_iface);
          admit = (uu___258_20562.admit);
          lax = (uu___258_20562.lax);
          lax_universes = (uu___258_20562.lax_universes);
          phase1 = (uu___258_20562.phase1);
          failhard = (uu___258_20562.failhard);
          nosynth = (uu___258_20562.nosynth);
          nocoerce = (uu___258_20562.nocoerce);
          uvar_subtyping = (uu___258_20562.uvar_subtyping);
          tc_term = (uu___258_20562.tc_term);
          type_of = (uu___258_20562.type_of);
          universe_of = (uu___258_20562.universe_of);
          check_type_of = (uu___258_20562.check_type_of);
          use_bv_sorts = (uu___258_20562.use_bv_sorts);
          qtbl_name_and_index = (uu___258_20562.qtbl_name_and_index);
          normalized_eff_names = (uu___258_20562.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___258_20562.synth_hook);
          splice = (uu___258_20562.splice);
          is_native_tactic = (uu___258_20562.is_native_tactic);
          identifier_info = (uu___258_20562.identifier_info);
          tc_hooks = (uu___258_20562.tc_hooks);
          dsenv = (uu___258_20562.dsenv);
          dep_graph = (uu___258_20562.dep_graph);
          nbe = (uu___258_20562.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___259_20602 = e  in
      {
        solver = (uu___259_20602.solver);
        range = (uu___259_20602.range);
        curmodule = (uu___259_20602.curmodule);
        gamma = (uu___259_20602.gamma);
        gamma_sig = (uu___259_20602.gamma_sig);
        gamma_cache = (uu___259_20602.gamma_cache);
        modules = (uu___259_20602.modules);
        expected_typ = (uu___259_20602.expected_typ);
        sigtab = (uu___259_20602.sigtab);
        attrtab = (uu___259_20602.attrtab);
        is_pattern = (uu___259_20602.is_pattern);
        instantiate_imp = (uu___259_20602.instantiate_imp);
        effects = (uu___259_20602.effects);
        generalize = (uu___259_20602.generalize);
        letrecs = (uu___259_20602.letrecs);
        top_level = (uu___259_20602.top_level);
        check_uvars = (uu___259_20602.check_uvars);
        use_eq = (uu___259_20602.use_eq);
        is_iface = (uu___259_20602.is_iface);
        admit = (uu___259_20602.admit);
        lax = (uu___259_20602.lax);
        lax_universes = (uu___259_20602.lax_universes);
        phase1 = (uu___259_20602.phase1);
        failhard = (uu___259_20602.failhard);
        nosynth = (uu___259_20602.nosynth);
        nocoerce = (uu___259_20602.nocoerce);
        uvar_subtyping = (uu___259_20602.uvar_subtyping);
        tc_term = (uu___259_20602.tc_term);
        type_of = (uu___259_20602.type_of);
        universe_of = (uu___259_20602.universe_of);
        check_type_of = (uu___259_20602.check_type_of);
        use_bv_sorts = (uu___259_20602.use_bv_sorts);
        qtbl_name_and_index = (uu___259_20602.qtbl_name_and_index);
        normalized_eff_names = (uu___259_20602.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___259_20602.synth_hook);
        splice = (uu___259_20602.splice);
        is_native_tactic = (uu___259_20602.is_native_tactic);
        identifier_info = (uu___259_20602.identifier_info);
        tc_hooks = (uu___259_20602.tc_hooks);
        dsenv = (uu___259_20602.dsenv);
        dep_graph = (uu___259_20602.dep_graph);
        nbe = (uu___259_20602.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____20617 = FStar_Syntax_Free.names t  in
      let uu____20620 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____20617 uu____20620
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____20641 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____20641
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____20649 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____20649
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____20666 =
      match uu____20666 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20676 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____20676)
       in
    let uu____20678 =
      let uu____20681 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____20681 FStar_List.rev  in
    FStar_All.pipe_right uu____20678 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    { guard_f = g; deferred = []; univ_ineqs = ([], []); implicits = [] }
  
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.guard_f 
let (is_trivial : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = [];
        univ_ineqs = ([],[]); implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check =
                   FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____20734 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____20734 with
                   | FStar_Pervasives_Native.Some uu____20737 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____20738 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____20744;
        univ_ineqs = uu____20745; implicits = uu____20746;_} -> true
    | uu____20757 -> false
  
let (trivial_guard : guard_t) =
  {
    guard_f = FStar_TypeChecker_Common.Trivial;
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  } 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs  ->
    fun g  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___260_20784 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___260_20784.deferred);
            univ_ineqs = (uu___260_20784.univ_ineqs);
            implicits = (uu___260_20784.implicits)
          }
  
let (abstract_guard : FStar_Syntax_Syntax.binder -> guard_t -> guard_t) =
  fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun vset  ->
        fun t  ->
          let uu____20819 = FStar_Options.defensive ()  in
          if uu____20819
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____20823 =
              let uu____20824 =
                let uu____20825 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____20825  in
              Prims.op_Negation uu____20824  in
            (if uu____20823
             then
               let uu____20830 =
                 let uu____20835 =
                   let uu____20836 = FStar_Syntax_Print.term_to_string t  in
                   let uu____20837 =
                     let uu____20838 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____20838
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____20836 uu____20837
                    in
                 (FStar_Errors.Warning_Defensive, uu____20835)  in
               FStar_Errors.log_issue rng uu____20830
             else ())
          else ()
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____20869 =
            let uu____20870 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20870  in
          if uu____20869
          then ()
          else
            (let uu____20872 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____20872 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____20895 =
            let uu____20896 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____20896  in
          if uu____20895
          then ()
          else
            (let uu____20898 = bound_vars e  in
             def_check_closed_in rng msg uu____20898 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___261_20933 = g  in
          let uu____20934 =
            let uu____20935 =
              let uu____20936 =
                let uu____20943 =
                  let uu____20944 =
                    let uu____20961 =
                      let uu____20972 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____20972]  in
                    (f, uu____20961)  in
                  FStar_Syntax_Syntax.Tm_app uu____20944  in
                FStar_Syntax_Syntax.mk uu____20943  in
              uu____20936 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____20935
             in
          {
            guard_f = uu____20934;
            deferred = (uu___261_20933.deferred);
            univ_ineqs = (uu___261_20933.univ_ineqs);
            implicits = (uu___261_20933.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___262_21028 = g  in
          let uu____21029 =
            let uu____21030 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____21030  in
          {
            guard_f = uu____21029;
            deferred = (uu___262_21028.deferred);
            univ_ineqs = (uu___262_21028.univ_ineqs);
            implicits = (uu___262_21028.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____21036 ->
        failwith "impossible"
  
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____21051 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____21051
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____21057 =
      let uu____21058 = FStar_Syntax_Util.unmeta t  in
      uu____21058.FStar_Syntax_Syntax.n  in
    match uu____21057 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____21062 -> FStar_TypeChecker_Common.NonTrivial t
  
let (imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    -> guard_t -> guard_t -> guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____21103 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____21103;
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
  
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____21184 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____21184
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___263_21188 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___263_21188.deferred);
              univ_ineqs = (uu___263_21188.univ_ineqs);
              implicits = (uu___263_21188.implicits)
            }
  
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____21221 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____21221
               then f1
               else
                 (let u =
                    env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___264_21244 = g  in
            let uu____21245 =
              let uu____21246 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____21246  in
            {
              guard_f = uu____21245;
              deferred = (uu___264_21244.deferred);
              univ_ineqs = (uu___264_21244.univ_ineqs);
              implicits = (uu___264_21244.implicits)
            }
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.ctx_uvar,FStar_Range.range)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list,guard_t)
              FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          fun should_check  ->
            let uu____21284 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____21284 with
            | FStar_Pervasives_Native.Some
                (uu____21309::(tm,uu____21311)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____21375 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____21393 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21393;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  }  in
                (FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                   true gamma binders;
                 (let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_uvar
                         (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                      FStar_Pervasives_Native.None r
                     in
                  let imp =
                    {
                      imp_reason = reason;
                      imp_uvar = ctx_uvar;
                      imp_tm = t;
                      imp_range = r;
                      imp_meta = FStar_Pervasives_Native.None
                    }  in
                  let g =
                    let uu___265_21428 = trivial_guard  in
                    {
                      guard_f = (uu___265_21428.guard_f);
                      deferred = (uu___265_21428.deferred);
                      univ_ineqs = (uu___265_21428.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21445  -> ());
    push = (fun uu____21447  -> ());
    pop = (fun uu____21449  -> ());
    snapshot =
      (fun uu____21451  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21460  -> fun uu____21461  -> ());
    encode_modul = (fun uu____21472  -> fun uu____21473  -> ());
    encode_sig = (fun uu____21476  -> fun uu____21477  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____21483 =
             let uu____21490 = FStar_Options.peek ()  in (e, g, uu____21490)
              in
           [uu____21483]);
    solve = (fun uu____21506  -> fun uu____21507  -> fun uu____21508  -> ());
    finish = (fun uu____21514  -> ());
    refresh = (fun uu____21516  -> ())
  } 