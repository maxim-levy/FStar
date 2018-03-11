open Prims
let add_fuel :
  'Auu____4 . 'Auu____4 -> 'Auu____4 Prims.list -> 'Auu____4 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____19 = FStar_Options.unthrottle_inductives ()  in
      if uu____19 then tl1 else x :: tl1
  
let withenv :
  'Auu____28 'Auu____29 'Auu____30 .
    'Auu____28 ->
      ('Auu____29,'Auu____30) FStar_Pervasives_Native.tuple2 ->
        ('Auu____29,'Auu____30,'Auu____28) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____48  -> match uu____48 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____59 'Auu____60 'Auu____61 .
    (('Auu____59,'Auu____60) FStar_Util.either,'Auu____61)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____59,'Auu____60) FStar_Util.either,'Auu____61)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___79_107  ->
         match uu___79_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___102_143 = a  in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___102_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___102_143.FStar_Syntax_Syntax.sort)
        }  in
      let uu____145 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____145
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____158 =
          let uu____159 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____159  in
        let uu____160 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____160 with
        | (uu____165,t) ->
            let uu____167 =
              let uu____168 = FStar_Syntax_Subst.compress t  in
              uu____168.FStar_Syntax_Syntax.n  in
            (match uu____167 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____189 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____189 with
                  | (binders,uu____195) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____210 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____217 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____217
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____224 =
        let uu____229 = mk_term_projector_name lid a  in
        (uu____229,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____224
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____236 =
        let uu____241 = mk_term_projector_name_by_pos lid i  in
        (uu____241,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____236
  
let mk_data_tester :
  'Auu____246 .
    'Auu____246 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
  
type varops_t =
  {
  push: Prims.unit -> Prims.unit ;
  pop: Prims.unit -> Prims.unit ;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: Prims.unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }[@@deriving show]
let (__proj__Mkvarops_t__item__push : varops_t -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
  
let (__proj__Mkvarops_t__item__pop : varops_t -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> Prims.unit -> Prims.int)
  =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____610 =
    let uu____611 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____614 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____611, uu____614)  in
  let scopes =
    let uu____634 = let uu____645 = new_scope ()  in [uu____645]  in
    FStar_Util.mk_ref uu____634  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____686 =
        let uu____689 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____689
          (fun uu____772  ->
             match uu____772 with
             | (names1,uu____784) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____686 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____793 ->
          (FStar_Util.incr ctr;
           (let uu____828 =
              let uu____829 =
                let uu____830 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____830  in
              Prims.strcat "__" uu____829  in
            Prims.strcat y1 uu____828))
       in
    let top_scope =
      let uu____875 =
        let uu____884 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____884
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____875  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____993 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1073 =
      let uu____1074 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1074  in
    FStar_Util.format2 "%s_%s" pfx uu____1073  in
  let string_const s =
    let uu____1079 =
      let uu____1082 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1082
        (fun uu____1165  ->
           match uu____1165 with
           | (uu____1176,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1079 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1189 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1189  in
        let top_scope =
          let uu____1193 =
            let uu____1202 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1202  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1193  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1300 =
    let uu____1301 =
      let uu____1312 = new_scope ()  in
      let uu____1321 = FStar_ST.op_Bang scopes  in uu____1312 :: uu____1321
       in
    FStar_ST.op_Colon_Equals scopes uu____1301  in
  let pop1 uu____1465 =
    let uu____1466 =
      let uu____1477 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1477
       in
    FStar_ST.op_Colon_Equals scopes uu____1466  in
  {
    push = push1;
    pop = pop1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  } 
let (unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv) =
  fun x  ->
    let uu___103_1621 = x  in
    let uu____1622 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1622;
      FStar_Syntax_Syntax.index = (uu___103_1621.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___103_1621.FStar_Syntax_Syntax.sort)
    }
  
type fvar_binding =
  {
  fvar_lid: FStar_Ident.lident ;
  smt_arity: Prims.int ;
  smt_id: Prims.string ;
  smt_token: FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ;
  smt_fuel_partial_app:
    FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option }[@@deriving
                                                                  show]
let (__proj__Mkfvar_binding__item__fvar_lid :
  fvar_binding -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__fvar_lid
  
let (__proj__Mkfvar_binding__item__smt_arity : fvar_binding -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_arity
  
let (__proj__Mkfvar_binding__item__smt_id : fvar_binding -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_id
  
let (__proj__Mkfvar_binding__item__smt_token :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_token
  
let (__proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_fuel_partial_app
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2 
  | Binding_fvar of fvar_binding [@@deriving show]
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1735 -> false
  
let (__proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_fvar : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1759 -> false
  
let (__proj__Binding_fvar__item___0 : binding -> fvar_binding) =
  fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar :
  'Auu____1770 'Auu____1771 .
    'Auu____1770 ->
      ('Auu____1770,'Auu____1771 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }[@@deriving show]
let (__proj__Mkcache_entry__item__cache_symbol_name :
  cache_entry -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
  
let (__proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
  
let (__proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
  
let (__proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_assumption_names
  
type env_t =
  {
  bindings: binding Prims.list ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  cache: cache_entry FStar_Util.smap ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string }[@@deriving show]
let (__proj__Mkenv_t__item__bindings : env_t -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__bindings
  
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__depth
  
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__tcenv
  
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__warn
  
let (__proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__cache
  
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__nolabels
  
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__use_zfuel_name
  
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__encode_non_total_function_typ
  
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__current_module_name
  
let mk_cache_entry :
  'Auu____2067 .
    'Auu____2067 ->
      Prims.string ->
        FStar_SMTEncoding_Term.sort Prims.list ->
          FStar_SMTEncoding_Term.decl Prims.list -> cache_entry
  =
  fun env  ->
    fun tsym  ->
      fun cvar_sorts  ->
        fun t_decls1  ->
          let names1 =
            FStar_All.pipe_right t_decls1
              (FStar_List.collect
                 (fun uu___80_2101  ->
                    match uu___80_2101 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2105 -> []))
             in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls1;
            cache_symbol_assumption_names = names1
          }
  
let (use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
  
let (print_env : env_t -> Prims.string) =
  fun e  ->
    let uu____2114 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___81_2124  ->
              match uu___81_2124 with
              | Binding_var (x,uu____2126) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar fvb ->
                  FStar_Syntax_Print.lid_to_string fvb.fvar_lid))
       in
    FStar_All.pipe_right uu____2114 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2133 .
    env_t ->
      (binding -> 'Auu____2133 FStar_Pervasives_Native.option) ->
        'Auu____2133 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let (caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____2161 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2161
      then
        let uu____2164 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2164
      else FStar_Pervasives_Native.None
  
let (fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____2177 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2177)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___104_2193 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___104_2193.tcenv);
           warn = (uu___104_2193.warn);
           cache = (uu___104_2193.cache);
           nolabels = (uu___104_2193.nolabels);
           use_zfuel_name = (uu___104_2193.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___104_2193.encode_non_total_function_typ);
           current_module_name = (uu___104_2193.current_module_name)
         }))
  
let (new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      (ysym, y,
        (let uu___105_2211 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___105_2211.depth);
           tcenv = (uu___105_2211.tcenv);
           warn = (uu___105_2211.warn);
           cache = (uu___105_2211.cache);
           nolabels = (uu___105_2211.nolabels);
           use_zfuel_name = (uu___105_2211.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___105_2211.encode_non_total_function_typ);
           current_module_name = (uu___105_2211.current_module_name)
         }))
  
let (new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        (ysym, y,
          (let uu___106_2232 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___106_2232.depth);
             tcenv = (uu___106_2232.tcenv);
             warn = (uu___106_2232.warn);
             cache = (uu___106_2232.cache);
             nolabels = (uu___106_2232.nolabels);
             use_zfuel_name = (uu___106_2232.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___106_2232.encode_non_total_function_typ);
             current_module_name = (uu___106_2232.current_module_name)
           }))
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___107_2242 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___107_2242.depth);
          tcenv = (uu___107_2242.tcenv);
          warn = (uu___107_2242.warn);
          cache = (uu___107_2242.cache);
          nolabels = (uu___107_2242.nolabels);
          use_zfuel_name = (uu___107_2242.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___107_2242.encode_non_total_function_typ);
          current_module_name = (uu___107_2242.current_module_name)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___82_2266  ->
             match uu___82_2266 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2279 -> FStar_Pervasives_Native.None)
         in
      let uu____2284 = aux a  in
      match uu____2284 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2296 = aux a2  in
          (match uu____2296 with
           | FStar_Pervasives_Native.None  ->
               let uu____2307 =
                 let uu____2308 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2309 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2308 uu____2309
                  in
               failwith uu____2307
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let (mk_fvb :
  FStar_Ident.lident ->
    Prims.string ->
      Prims.int ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            fvar_binding)
  =
  fun lid  ->
    fun fname  ->
      fun arity  ->
        fun ftok  ->
          fun fuel_partial_app  ->
            {
              fvar_lid = lid;
              smt_arity = arity;
              smt_id = fname;
              smt_token = ftok;
              smt_fuel_partial_app = fuel_partial_app
            }
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let fname = varops.new_fvar x  in
        let ftok_name = Prims.strcat fname "@tok"  in
        let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
        let fvb =
          mk_fvb x fname arity (FStar_Pervasives_Native.Some ftok)
            FStar_Pervasives_Native.None
           in
        (fname, ftok_name,
          (let uu___108_2367 = env  in
           {
             bindings = ((Binding_fvar fvb) :: (env.bindings));
             depth = (uu___108_2367.depth);
             tcenv = (uu___108_2367.tcenv);
             warn = (uu___108_2367.warn);
             cache = (uu___108_2367.cache);
             nolabels = (uu___108_2367.nolabels);
             use_zfuel_name = (uu___108_2367.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___108_2367.encode_non_total_function_typ);
             current_module_name = (uu___108_2367.current_module_name)
           }))
  
let (try_lookup_lid :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___83_2378  ->
           match uu___83_2378 with
           | Binding_fvar fvb when FStar_Ident.lid_equals fvb.fvar_lid a ->
               FStar_Pervasives_Native.Some fvb
           | uu____2382 -> FStar_Pervasives_Native.None)
  
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env  ->
    fun s  ->
      let uu____2389 =
        lookup_binding env
          (fun uu___84_2394  ->
             match uu___84_2394 with
             | Binding_fvar fvb when (fvb.fvar_lid).FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2398 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____2389 FStar_Option.isSome
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____2407 = try_lookup_lid env a  in
      match uu____2407 with
      | FStar_Pervasives_Native.None  ->
          let uu____2410 =
            let uu____2411 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____2411  in
          failwith uu____2410
      | FStar_Pervasives_Native.Some s -> s
  
let (push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t)
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun fname  ->
          fun ftok  ->
            let fvb = mk_fvb x fname arity ftok FStar_Pervasives_Native.None
               in
            let uu___109_2433 = env  in
            {
              bindings = ((Binding_fvar fvb) :: (env.bindings));
              depth = (uu___109_2433.depth);
              tcenv = (uu___109_2433.tcenv);
              warn = (uu___109_2433.warn);
              cache = (uu___109_2433.cache);
              nolabels = (uu___109_2433.nolabels);
              use_zfuel_name = (uu___109_2433.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___109_2433.encode_non_total_function_typ);
              current_module_name = (uu___109_2433.current_module_name)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____2445 =
            let uu____2452 =
              let uu____2455 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____2455]  in
            (f, uu____2452)  in
          FStar_SMTEncoding_Util.mkApp uu____2445  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___110_2461 = env  in
        {
          bindings = ((Binding_fvar fvb1) :: (env.bindings));
          depth = (uu___110_2461.depth);
          tcenv = (uu___110_2461.tcenv);
          warn = (uu___110_2461.warn);
          cache = (uu___110_2461.cache);
          nolabels = (uu___110_2461.nolabels);
          use_zfuel_name = (uu___110_2461.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___110_2461.encode_non_total_function_typ);
          current_module_name = (uu___110_2461.current_module_name)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2470 = try_lookup_lid env l  in
      match uu____2470 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2479 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2487,fuel::[]) ->
                         let uu____2491 =
                           let uu____2492 =
                             let uu____2493 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____2493
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____2492 "fuel"  in
                         if uu____2491
                         then
                           let uu____2496 =
                             let uu____2497 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2497
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_40  ->
                                FStar_Pervasives_Native.Some _0_40)
                             uu____2496
                         else FStar_Pervasives_Native.Some t
                     | uu____2501 -> FStar_Pervasives_Native.Some t)
                | uu____2502 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____2515 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____2515 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2519 =
            let uu____2520 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____2520  in
          failwith uu____2519
  
let (lookup_free_var_name :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      ((fvb.smt_id), (fvb.smt_arity))
  
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list,
        Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
            FStar_SMTEncoding_Term.freevars = uu____2565;
            FStar_SMTEncoding_Term.rng = uu____2566;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____2581 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____2609 ->
                    ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                      (fvb.smt_arity))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___85_2622  ->
           match uu___85_2622 with
           | Binding_fvar fvb when fvb.smt_id = nm -> fvb.smt_token
           | uu____2626 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____2630 .
    'Auu____2630 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____2648  ->
      match uu____2648 with
      | (pats,vars,body) ->
          let fallback uu____2673 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____2678 = FStar_Options.unthrottle_inductives ()  in
          if uu____2678
          then fallback ()
          else
            (let uu____2680 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____2680 with
             | (fsym,fterm) ->
                 let add_fuel1 tms =
                   FStar_All.pipe_right tms
                     (FStar_List.map
                        (fun p  ->
                           match p.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var "HasType",args) ->
                               FStar_SMTEncoding_Util.mkApp
                                 ("HasTypeFuel", (fterm :: args))
                           | uu____2711 -> p))
                    in
                 let pats1 = FStar_List.map add_fuel1 pats  in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____2732 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____2732
                         | uu____2735 ->
                             let uu____2736 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____2736 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____2741 -> body  in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars
                    in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
  
let (mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term)
  = mkForall_fuel' (Prims.parse_int "1") 
let (head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____2782 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2795 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2802 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2803 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2820 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2837 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2839 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2839 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2857;
             FStar_Syntax_Syntax.vars = uu____2858;_},uu____2859)
          ->
          let uu____2884 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2884 FStar_Option.isNone
      | uu____2901 -> false
  
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____2908 =
        let uu____2909 = FStar_Syntax_Util.un_uinst t  in
        uu____2909.FStar_Syntax_Syntax.n  in
      match uu____2908 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2912,uu____2913,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___86_2934  ->
                  match uu___86_2934 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2935 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2937 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2937 FStar_Option.isSome
      | uu____2954 -> false
  
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      let uu____2961 = head_normal env t  in
      if uu____2961
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let (norm : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2972 =
      let uu____2973 = FStar_Syntax_Syntax.null_binder t  in [uu____2973]  in
    let uu____2974 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____2972 uu____2974 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____3012 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3012
                | s ->
                    let uu____3017 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3017) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let raise_arity_mismatch :
  'Auu____3035 .
    Prims.string ->
      Prims.int -> Prims.int -> FStar_Range.range -> 'Auu____3035
  =
  fun head1  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____3052 =
            let uu____3057 =
              let uu____3058 = FStar_Util.string_of_int arity  in
              let uu____3059 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____3058 uu____3059
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____3057)  in
          FStar_Errors.raise_error uu____3052 rng
  
let (maybe_curry_app :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.op ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun head1  ->
      fun arity  ->
        fun args  ->
          let n_args = FStar_List.length args  in
          if n_args = arity
          then FStar_SMTEncoding_Util.mkApp' (head1, args)
          else
            if n_args > arity
            then
              (let uu____3090 = FStar_Util.first_N arity args  in
               match uu____3090 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____3113 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____3113 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___87_3120  ->
    match uu___87_3120 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3121 -> false
  
let (is_an_eta_expansion :
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____3157;
                       FStar_SMTEncoding_Term.rng = uu____3158;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3181) ->
              let uu____3190 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3201 -> false) args (FStar_List.rev xs))
                 in
              if uu____3190
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3205,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3209 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3213 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3213))
                 in
              if uu____3209
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3217 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }[@@deriving show]
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
  
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
  
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____3439 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3443 -> false
  
let (as_function_typ :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____3462 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3475 ->
            let uu____3482 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____3482
        | uu____3483 ->
            if norm1
            then let uu____3484 = whnf env t1  in aux false uu____3484
            else
              (let uu____3486 =
                 let uu____3487 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____3488 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3487 uu____3488
                  in
               failwith uu____3486)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3520) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3525 ->
        let uu____3526 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____3526)
  
let is_arithmetic_primitive :
  'Auu____3540 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3540 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3560::uu____3561::[]) ->
          ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.op_Subtraction))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.op_Multiply))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3565::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3568 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3589 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____3604 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____3608 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____3608)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____3647)::uu____3648::uu____3649::[]) ->
          (((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_and_lid)
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.bv_xor_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.bv_or_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_add_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_sub_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_shift_left_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_shift_right_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_udiv_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.bv_mod_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_uext_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____3700)::uu____3701::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____3738 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____3957 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____3957, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____3960 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____3960, [])
      | FStar_Const.Const_char c1 ->
          let uu____3964 =
            let uu____3965 =
              let uu____3972 =
                let uu____3975 =
                  let uu____3976 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____3976  in
                [uu____3975]  in
              ("FStar.Char.__char_of_int", uu____3972)  in
            FStar_SMTEncoding_Util.mkApp uu____3965  in
          (uu____3964, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____3992 =
            let uu____3993 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____3993  in
          (uu____3992, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4014) ->
          let uu____4015 = varops.string_const s  in (uu____4015, [])
      | FStar_Const.Const_range uu____4018 ->
          let uu____4019 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4019, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4025 =
            let uu____4026 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4026  in
          failwith uu____4025

and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____4055 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4055
         then
           let uu____4056 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4056
         else ());
        (let uu____4058 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4142  ->
                   fun b  ->
                     match uu____4142 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4221 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4237 = gen_term_var env1 x  in
                           match uu____4237 with
                           | (xxsym,xx,env') ->
                               let uu____4261 =
                                 let uu____4266 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____4266 env1 xx
                                  in
                               (match uu____4261 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4221 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4058 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4425 = encode_term t env  in
          match uu____4425 with
          | (t1,decls) ->
              let uu____4436 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____4436, decls)

and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4447 = encode_term t env  in
          match uu____4447 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4462 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____4462, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4464 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____4464, decls))

and (encode_arith_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____4470 = encode_args args_e env  in
        match uu____4470 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4489 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____4498 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____4498  in
            let binary arg_tms1 =
              let uu____4511 =
                let uu____4512 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____4512  in
              let uu____4513 =
                let uu____4514 =
                  let uu____4515 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____4515  in
                FStar_SMTEncoding_Term.unboxInt uu____4514  in
              (uu____4511, uu____4513)  in
            let mk_default uu____4521 =
              let uu____4522 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4522 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l a op mk_args ts =
              let uu____4572 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____4572
              then
                let uu____4573 =
                  let uu____4574 = mk_args ts  in op uu____4574  in
                FStar_All.pipe_right uu____4573 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____4603 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____4603
              then
                let uu____4604 = binary ts  in
                match uu____4604 with
                | (t1,t2) ->
                    let uu____4611 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____4611
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4615 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____4615
                 then
                   let uu____4616 = op (binary ts)  in
                   FStar_All.pipe_right uu____4616
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 =
              mk_l ()
                (fun a415  -> (Obj.magic FStar_SMTEncoding_Util.mkAdd) a415)
                (fun a416  -> (Obj.magic binary) a416)
               in
            let sub1 =
              mk_l ()
                (fun a417  -> (Obj.magic FStar_SMTEncoding_Util.mkSub) a417)
                (fun a418  -> (Obj.magic binary) a418)
               in
            let minus =
              mk_l ()
                (fun a419  -> (Obj.magic FStar_SMTEncoding_Util.mkMinus) a419)
                (fun a420  -> (Obj.magic unary) a420)
               in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)]  in
            let uu____4739 =
              let uu____4748 =
                FStar_List.tryFind
                  (fun uu____4770  ->
                     match uu____4770 with
                     | (l,uu____4780) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____4748 FStar_Util.must  in
            (match uu____4739 with
             | (uu____4819,op) ->
                 let uu____4829 = op arg_tms  in (uu____4829, decls))

and (encode_BitVector_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____4837 = FStar_List.hd args_e  in
        match uu____4837 with
        | (tm_sz,uu____4845) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____4855 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____4855 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____4863 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____4863);
                   t_decls1)
               in
            let uu____4864 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____4884::(sz_arg,uu____4886)::uu____4887::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____4936 =
                    let uu____4939 = FStar_List.tail args_e  in
                    FStar_List.tail uu____4939  in
                  let uu____4942 =
                    let uu____4945 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____4945  in
                  (uu____4936, uu____4942)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____4951::(sz_arg,uu____4953)::uu____4954::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5003 =
                    let uu____5004 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5004
                     in
                  failwith uu____5003
              | uu____5013 ->
                  let uu____5020 = FStar_List.tail args_e  in
                  (uu____5020, FStar_Pervasives_Native.None)
               in
            (match uu____4864 with
             | (arg_tms,ext_sz) ->
                 let uu____5043 = encode_args arg_tms env  in
                 (match uu____5043 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5064 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5073 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5073  in
                      let unary_arith arg_tms2 =
                        let uu____5082 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5082  in
                      let binary arg_tms2 =
                        let uu____5095 =
                          let uu____5096 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5096
                           in
                        let uu____5097 =
                          let uu____5098 =
                            let uu____5099 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5099  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5098
                           in
                        (uu____5095, uu____5097)  in
                      let binary_arith arg_tms2 =
                        let uu____5114 =
                          let uu____5115 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5115
                           in
                        let uu____5116 =
                          let uu____5117 =
                            let uu____5118 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5118  in
                          FStar_SMTEncoding_Term.unboxInt uu____5117  in
                        (uu____5114, uu____5116)  in
                      let mk_bv a op mk_args resBox ts =
                        let uu____5160 =
                          let uu____5161 = mk_args ts  in op uu____5161  in
                        FStar_All.pipe_right uu____5160 resBox  in
                      let bv_and =
                        mk_bv ()
                          (fun a421  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAnd) a421)
                          (fun a422  -> (Obj.magic binary) a422)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv ()
                          (fun a423  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvXor) a423)
                          (fun a424  -> (Obj.magic binary) a424)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv ()
                          (fun a425  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvOr) a425)
                          (fun a426  -> (Obj.magic binary) a426)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv ()
                          (fun a427  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvAdd) a427)
                          (fun a428  -> (Obj.magic binary) a428)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv ()
                          (fun a429  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvSub) a429)
                          (fun a430  -> (Obj.magic binary) a430)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv ()
                          (fun a431  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShl sz))
                               a431)
                          (fun a432  -> (Obj.magic binary_arith) a432)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv ()
                          (fun a433  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvShr sz))
                               a433)
                          (fun a434  -> (Obj.magic binary_arith) a434)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv ()
                          (fun a435  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvUdiv sz))
                               a435)
                          (fun a436  -> (Obj.magic binary_arith) a436)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv ()
                          (fun a437  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMod sz))
                               a437)
                          (fun a438  -> (Obj.magic binary_arith) a438)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv ()
                          (fun a439  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkBvMul sz))
                               a439)
                          (fun a440  -> (Obj.magic binary_arith) a440)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv ()
                          (fun a441  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvUlt) a441)
                          (fun a442  -> (Obj.magic binary) a442)
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____5225 =
                          let uu____5228 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____5228  in
                        let uu____5230 =
                          let uu____5233 =
                            let uu____5234 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____5234  in
                          FStar_SMTEncoding_Term.boxBitVec uu____5233  in
                        mk_bv () (fun a443  -> (Obj.magic uu____5225) a443)
                          (fun a444  -> (Obj.magic unary) a444) uu____5230
                          arg_tms2
                         in
                      let to_int1 =
                        mk_bv ()
                          (fun a445  ->
                             (Obj.magic FStar_SMTEncoding_Util.mkBvToNat)
                               a445) (fun a446  -> (Obj.magic unary) a446)
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv ()
                          (fun a447  ->
                             (Obj.magic (FStar_SMTEncoding_Util.mkNatToBv sz))
                               a447)
                          (fun a448  -> (Obj.magic unary_arith) a448)
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_add_lid, bv_add);
                        (FStar_Parser_Const.bv_sub_lid, bv_sub);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int1);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)]  in
                      let uu____5433 =
                        let uu____5442 =
                          FStar_List.tryFind
                            (fun uu____5464  ->
                               match uu____5464 with
                               | (l,uu____5474) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____5442 FStar_Util.must  in
                      (match uu____5433 with
                       | (uu____5515,op) ->
                           let uu____5525 = op arg_tms1  in
                           (uu____5525, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____5536 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____5536
       then
         let uu____5537 = FStar_Syntax_Print.tag_of_term t  in
         let uu____5538 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____5539 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5537 uu____5538
           uu____5539
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5545 ->
           let uu____5570 =
             let uu____5571 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____5572 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____5573 = FStar_Syntax_Print.term_to_string t0  in
             let uu____5574 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5571
               uu____5572 uu____5573 uu____5574
              in
           failwith uu____5570
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5579 =
             let uu____5580 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____5581 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____5582 = FStar_Syntax_Print.term_to_string t0  in
             let uu____5583 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5580
               uu____5581 uu____5582 uu____5583
              in
           failwith uu____5579
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____5589 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____5589 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____5591 =
             let uu____5592 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____5592
              in
           failwith uu____5591
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____5599),uu____5600) ->
           let uu____5649 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____5657 -> false  in
           if uu____5649
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = uu____5673;
              FStar_Syntax_Syntax.pos = uu____5674;
              FStar_Syntax_Syntax.vars = uu____5675;_},FStar_Syntax_Syntax.Meta_quoted
            (qt,uu____5677))
           ->
           let tv =
             let uu____5691 = FStar_Reflection_Basic.inspect qt  in
             FStar_Reflection_Embeddings.embed_term_view
               t.FStar_Syntax_Syntax.pos uu____5691
              in
           let t1 =
             let uu____5695 =
               let uu____5704 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____5704]  in
             FStar_Syntax_Util.mk_app FStar_Reflection_Data.fstar_refl_pack
               uu____5695
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5706) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5716 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____5716, [])
       | FStar_Syntax_Syntax.Tm_type uu____5719 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5723) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____5748 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5748 with
            | (binders1,res) ->
                let uu____5759 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5759
                then
                  let uu____5764 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5764 with
                   | (vars,guards,env',decls,uu____5789) ->
                       let fsym =
                         let uu____5807 = varops.fresh "f"  in
                         (uu____5807, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5810 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___111_5819 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___111_5819.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___111_5819.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___111_5819.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___111_5819.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___111_5819.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___111_5819.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___111_5819.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___111_5819.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___111_5819.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___111_5819.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___111_5819.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___111_5819.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___111_5819.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___111_5819.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___111_5819.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___111_5819.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___111_5819.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___111_5819.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___111_5819.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___111_5819.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___111_5819.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___111_5819.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___111_5819.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___111_5819.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___111_5819.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___111_5819.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___111_5819.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___111_5819.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___111_5819.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.splice =
                                (uu___111_5819.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___111_5819.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___111_5819.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___111_5819.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___111_5819.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___111_5819.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____5810 with
                        | (pre_opt,res_t) ->
                            let uu____5830 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____5830 with
                             | (res_pred,decls') ->
                                 let uu____5841 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5854 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____5854, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5858 =
                                         encode_formula pre env'  in
                                       (match uu____5858 with
                                        | (guard,decls0) ->
                                            let uu____5871 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____5871, decls0))
                                    in
                                 (match uu____5841 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____5883 =
                                          let uu____5894 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____5894)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5883
                                         in
                                      let cvars =
                                        let uu____5912 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____5912
                                          (FStar_List.filter
                                             (fun uu____5926  ->
                                                match uu____5926 with
                                                | (x,uu____5932) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____5951 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____5951 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5959 =
                                             let uu____5960 =
                                               let uu____5967 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5967)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5960
                                              in
                                           (uu____5959,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____5987 =
                                               let uu____5988 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____5988
                                                in
                                             varops.mk_unique uu____5987  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____5999 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____5999
                                             then
                                               let uu____6002 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6002
                                             else
                                               FStar_Pervasives_Native.None
                                              in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____6010 =
                                               let uu____6017 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6017)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6010
                                              in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type
                                              in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym
                                                in
                                             let uu____6029 =
                                               let uu____6036 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6036,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6029
                                              in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1
                                              in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1
                                              in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym
                                                in
                                             let uu____6057 =
                                               let uu____6064 =
                                                 let uu____6065 =
                                                   let uu____6076 =
                                                     let uu____6077 =
                                                       let uu____6082 =
                                                         let uu____6083 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6083
                                                          in
                                                       (f_has_t, uu____6082)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6077
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6076)
                                                    in
                                                 mkForall_fuel uu____6065  in
                                               (uu____6064,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6057
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6106 =
                                               let uu____6113 =
                                                 let uu____6114 =
                                                   let uu____6125 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6125)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6114
                                                  in
                                               (uu____6113,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6106
                                              in
                                           let t_decls1 =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1]))
                                              in
                                           ((let uu____6150 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6150);
                                            (t1, t_decls1)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow"  in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym  in
                     let uu____6165 =
                       let uu____6172 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6172,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6165  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6184 =
                       let uu____6191 =
                         let uu____6192 =
                           let uu____6203 =
                             let uu____6204 =
                               let uu____6209 =
                                 let uu____6210 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6210
                                  in
                               (f_has_t, uu____6209)  in
                             FStar_SMTEncoding_Util.mkImp uu____6204  in
                           ([[f_has_t]], [fsym], uu____6203)  in
                         mkForall_fuel uu____6192  in
                       (uu____6191, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6184  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6237 ->
           let uu____6244 =
             let uu____6249 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____6249 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6256;
                 FStar_Syntax_Syntax.vars = uu____6257;_} ->
                 let uu____6268 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____6268 with
                  | (b,f1) ->
                      let uu____6293 =
                        let uu____6294 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____6294  in
                      (uu____6293, f1))
             | uu____6303 -> failwith "impossible"  in
           (match uu____6244 with
            | (x,f) ->
                let uu____6314 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____6314 with
                 | (base_t,decls) ->
                     let uu____6325 = gen_term_var env x  in
                     (match uu____6325 with
                      | (x1,xtm,env') ->
                          let uu____6339 = encode_formula f env'  in
                          (match uu____6339 with
                           | (refinement,decls') ->
                               let uu____6350 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____6350 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____6366 =
                                        let uu____6369 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6376 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____6369
                                          uu____6376
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6366
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6409  ->
                                              match uu____6409 with
                                              | (y,uu____6415) ->
                                                  (y <> x1) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort)
                                       in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____6448 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____6448 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6456 =
                                           let uu____6457 =
                                             let uu____6464 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6464)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6457
                                            in
                                         (uu____6456,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____6485 =
                                             let uu____6486 =
                                               let uu____6487 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6487
                                                in
                                             Prims.strcat module_name
                                               uu____6486
                                              in
                                           varops.mk_unique uu____6485  in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                            in
                                         let t1 =
                                           let uu____6501 =
                                             let uu____6508 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____6508)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6501
                                            in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1
                                            in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type
                                            in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t
                                            in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1
                                            in
                                         let t_haseq1 =
                                           let uu____6523 =
                                             let uu____6530 =
                                               let uu____6531 =
                                                 let uu____6542 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6542)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6531
                                                in
                                             (uu____6530,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6523
                                            in
                                         let t_kinding =
                                           let uu____6560 =
                                             let uu____6567 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____6567,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6560
                                            in
                                         let t_interp =
                                           let uu____6585 =
                                             let uu____6592 =
                                               let uu____6593 =
                                                 let uu____6604 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6604)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6593
                                                in
                                             let uu____6627 =
                                               let uu____6630 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6630
                                                in
                                             (uu____6592, uu____6627,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6585
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____6637 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____6637);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____6667 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6667  in
           let uu____6668 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____6668 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6680 =
                    let uu____6687 =
                      let uu____6688 =
                        let uu____6689 =
                          let uu____6690 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____6690
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____6689  in
                      varops.mk_unique uu____6688  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6687)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6680  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____6695 ->
           let uu____6710 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6710 with
            | (head1,args_e) ->
                let uu____6751 =
                  let uu____6764 =
                    let uu____6765 = FStar_Syntax_Subst.compress head1  in
                    uu____6765.FStar_Syntax_Syntax.n  in
                  (uu____6764, args_e)  in
                (match uu____6751 with
                 | uu____6780 when head_redex env head1 ->
                     let uu____6793 = whnf env t  in
                     encode_term uu____6793 env
                 | uu____6794 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6813 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6827;
                       FStar_Syntax_Syntax.vars = uu____6828;_},uu____6829),uu____6830::
                    (v1,uu____6832)::(v2,uu____6834)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6889 = encode_term v1 env  in
                     (match uu____6889 with
                      | (v11,decls1) ->
                          let uu____6900 = encode_term v2 env  in
                          (match uu____6900 with
                           | (v21,decls2) ->
                               let uu____6911 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____6911,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6915::(v1,uu____6917)::(v2,uu____6919)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6966 = encode_term v1 env  in
                     (match uu____6966 with
                      | (v11,decls1) ->
                          let uu____6977 = encode_term v2 env  in
                          (match uu____6977 with
                           | (v21,decls2) ->
                               let uu____6988 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____6988,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6992)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7018)::(rng,uu____7020)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7055) ->
                     let e0 =
                       let uu____7073 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7073
                        in
                     ((let uu____7081 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7081
                       then
                         let uu____7082 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7082
                       else ());
                      (let e =
                         let uu____7087 =
                           let uu____7088 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7089 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7088
                             uu____7089
                            in
                         uu____7087 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7098),(arg,uu____7100)::[]) -> encode_term arg env
                 | uu____7125 ->
                     let uu____7138 = encode_args args_e env  in
                     (match uu____7138 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7193 = encode_term head1 env  in
                            match uu____7193 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7257 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____7257 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7335  ->
                                                 fun uu____7336  ->
                                                   match (uu____7335,
                                                           uu____7336)
                                                   with
                                                   | ((bv,uu____7358),
                                                      (a,uu____7360)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____7378 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____7378
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____7383 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____7383 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____7398 =
                                                   let uu____7405 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____7414 =
                                                     let uu____7415 =
                                                       let uu____7416 =
                                                         let uu____7417 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____7417
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7416
                                                        in
                                                     varops.mk_unique
                                                       uu____7415
                                                      in
                                                   (uu____7405,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7414)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7398
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____7434 = lookup_free_var_sym env fv  in
                            match uu____7434 with
                            | (fname,fuel_args,arity) ->
                                let tm =
                                  maybe_curry_app t0.FStar_Syntax_Syntax.pos
                                    fname arity
                                    (FStar_List.append fuel_args args)
                                   in
                                (tm, decls)
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____7466;
                                   FStar_Syntax_Syntax.vars = uu____7467;_},uu____7468)
                                ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.pos = uu____7483;
                                   FStar_Syntax_Syntax.vars = uu____7484;_},uu____7485)
                                ->
                                let uu____7494 =
                                  let uu____7495 =
                                    let uu____7500 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7500
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7495
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7494
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7530 =
                                  let uu____7531 =
                                    let uu____7536 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7536
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7531
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7530
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7565,(FStar_Util.Inl t1,uu____7567),uu____7568)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7617,(FStar_Util.Inr c,uu____7619),uu____7620)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7669 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7696 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7696
                                  in
                               let uu____7697 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____7697 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7713;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7714;_},uu____7715)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____7733 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____7782 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7782 with
            | (bs1,body1,opening) ->
                let fallback uu____7805 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____7812 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____7812, [decl])  in
                let is_impure rc =
                  let uu____7819 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7819 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7829 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____7829
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____7849 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7849
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____7853 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7853)
                    else FStar_Pervasives_Native.None
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7860 =
                         let uu____7865 =
                           let uu____7866 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7866
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7865)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7860);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7868 =
                       (is_impure rc) &&
                         (let uu____7870 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____7870)
                        in
                     if uu____7868
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____7877 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7877 with
                        | (vars,guards,envbody,decls,uu____7902) ->
                            let body2 =
                              let uu____7916 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____7916
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____7918 = encode_term body2 envbody  in
                            (match uu____7918 with
                             | (body3,decls') ->
                                 let uu____7929 =
                                   let uu____7938 = codomain_eff rc  in
                                   match uu____7938 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7957 = encode_term tfun env
                                          in
                                       (match uu____7957 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7929 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7989 =
                                          let uu____8000 =
                                            let uu____8001 =
                                              let uu____8006 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8006, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8001
                                             in
                                          ([], vars, uu____8000)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____7989
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8018 =
                                              let uu____8021 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8021
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8018
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8040 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8040 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8048 =
                                             let uu____8049 =
                                               let uu____8056 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8056)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8049
                                              in
                                           (uu____8048,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8067 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8067 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8078 =
                                                    let uu____8079 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8079 = cache_size
                                                     in
                                                  if uu____8078
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'')
                                                   in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name
                                                     in
                                                  let fsym =
                                                    let uu____8095 =
                                                      let uu____8096 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8096
                                                       in
                                                    varops.mk_unique
                                                      uu____8095
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____8103 =
                                                    let uu____8110 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8110)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8103
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1
                                                         in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym
                                                         in
                                                      let uu____8128 =
                                                        let uu____8129 =
                                                          let uu____8136 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8136,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8129
                                                         in
                                                      [uu____8128]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8149 =
                                                    let uu____8156 =
                                                      let uu____8157 =
                                                        let uu____8168 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8168)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8157
                                                       in
                                                    (uu____8156,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8149
                                                   in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f])))
                                                   in
                                                ((let uu____8185 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8185);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8188,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8189;
                          FStar_Syntax_Syntax.lbunivs = uu____8190;
                          FStar_Syntax_Syntax.lbtyp = uu____8191;
                          FStar_Syntax_Syntax.lbeff = uu____8192;
                          FStar_Syntax_Syntax.lbdef = uu____8193;
                          FStar_Syntax_Syntax.lbattrs = uu____8194;
                          FStar_Syntax_Syntax.lbpos = uu____8195;_}::uu____8196),uu____8197)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8227;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8229;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____8231;
                FStar_Syntax_Syntax.lbpos = uu____8232;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8256 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)

and (encode_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____8326 =
                let uu____8331 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8331 env  in
              match uu____8326 with
              | (ee1,decls1) ->
                  let uu____8352 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8352 with
                   | (xs,e21) ->
                       let uu____8377 = FStar_List.hd xs  in
                       (match uu____8377 with
                        | (x1,uu____8391) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____8393 = encode_body e21 env'  in
                            (match uu____8393 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____8425 =
              let uu____8432 =
                let uu____8433 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8433  in
              gen_term_var env uu____8432  in
            match uu____8425 with
            | (scrsym,scr',env1) ->
                let uu____8441 = encode_term e env1  in
                (match uu____8441 with
                 | (scr,decls) ->
                     let uu____8452 =
                       let encode_branch b uu____8477 =
                         match uu____8477 with
                         | (else_case,decls1) ->
                             let uu____8496 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____8496 with
                              | (p,w,br) ->
                                  let uu____8522 = encode_pat env1 p  in
                                  (match uu____8522 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8559  ->
                                                   match uu____8559 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____8566 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8588 =
                                               encode_term w1 env2  in
                                             (match uu____8588 with
                                              | (w2,decls2) ->
                                                  let uu____8601 =
                                                    let uu____8602 =
                                                      let uu____8607 =
                                                        let uu____8608 =
                                                          let uu____8613 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8613)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8608
                                                         in
                                                      (guard, uu____8607)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8602
                                                     in
                                                  (uu____8601, decls2))
                                          in
                                       (match uu____8566 with
                                        | (guard1,decls2) ->
                                            let uu____8626 =
                                              encode_br br env2  in
                                            (match uu____8626 with
                                             | (br1,decls3) ->
                                                 let uu____8639 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8639,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____8452 with
                      | (match_tm,decls1) ->
                          let uu____8658 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____8658, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____8698 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____8698
       then
         let uu____8699 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8699
       else ());
      (let uu____8701 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8701 with
       | (vars,pat_term) ->
           let uu____8718 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8771  ->
                     fun v1  ->
                       match uu____8771 with
                       | (env1,vars1) ->
                           let uu____8823 = gen_term_var env1 v1  in
                           (match uu____8823 with
                            | (xx,uu____8845,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____8718 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8924 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8925 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8926 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8934 = encode_const c env1  in
                      (match uu____8934 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8948::uu____8949 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8952 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8975 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____8975 with
                        | (uu____8982,uu____8983::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8986 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9019  ->
                                  match uu____9019 with
                                  | (arg,uu____9027) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9033 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9033))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9060) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9091 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9114 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9158  ->
                                  match uu____9158 with
                                  | (arg,uu____9172) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9178 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9178))
                         in
                      FStar_All.pipe_right uu____9114 FStar_List.flatten
                   in
                let pat_term1 uu____9206 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and (encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    fun env  ->
      let uu____9216 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9254  ->
                fun uu____9255  ->
                  match (uu____9254, uu____9255) with
                  | ((tms,decls),(t,uu____9291)) ->
                      let uu____9312 = encode_term t env  in
                      (match uu____9312 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9216 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9369 = FStar_Syntax_Util.list_elements e  in
        match uu____9369 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____9390 =
          let uu____9405 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____9405 FStar_Syntax_Util.head_and_args  in
        match uu____9390 with
        | (head1,args) ->
            let uu____9444 =
              let uu____9457 =
                let uu____9458 = FStar_Syntax_Util.un_uinst head1  in
                uu____9458.FStar_Syntax_Syntax.n  in
              (uu____9457, args)  in
            (match uu____9444 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9472,uu____9473)::(e,uu____9475)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9510 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9546 =
            let uu____9561 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9561 FStar_Syntax_Util.head_and_args
             in
          match uu____9546 with
          | (head1,args) ->
              let uu____9602 =
                let uu____9615 =
                  let uu____9616 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9616.FStar_Syntax_Syntax.n  in
                (uu____9615, args)  in
              (match uu____9602 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9633)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9660 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9682 = smt_pat_or1 t1  in
            (match uu____9682 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9698 = list_elements1 e  in
                 FStar_All.pipe_right uu____9698
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9716 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9716
                           (FStar_List.map one_pat)))
             | uu____9727 ->
                 let uu____9732 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9732])
        | uu____9753 ->
            let uu____9756 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9756]
         in
      let uu____9777 =
        let uu____9796 =
          let uu____9797 = FStar_Syntax_Subst.compress t  in
          uu____9797.FStar_Syntax_Syntax.n  in
        match uu____9796 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9836 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9836 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9879;
                        FStar_Syntax_Syntax.effect_name = uu____9880;
                        FStar_Syntax_Syntax.result_typ = uu____9881;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9883)::(post,uu____9885)::(pats,uu____9887)::[];
                        FStar_Syntax_Syntax.flags = uu____9888;_}
                      ->
                      let uu____9929 = lemma_pats pats  in
                      (binders1, pre, post, uu____9929)
                  | uu____9946 -> failwith "impos"))
        | uu____9965 -> failwith "Impos"  in
      match uu____9777 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___112_10013 = env  in
            {
              bindings = (uu___112_10013.bindings);
              depth = (uu___112_10013.depth);
              tcenv = (uu___112_10013.tcenv);
              warn = (uu___112_10013.warn);
              cache = (uu___112_10013.cache);
              nolabels = (uu___112_10013.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___112_10013.encode_non_total_function_typ);
              current_module_name = (uu___112_10013.current_module_name)
            }  in
          let uu____10014 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10014 with
           | (vars,guards,env2,decls,uu____10039) ->
               let uu____10052 =
                 let uu____10067 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10121 =
                             let uu____10132 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10132
                               FStar_List.unzip
                              in
                           match uu____10121 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10067 FStar_List.unzip  in
               (match uu____10052 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___113_10284 = env2  in
                      {
                        bindings = (uu___113_10284.bindings);
                        depth = (uu___113_10284.depth);
                        tcenv = (uu___113_10284.tcenv);
                        warn = (uu___113_10284.warn);
                        cache = (uu___113_10284.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___113_10284.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___113_10284.encode_non_total_function_typ);
                        current_module_name =
                          (uu___113_10284.current_module_name)
                      }  in
                    let uu____10285 =
                      let uu____10290 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10290 env3  in
                    (match uu____10285 with
                     | (pre1,decls'') ->
                         let uu____10297 =
                           let uu____10302 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____10302 env3  in
                         (match uu____10297 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10312 =
                                let uu____10313 =
                                  let uu____10324 =
                                    let uu____10325 =
                                      let uu____10330 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10330, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10325
                                     in
                                  (pats, vars, uu____10324)  in
                                FStar_SMTEncoding_Util.mkForall uu____10313
                                 in
                              (uu____10312, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____10343 = FStar_Syntax_Util.head_and_args t  in
      match uu____10343 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10402::(x,uu____10404)::(t1,uu____10406)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10453 = encode_term x env  in
               (match uu____10453 with
                | (x1,decls) ->
                    let uu____10466 = encode_term t1 env  in
                    (match uu____10466 with
                     | (t2,decls') ->
                         let uu____10479 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____10479, (FStar_List.append decls decls'))))
           | uu____10482 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10505 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10505
        then
          let uu____10506 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10507 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10506 uu____10507
        else ()  in
      let enc f r l =
        let uu____10540 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10568 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10568 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10540 with
        | (decls,args) ->
            let uu____10597 =
              let uu___114_10598 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___114_10598.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___114_10598.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10597, decls)
         in
      let const_op f r uu____10629 =
        let uu____10642 = f r  in (uu____10642, [])  in
      let un_op f l =
        let uu____10661 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10661  in
      let bin_op f uu___88_10677 =
        match uu___88_10677 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10688 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10722 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10745  ->
                 match uu____10745 with
                 | (t,uu____10759) ->
                     let uu____10760 = encode_formula t env  in
                     (match uu____10760 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10722 with
        | (decls,phis) ->
            let uu____10789 =
              let uu___115_10790 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___115_10790.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___115_10790.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10789, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10851  ->
               match uu____10851 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10870) -> false
                    | uu____10871 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10886 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10886
        else
          (let uu____10900 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10900 r rf)
         in
      let mk_imp1 r uu___89_10925 =
        match uu___89_10925 with
        | (lhs,uu____10931)::(rhs,uu____10933)::[] ->
            let uu____10960 = encode_formula rhs env  in
            (match uu____10960 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10975) ->
                      (l1, decls1)
                  | uu____10980 ->
                      let uu____10981 = encode_formula lhs env  in
                      (match uu____10981 with
                       | (l2,decls2) ->
                           let uu____10992 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10992, (FStar_List.append decls1 decls2)))))
        | uu____10995 -> failwith "impossible"  in
      let mk_ite r uu___90_11016 =
        match uu___90_11016 with
        | (guard,uu____11022)::(_then,uu____11024)::(_else,uu____11026)::[]
            ->
            let uu____11063 = encode_formula guard env  in
            (match uu____11063 with
             | (g,decls1) ->
                 let uu____11074 = encode_formula _then env  in
                 (match uu____11074 with
                  | (t,decls2) ->
                      let uu____11085 = encode_formula _else env  in
                      (match uu____11085 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11099 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11124 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11124  in
      let connectives =
        let uu____11142 =
          let uu____11155 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11155)  in
        let uu____11172 =
          let uu____11187 =
            let uu____11200 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11200)  in
          let uu____11217 =
            let uu____11232 =
              let uu____11247 =
                let uu____11260 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11260)  in
              let uu____11277 =
                let uu____11292 =
                  let uu____11307 =
                    let uu____11320 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11320)  in
                  [uu____11307;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11292  in
              uu____11247 :: uu____11277  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11232  in
          uu____11187 :: uu____11217  in
        uu____11142 :: uu____11172  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11641 = encode_formula phi' env  in
            (match uu____11641 with
             | (phi2,decls) ->
                 let uu____11652 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11652, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11653 ->
            let uu____11660 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11660 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11699 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11699 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11711;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11713;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11715;
                 FStar_Syntax_Syntax.lbpos = uu____11716;_}::[]),e2)
            ->
            let uu____11740 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11740 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11787::(x,uu____11789)::(t,uu____11791)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11838 = encode_term x env  in
                 (match uu____11838 with
                  | (x1,decls) ->
                      let uu____11849 = encode_term t env  in
                      (match uu____11849 with
                       | (t1,decls') ->
                           let uu____11860 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____11860, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11865)::(msg,uu____11867)::(phi2,uu____11869)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11914 =
                   let uu____11919 =
                     let uu____11920 = FStar_Syntax_Subst.compress r  in
                     uu____11920.FStar_Syntax_Syntax.n  in
                   let uu____11923 =
                     let uu____11924 = FStar_Syntax_Subst.compress msg  in
                     uu____11924.FStar_Syntax_Syntax.n  in
                   (uu____11919, uu____11923)  in
                 (match uu____11914 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____11933))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____11939 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____11946)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____11971 when head_redex env head2 ->
                 let uu____11984 = whnf env phi1  in
                 encode_formula uu____11984 env
             | uu____11985 ->
                 let uu____11998 = encode_term phi1 env  in
                 (match uu____11998 with
                  | (tt,decls) ->
                      let uu____12009 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___116_12012 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___116_12012.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___116_12012.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12009, decls)))
        | uu____12013 ->
            let uu____12014 = encode_term phi1 env  in
            (match uu____12014 with
             | (tt,decls) ->
                 let uu____12025 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___117_12028 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___117_12028.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___117_12028.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12025, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12064 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12064 with
        | (vars,guards,env2,decls,uu____12103) ->
            let uu____12116 =
              let uu____12129 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12181 =
                          let uu____12192 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12232  ->
                                    match uu____12232 with
                                    | (t,uu____12246) ->
                                        encode_smt_pattern t
                                          (let uu___118_12252 = env2  in
                                           {
                                             bindings =
                                               (uu___118_12252.bindings);
                                             depth = (uu___118_12252.depth);
                                             tcenv = (uu___118_12252.tcenv);
                                             warn = (uu___118_12252.warn);
                                             cache = (uu___118_12252.cache);
                                             nolabels =
                                               (uu___118_12252.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___118_12252.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___118_12252.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12192 FStar_List.unzip
                           in
                        match uu____12181 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12129 FStar_List.unzip  in
            (match uu____12116 with
             | (pats,decls') ->
                 let uu____12361 = encode_formula body env2  in
                 (match uu____12361 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12393;
                             FStar_SMTEncoding_Term.rng = uu____12394;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12409 -> guards  in
                      let uu____12414 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12414, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12474  ->
                   match uu____12474 with
                   | (x,uu____12480) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x))
            in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12488 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12500 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____12500) uu____12488 tl1
                in
             let uu____12503 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12530  ->
                       match uu____12530 with
                       | (b,uu____12536) ->
                           let uu____12537 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____12537))
                in
             (match uu____12503 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12543) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____12557 =
                    let uu____12562 =
                      let uu____12563 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12563
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12562)
                     in
                  FStar_Errors.log_issue pos uu____12557)
          in
       let uu____12564 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12564 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12573 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12631  ->
                     match uu____12631 with
                     | (l,uu____12645) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12573 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12678,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12718 = encode_q_body env vars pats body  in
             match uu____12718 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12763 =
                     let uu____12774 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12774)  in
                   FStar_SMTEncoding_Term.mkForall uu____12763
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12793 = encode_q_body env vars pats body  in
             match uu____12793 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12837 =
                   let uu____12838 =
                     let uu____12849 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____12849)  in
                   FStar_SMTEncoding_Term.mkExists uu____12838
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____12837, decls))))

type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,Prims.int,FStar_SMTEncoding_Term.decl
                                                 Prims.list)
          FStar_Pervasives_Native.tuple3
    ;
  is: FStar_Ident.lident -> Prims.bool }[@@deriving show]
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,Prims.int,FStar_SMTEncoding_Term.decl
                                                 Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
  
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
  
let (prims : prims_t) =
  let uu____12952 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____12952 with
  | (asym,a) ->
      let uu____12959 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____12959 with
       | (xsym,x) ->
           let uu____12966 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____12966 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13014 =
                      let uu____13025 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____13025, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13014  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13051 =
                      let uu____13058 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13058)  in
                    FStar_SMTEncoding_Util.mkApp uu____13051  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13071 =
                    let uu____13074 =
                      let uu____13077 =
                        let uu____13080 =
                          let uu____13081 =
                            let uu____13088 =
                              let uu____13089 =
                                let uu____13100 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13100)  in
                              FStar_SMTEncoding_Util.mkForall uu____13089  in
                            (uu____13088, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13081  in
                        let uu____13117 =
                          let uu____13120 =
                            let uu____13121 =
                              let uu____13128 =
                                let uu____13129 =
                                  let uu____13140 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13140)  in
                                FStar_SMTEncoding_Util.mkForall uu____13129
                                 in
                              (uu____13128,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13121  in
                          [uu____13120]  in
                        uu____13080 :: uu____13117  in
                      xtok_decl :: uu____13077  in
                    xname_decl :: uu____13074  in
                  (xtok1, (FStar_List.length vars), uu____13071)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____13237 =
                    let uu____13252 =
                      let uu____13263 =
                        let uu____13264 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13264
                         in
                      quant axy uu____13263  in
                    (FStar_Parser_Const.op_Eq, uu____13252)  in
                  let uu____13275 =
                    let uu____13292 =
                      let uu____13307 =
                        let uu____13318 =
                          let uu____13319 =
                            let uu____13320 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____13320  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13319
                           in
                        quant axy uu____13318  in
                      (FStar_Parser_Const.op_notEq, uu____13307)  in
                    let uu____13331 =
                      let uu____13348 =
                        let uu____13363 =
                          let uu____13374 =
                            let uu____13375 =
                              let uu____13376 =
                                let uu____13381 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____13382 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____13381, uu____13382)  in
                              FStar_SMTEncoding_Util.mkLT uu____13376  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13375
                             in
                          quant xy uu____13374  in
                        (FStar_Parser_Const.op_LT, uu____13363)  in
                      let uu____13393 =
                        let uu____13410 =
                          let uu____13425 =
                            let uu____13436 =
                              let uu____13437 =
                                let uu____13438 =
                                  let uu____13443 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____13444 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____13443, uu____13444)  in
                                FStar_SMTEncoding_Util.mkLTE uu____13438  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13437
                               in
                            quant xy uu____13436  in
                          (FStar_Parser_Const.op_LTE, uu____13425)  in
                        let uu____13455 =
                          let uu____13472 =
                            let uu____13487 =
                              let uu____13498 =
                                let uu____13499 =
                                  let uu____13500 =
                                    let uu____13505 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____13506 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____13505, uu____13506)  in
                                  FStar_SMTEncoding_Util.mkGT uu____13500  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13499
                                 in
                              quant xy uu____13498  in
                            (FStar_Parser_Const.op_GT, uu____13487)  in
                          let uu____13517 =
                            let uu____13534 =
                              let uu____13549 =
                                let uu____13560 =
                                  let uu____13561 =
                                    let uu____13562 =
                                      let uu____13567 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____13568 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____13567, uu____13568)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____13562
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13561
                                   in
                                quant xy uu____13560  in
                              (FStar_Parser_Const.op_GTE, uu____13549)  in
                            let uu____13579 =
                              let uu____13596 =
                                let uu____13611 =
                                  let uu____13622 =
                                    let uu____13623 =
                                      let uu____13624 =
                                        let uu____13629 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____13630 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____13629, uu____13630)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13624
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13623
                                     in
                                  quant xy uu____13622  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13611)
                                 in
                              let uu____13641 =
                                let uu____13658 =
                                  let uu____13673 =
                                    let uu____13684 =
                                      let uu____13685 =
                                        let uu____13686 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13686
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13685
                                       in
                                    quant qx uu____13684  in
                                  (FStar_Parser_Const.op_Minus, uu____13673)
                                   in
                                let uu____13697 =
                                  let uu____13714 =
                                    let uu____13729 =
                                      let uu____13740 =
                                        let uu____13741 =
                                          let uu____13742 =
                                            let uu____13747 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____13748 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____13747, uu____13748)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13742
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13741
                                         in
                                      quant xy uu____13740  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13729)
                                     in
                                  let uu____13759 =
                                    let uu____13776 =
                                      let uu____13791 =
                                        let uu____13802 =
                                          let uu____13803 =
                                            let uu____13804 =
                                              let uu____13809 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____13810 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____13809, uu____13810)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13804
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13803
                                           in
                                        quant xy uu____13802  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13791)
                                       in
                                    let uu____13821 =
                                      let uu____13838 =
                                        let uu____13853 =
                                          let uu____13864 =
                                            let uu____13865 =
                                              let uu____13866 =
                                                let uu____13871 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____13872 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____13871, uu____13872)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13866
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13865
                                             in
                                          quant xy uu____13864  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13853)
                                         in
                                      let uu____13883 =
                                        let uu____13900 =
                                          let uu____13915 =
                                            let uu____13926 =
                                              let uu____13927 =
                                                let uu____13928 =
                                                  let uu____13933 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____13934 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____13933, uu____13934)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13928
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13927
                                               in
                                            quant xy uu____13926  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13915)
                                           in
                                        let uu____13945 =
                                          let uu____13962 =
                                            let uu____13977 =
                                              let uu____13988 =
                                                let uu____13989 =
                                                  let uu____13990 =
                                                    let uu____13995 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____13996 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____13995,
                                                      uu____13996)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13990
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13989
                                                 in
                                              quant xy uu____13988  in
                                            (FStar_Parser_Const.op_And,
                                              uu____13977)
                                             in
                                          let uu____14007 =
                                            let uu____14024 =
                                              let uu____14039 =
                                                let uu____14050 =
                                                  let uu____14051 =
                                                    let uu____14052 =
                                                      let uu____14057 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14058 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14057,
                                                        uu____14058)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14052
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14051
                                                   in
                                                quant xy uu____14050  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14039)
                                               in
                                            let uu____14069 =
                                              let uu____14086 =
                                                let uu____14101 =
                                                  let uu____14112 =
                                                    let uu____14113 =
                                                      let uu____14114 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14114
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14113
                                                     in
                                                  quant qx uu____14112  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14101)
                                                 in
                                              [uu____14086]  in
                                            uu____14024 :: uu____14069  in
                                          uu____13962 :: uu____14007  in
                                        uu____13900 :: uu____13945  in
                                      uu____13838 :: uu____13883  in
                                    uu____13776 :: uu____13821  in
                                  uu____13714 :: uu____13759  in
                                uu____13658 :: uu____13697  in
                              uu____13596 :: uu____13641  in
                            uu____13534 :: uu____13579  in
                          uu____13472 :: uu____13517  in
                        uu____13410 :: uu____13455  in
                      uu____13348 :: uu____13393  in
                    uu____13292 :: uu____13331  in
                  uu____13237 :: uu____13275  in
                let mk1 l v1 =
                  let uu____14364 =
                    let uu____14375 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14441  ->
                              match uu____14441 with
                              | (l',uu____14457) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____14375
                      (FStar_Option.map
                         (fun uu____14529  ->
                            match uu____14529 with | (uu____14552,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____14364 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14637  ->
                          match uu____14637 with
                          | (l',uu____14653) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____14695 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____14695 with
        | (xxsym,xx) ->
            let uu____14702 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____14702 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____14712 =
                   let uu____14719 =
                     let uu____14720 =
                       let uu____14731 =
                         let uu____14732 =
                           let uu____14737 =
                             let uu____14738 =
                               let uu____14743 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____14743)  in
                             FStar_SMTEncoding_Util.mkEq uu____14738  in
                           (xx_has_type, uu____14737)  in
                         FStar_SMTEncoding_Util.mkImp uu____14732  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14731)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____14720  in
                   let uu____14768 =
                     let uu____14769 =
                       let uu____14770 =
                         let uu____14771 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____14771  in
                       Prims.strcat module_name uu____14770  in
                     varops.mk_unique uu____14769  in
                   (uu____14719, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14768)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____14712)
  
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____14807 =
      let uu____14808 =
        let uu____14815 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____14815, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14808  in
    let uu____14818 =
      let uu____14821 =
        let uu____14822 =
          let uu____14829 =
            let uu____14830 =
              let uu____14841 =
                let uu____14842 =
                  let uu____14847 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____14847)  in
                FStar_SMTEncoding_Util.mkImp uu____14842  in
              ([[typing_pred]], [xx], uu____14841)  in
            mkForall_fuel uu____14830  in
          (uu____14829, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14822  in
      [uu____14821]  in
    uu____14807 :: uu____14818  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____14889 =
      let uu____14890 =
        let uu____14897 =
          let uu____14898 =
            let uu____14909 =
              let uu____14914 =
                let uu____14917 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____14917]  in
              [uu____14914]  in
            let uu____14922 =
              let uu____14923 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____14923 tt  in
            (uu____14909, [bb], uu____14922)  in
          FStar_SMTEncoding_Util.mkForall uu____14898  in
        (uu____14897, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14890  in
    let uu____14944 =
      let uu____14947 =
        let uu____14948 =
          let uu____14955 =
            let uu____14956 =
              let uu____14967 =
                let uu____14968 =
                  let uu____14973 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____14973)  in
                FStar_SMTEncoding_Util.mkImp uu____14968  in
              ([[typing_pred]], [xx], uu____14967)  in
            mkForall_fuel uu____14956  in
          (uu____14955, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14948  in
      [uu____14947]  in
    uu____14889 :: uu____14944  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____15023 =
        let uu____15024 =
          let uu____15031 =
            let uu____15034 =
              let uu____15037 =
                let uu____15040 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____15041 =
                  let uu____15044 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____15044]  in
                uu____15040 :: uu____15041  in
              tt :: uu____15037  in
            tt :: uu____15034  in
          ("Prims.Precedes", uu____15031)  in
        FStar_SMTEncoding_Util.mkApp uu____15024  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15023  in
    let precedes_y_x =
      let uu____15048 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15048  in
    let uu____15051 =
      let uu____15052 =
        let uu____15059 =
          let uu____15060 =
            let uu____15071 =
              let uu____15076 =
                let uu____15079 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____15079]  in
              [uu____15076]  in
            let uu____15084 =
              let uu____15085 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15085 tt  in
            (uu____15071, [bb], uu____15084)  in
          FStar_SMTEncoding_Util.mkForall uu____15060  in
        (uu____15059, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15052  in
    let uu____15106 =
      let uu____15109 =
        let uu____15110 =
          let uu____15117 =
            let uu____15118 =
              let uu____15129 =
                let uu____15130 =
                  let uu____15135 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____15135)  in
                FStar_SMTEncoding_Util.mkImp uu____15130  in
              ([[typing_pred]], [xx], uu____15129)  in
            mkForall_fuel uu____15118  in
          (uu____15117, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15110  in
      let uu____15160 =
        let uu____15163 =
          let uu____15164 =
            let uu____15171 =
              let uu____15172 =
                let uu____15183 =
                  let uu____15184 =
                    let uu____15189 =
                      let uu____15190 =
                        let uu____15193 =
                          let uu____15196 =
                            let uu____15199 =
                              let uu____15200 =
                                let uu____15205 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____15206 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____15205, uu____15206)  in
                              FStar_SMTEncoding_Util.mkGT uu____15200  in
                            let uu____15207 =
                              let uu____15210 =
                                let uu____15211 =
                                  let uu____15216 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____15217 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____15216, uu____15217)  in
                                FStar_SMTEncoding_Util.mkGTE uu____15211  in
                              let uu____15218 =
                                let uu____15221 =
                                  let uu____15222 =
                                    let uu____15227 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____15228 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____15227, uu____15228)  in
                                  FStar_SMTEncoding_Util.mkLT uu____15222  in
                                [uu____15221]  in
                              uu____15210 :: uu____15218  in
                            uu____15199 :: uu____15207  in
                          typing_pred_y :: uu____15196  in
                        typing_pred :: uu____15193  in
                      FStar_SMTEncoding_Util.mk_and_l uu____15190  in
                    (uu____15189, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____15184  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15183)
                 in
              mkForall_fuel uu____15172  in
            (uu____15171,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____15164  in
        [uu____15163]  in
      uu____15109 :: uu____15160  in
    uu____15051 :: uu____15106  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15274 =
      let uu____15275 =
        let uu____15282 =
          let uu____15283 =
            let uu____15294 =
              let uu____15299 =
                let uu____15302 = FStar_SMTEncoding_Term.boxString b  in
                [uu____15302]  in
              [uu____15299]  in
            let uu____15307 =
              let uu____15308 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15308 tt  in
            (uu____15294, [bb], uu____15307)  in
          FStar_SMTEncoding_Util.mkForall uu____15283  in
        (uu____15282, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15275  in
    let uu____15329 =
      let uu____15332 =
        let uu____15333 =
          let uu____15340 =
            let uu____15341 =
              let uu____15352 =
                let uu____15353 =
                  let uu____15358 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____15358)  in
                FStar_SMTEncoding_Util.mkImp uu____15353  in
              ([[typing_pred]], [xx], uu____15352)  in
            mkForall_fuel uu____15341  in
          (uu____15340, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15333  in
      [uu____15332]  in
    uu____15274 :: uu____15329  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____15411 =
      let uu____15412 =
        let uu____15419 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____15419, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15412  in
    [uu____15411]  in
  let mk_and_interp env conj uu____15431 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15456 =
      let uu____15457 =
        let uu____15464 =
          let uu____15465 =
            let uu____15476 =
              let uu____15477 =
                let uu____15482 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____15482, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15477  in
            ([[l_and_a_b]], [aa; bb], uu____15476)  in
          FStar_SMTEncoding_Util.mkForall uu____15465  in
        (uu____15464, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15457  in
    [uu____15456]  in
  let mk_or_interp env disj uu____15520 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15545 =
      let uu____15546 =
        let uu____15553 =
          let uu____15554 =
            let uu____15565 =
              let uu____15566 =
                let uu____15571 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____15571, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15566  in
            ([[l_or_a_b]], [aa; bb], uu____15565)  in
          FStar_SMTEncoding_Util.mkForall uu____15554  in
        (uu____15553, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15546  in
    [uu____15545]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____15634 =
      let uu____15635 =
        let uu____15642 =
          let uu____15643 =
            let uu____15654 =
              let uu____15655 =
                let uu____15660 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15660, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15655  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15654)  in
          FStar_SMTEncoding_Util.mkForall uu____15643  in
        (uu____15642, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15635  in
    [uu____15634]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____15733 =
      let uu____15734 =
        let uu____15741 =
          let uu____15742 =
            let uu____15753 =
              let uu____15754 =
                let uu____15759 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15759, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15754  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15753)  in
          FStar_SMTEncoding_Util.mkForall uu____15742  in
        (uu____15741, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15734  in
    [uu____15733]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15830 =
      let uu____15831 =
        let uu____15838 =
          let uu____15839 =
            let uu____15850 =
              let uu____15851 =
                let uu____15856 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____15856, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15851  in
            ([[l_imp_a_b]], [aa; bb], uu____15850)  in
          FStar_SMTEncoding_Util.mkForall uu____15839  in
        (uu____15838, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15831  in
    [uu____15830]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15919 =
      let uu____15920 =
        let uu____15927 =
          let uu____15928 =
            let uu____15939 =
              let uu____15940 =
                let uu____15945 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____15945, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15940  in
            ([[l_iff_a_b]], [aa; bb], uu____15939)  in
          FStar_SMTEncoding_Util.mkForall uu____15928  in
        (uu____15927, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15920  in
    [uu____15919]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____15997 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15997  in
    let uu____16000 =
      let uu____16001 =
        let uu____16008 =
          let uu____16009 =
            let uu____16020 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____16020)  in
          FStar_SMTEncoding_Util.mkForall uu____16009  in
        (uu____16008, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16001  in
    [uu____16000]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b])  in
    let valid_b_x =
      let uu____16080 =
        let uu____16087 =
          let uu____16090 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16090]  in
        ("Valid", uu____16087)  in
      FStar_SMTEncoding_Util.mkApp uu____16080  in
    let uu____16093 =
      let uu____16094 =
        let uu____16101 =
          let uu____16102 =
            let uu____16113 =
              let uu____16114 =
                let uu____16119 =
                  let uu____16120 =
                    let uu____16131 =
                      let uu____16136 =
                        let uu____16139 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16139]  in
                      [uu____16136]  in
                    let uu____16144 =
                      let uu____16145 =
                        let uu____16150 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16150, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16145  in
                    (uu____16131, [xx1], uu____16144)  in
                  FStar_SMTEncoding_Util.mkForall uu____16120  in
                (uu____16119, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16114  in
            ([[l_forall_a_b]], [aa; bb], uu____16113)  in
          FStar_SMTEncoding_Util.mkForall uu____16102  in
        (uu____16101, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16094  in
    [uu____16093]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b])  in
    let valid_b_x =
      let uu____16232 =
        let uu____16239 =
          let uu____16242 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16242]  in
        ("Valid", uu____16239)  in
      FStar_SMTEncoding_Util.mkApp uu____16232  in
    let uu____16245 =
      let uu____16246 =
        let uu____16253 =
          let uu____16254 =
            let uu____16265 =
              let uu____16266 =
                let uu____16271 =
                  let uu____16272 =
                    let uu____16283 =
                      let uu____16288 =
                        let uu____16291 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16291]  in
                      [uu____16288]  in
                    let uu____16296 =
                      let uu____16297 =
                        let uu____16302 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16302, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16297  in
                    (uu____16283, [xx1], uu____16296)  in
                  FStar_SMTEncoding_Util.mkExists uu____16272  in
                (uu____16271, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16266  in
            ([[l_exists_a_b]], [aa; bb], uu____16265)  in
          FStar_SMTEncoding_Util.mkForall uu____16254  in
        (uu____16253, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16246  in
    [uu____16245]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____16362 =
      let uu____16363 =
        let uu____16370 =
          let uu____16371 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16371 range_ty  in
        let uu____16372 = varops.mk_unique "typing_range_const"  in
        (uu____16370, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16372)
         in
      FStar_SMTEncoding_Util.mkAssume uu____16363  in
    [uu____16362]  in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t])  in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t  in
      let hastypeS =
        let uu____16406 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16406 x1 t  in
      let uu____16407 =
        let uu____16418 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____16418)  in
      FStar_SMTEncoding_Util.mkForall uu____16407  in
    let uu____16441 =
      let uu____16442 =
        let uu____16449 =
          let uu____16450 =
            let uu____16461 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____16461)  in
          FStar_SMTEncoding_Util.mkForall uu____16450  in
        (uu____16449,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16442  in
    [uu____16441]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____16511 =
      let uu____16512 =
        let uu____16519 =
          let uu____16520 =
            let uu____16535 =
              let uu____16536 =
                let uu____16541 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____16542 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____16541, uu____16542)  in
              FStar_SMTEncoding_Util.mkAnd uu____16536  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16535)
             in
          FStar_SMTEncoding_Util.mkForall' uu____16520  in
        (uu____16519,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16512  in
    [uu____16511]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.forall_lid, mk_forall_interp);
    (FStar_Parser_Const.exists_lid, mk_exists_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____16888 =
            FStar_Util.find_opt
              (fun uu____16914  ->
                 match uu____16914 with
                 | (l,uu____16926) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____16888 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16951,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____16987 = encode_function_type_as_formula t env  in
        match uu____16987 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
  
let (encode_free_var :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,env_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____17027 =
                ((let uu____17030 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____17030) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____17027
              then
                let arg_sorts =
                  let uu____17040 =
                    let uu____17041 = FStar_Syntax_Subst.compress t_norm  in
                    uu____17041.FStar_Syntax_Syntax.n  in
                  match uu____17040 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17047) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____17077  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____17082 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____17084 =
                  new_term_constant_and_tok_from_lid env lid arity  in
                match uu____17084 with
                | (vname,vtok,env1) ->
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function"))
                       in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function"))
                       in
                    ([d; dd], env1)
              else
                (let uu____17117 = prims.is lid  in
                 if uu____17117
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____17125 = prims.mk lid vname  in
                   match uu____17125 with
                   | (tok,arity,definition) ->
                       let env1 =
                         push_free_var env lid arity vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17152 =
                      let uu____17163 = curried_arrow_formals_comp t_norm  in
                      match uu____17163 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17181 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____17181
                            then
                              let uu____17182 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___119_17185 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___119_17185.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___119_17185.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___119_17185.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___119_17185.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___119_17185.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___119_17185.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___119_17185.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___119_17185.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___119_17185.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___119_17185.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___119_17185.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___119_17185.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___119_17185.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___119_17185.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___119_17185.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___119_17185.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___119_17185.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___119_17185.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___119_17185.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___119_17185.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___119_17185.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___119_17185.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___119_17185.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___119_17185.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___119_17185.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___119_17185.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___119_17185.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___119_17185.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___119_17185.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___119_17185.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___119_17185.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___119_17185.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___119_17185.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___119_17185.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___119_17185.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17182
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17197 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____17197)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17152 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____17247 =
                          new_term_constant_and_tok_from_lid env lid arity
                           in
                        (match uu____17247 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17272 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___91_17314  ->
                                       match uu___91_17314 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17318 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17318 with
                                            | (uu____17339,(xxsym,uu____17341))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____17359 =
                                                  let uu____17360 =
                                                    let uu____17367 =
                                                      let uu____17368 =
                                                        let uu____17379 =
                                                          let uu____17380 =
                                                            let uu____17385 =
                                                              let uu____17386
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17386
                                                               in
                                                            (vapp,
                                                              uu____17385)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17380
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17379)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17368
                                                       in
                                                    (uu____17367,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17360
                                                   in
                                                [uu____17359])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17405 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17405 with
                                            | (uu____17426,(xxsym,uu____17428))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  }  in
                                                let tp_name =
                                                  mk_term_projector_name d f1
                                                   in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx])
                                                   in
                                                let uu____17451 =
                                                  let uu____17452 =
                                                    let uu____17459 =
                                                      let uu____17460 =
                                                        let uu____17471 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17471)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17460
                                                       in
                                                    (uu____17459,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17452
                                                   in
                                                [uu____17451])
                                       | uu____17488 -> []))
                                in
                             let uu____17489 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____17489 with
                              | (vars,guards,env',decls1,uu____17516) ->
                                  let uu____17529 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17538 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____17538, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17540 =
                                          encode_formula p env'  in
                                        (match uu____17540 with
                                         | (g,ds) ->
                                             let uu____17551 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____17551,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____17529 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____17564 =
                                           let uu____17571 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____17571)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17564
                                          in
                                       let uu____17580 =
                                         let vname_decl =
                                           let uu____17588 =
                                             let uu____17599 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17609  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____17599,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17588
                                            in
                                         let uu____17618 =
                                           let env2 =
                                             let uu___120_17624 = env1  in
                                             {
                                               bindings =
                                                 (uu___120_17624.bindings);
                                               depth = (uu___120_17624.depth);
                                               tcenv = (uu___120_17624.tcenv);
                                               warn = (uu___120_17624.warn);
                                               cache = (uu___120_17624.cache);
                                               nolabels =
                                                 (uu___120_17624.nolabels);
                                               use_zfuel_name =
                                                 (uu___120_17624.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___120_17624.current_module_name)
                                             }  in
                                           let uu____17625 =
                                             let uu____17626 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____17626
                                              in
                                           if uu____17625
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____17618 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17641::uu____17642 ->
                                                   let ff =
                                                     ("ty",
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                      in
                                                   let f =
                                                     FStar_SMTEncoding_Util.mkFreeV
                                                       ff
                                                      in
                                                   let vtok_app_l =
                                                     mk_Apply vtok_tm [ff]
                                                      in
                                                   let vtok_app_r =
                                                     mk_Apply f
                                                       [(vtok,
                                                          FStar_SMTEncoding_Term.Term_sort)]
                                                      in
                                                   let guarded_tok_typing =
                                                     let uu____17682 =
                                                       let uu____17693 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17693)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17682
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17720 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____17723 =
                                               match formals with
                                               | [] ->
                                                   let uu____17740 =
                                                     let uu____17741 =
                                                       let uu____17744 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_41  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_41)
                                                         uu____17744
                                                        in
                                                     push_free_var env1 lid
                                                       arity vname
                                                       uu____17741
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17740)
                                               | uu____17753 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____17760 =
                                                       let uu____17767 =
                                                         let uu____17768 =
                                                           let uu____17779 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17779)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17768
                                                          in
                                                       (uu____17767,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17760
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____17723 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____17580 with
                                        | (decls2,env2) ->
                                            let uu____17822 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____17830 =
                                                encode_term res_t1 env'  in
                                              match uu____17830 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17843 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____17843, decls)
                                               in
                                            (match uu____17822 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17854 =
                                                     let uu____17861 =
                                                       let uu____17862 =
                                                         let uu____17873 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____17873)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17862
                                                        in
                                                     (uu____17861,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17854
                                                    in
                                                 let freshness =
                                                   let uu____17889 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____17889
                                                   then
                                                     let uu____17894 =
                                                       let uu____17895 =
                                                         let uu____17906 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____17917 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____17906,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17917)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17895
                                                        in
                                                     let uu____17920 =
                                                       let uu____17923 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____17923]  in
                                                     uu____17894 ::
                                                       uu____17920
                                                   else []  in
                                                 let g =
                                                   let uu____17928 =
                                                     let uu____17931 =
                                                       let uu____17934 =
                                                         let uu____17937 =
                                                           let uu____17940 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____17940
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17937
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____17934
                                                        in
                                                     FStar_List.append decls2
                                                       uu____17931
                                                      in
                                                   FStar_List.append decls11
                                                     uu____17928
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (fvar_binding,FStar_SMTEncoding_Term.decl Prims.list,env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____17965 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____17965 with
          | FStar_Pervasives_Native.None  ->
              let uu____17976 = encode_free_var false env x t t_norm []  in
              (match uu____17976 with
               | (decls,env1) ->
                   let fvb =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (fvb, decls, env1))
          | FStar_Pervasives_Native.Some fvb -> (fvb, [], env)
  
let (encode_top_level_val :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm env t  in
            let uu____18029 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____18029 with
            | (decls,env1) ->
                let uu____18048 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____18048
                then
                  let uu____18055 =
                    let uu____18058 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____18058  in
                  (uu____18055, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____18110  ->
                fun lb  ->
                  match uu____18110 with
                  | (decls,env1) ->
                      let uu____18130 =
                        let uu____18137 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____18137
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____18130 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____18158 = FStar_Syntax_Util.head_and_args t  in
    match uu____18158 with
    | (hd1,args) ->
        let uu____18195 =
          let uu____18196 = FStar_Syntax_Util.un_uinst hd1  in
          uu____18196.FStar_Syntax_Syntax.n  in
        (match uu____18195 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18200,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18219 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____18241  ->
      fun quals  ->
        match uu____18241 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____18317 = FStar_Util.first_N nbinders formals  in
              match uu____18317 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18398  ->
                         fun uu____18399  ->
                           match (uu____18398, uu____18399) with
                           | ((formal,uu____18417),(binder,uu____18419)) ->
                               let uu____18428 =
                                 let uu____18435 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____18435)  in
                               FStar_Syntax_Syntax.NT uu____18428) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____18443 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18474  ->
                              match uu____18474 with
                              | (x,i) ->
                                  let uu____18485 =
                                    let uu___121_18486 = x  in
                                    let uu____18487 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___121_18486.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___121_18486.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18487
                                    }  in
                                  (uu____18485, i)))
                       in
                    FStar_All.pipe_right uu____18443
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____18505 =
                      let uu____18506 = FStar_Syntax_Subst.compress body  in
                      let uu____18507 =
                        let uu____18508 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18508
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____18506
                        uu____18507
                       in
                    uu____18505 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18569 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____18569
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___122_18572 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___122_18572.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___122_18572.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___122_18572.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___122_18572.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___122_18572.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___122_18572.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___122_18572.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___122_18572.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___122_18572.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___122_18572.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___122_18572.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___122_18572.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___122_18572.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___122_18572.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___122_18572.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___122_18572.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___122_18572.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___122_18572.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___122_18572.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___122_18572.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___122_18572.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___122_18572.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___122_18572.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___122_18572.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___122_18572.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___122_18572.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___122_18572.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___122_18572.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___122_18572.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.splice =
                         (uu___122_18572.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___122_18572.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___122_18572.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___122_18572.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___122_18572.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___122_18572.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____18605 = FStar_Syntax_Util.abs_formals e  in
                match uu____18605 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18669::uu____18670 ->
                         let uu____18685 =
                           let uu____18686 =
                             let uu____18689 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18689
                              in
                           uu____18686.FStar_Syntax_Syntax.n  in
                         (match uu____18685 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18732 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____18732 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____18774 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____18774
                                   then
                                     let uu____18809 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____18809 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18903  ->
                                                   fun uu____18904  ->
                                                     match (uu____18903,
                                                             uu____18904)
                                                     with
                                                     | ((x,uu____18922),
                                                        (b,uu____18924)) ->
                                                         let uu____18933 =
                                                           let uu____18940 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____18940)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18933)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____18942 =
                                            let uu____18963 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____18963)
                                             in
                                          (uu____18942, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19031 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____19031 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19120) ->
                              let uu____19125 =
                                let uu____19146 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____19146  in
                              (uu____19125, true)
                          | uu____19211 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.Weak;
                                  FStar_TypeChecker_Normalize.HNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____19213 ->
                              let uu____19214 =
                                let uu____19215 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____19216 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19215
                                  uu____19216
                                 in
                              failwith uu____19214)
                     | uu____19241 ->
                         let rec aux' t_norm2 =
                           let uu____19266 =
                             let uu____19267 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____19267.FStar_Syntax_Syntax.n  in
                           match uu____19266 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19308 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____19308 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____19336 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____19336 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19416)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19421 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____19477 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____19477
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19489 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19552  ->
                            fun lb  ->
                              match uu____19552 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19607 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____19607
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____19610 =
                                      let uu____19619 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____19619
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____19610 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____19489 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____19734 =
                          if fvb.smt_arity = (Prims.parse_int "0")
                          then
                            FStar_SMTEncoding_Util.mkFreeV
                              ((fvb.smt_id),
                                FStar_SMTEncoding_Term.Term_sort)
                          else
                            raise_arity_mismatch fvb.smt_id fvb.smt_arity
                              (Prims.parse_int "0") rng
                           in
                        match vars with
                        | [] -> mk_fv ()
                        | uu____19740 ->
                            if curry
                            then
                              (match fvb.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   mk_Apply ftok vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19748 = mk_fv ()  in
                                   mk_Apply uu____19748 vars)
                            else
                              (let uu____19750 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               maybe_curry_app rng
                                 (FStar_SMTEncoding_Term.Var (fvb.smt_id))
                                 fvb.smt_arity uu____19750)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19802;
                             FStar_Syntax_Syntax.lbeff = uu____19803;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____19805;
                             FStar_Syntax_Syntax.lbpos = uu____19806;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.fvar_lid  in
                            let uu____19830 =
                              let uu____19837 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____19837 with
                              | (tcenv',uu____19855,e_t) ->
                                  let uu____19861 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19872 -> failwith "Impossible"
                                     in
                                  (match uu____19861 with
                                   | (e1,t_norm1) ->
                                       ((let uu___125_19888 = env2  in
                                         {
                                           bindings =
                                             (uu___125_19888.bindings);
                                           depth = (uu___125_19888.depth);
                                           tcenv = tcenv';
                                           warn = (uu___125_19888.warn);
                                           cache = (uu___125_19888.cache);
                                           nolabels =
                                             (uu___125_19888.nolabels);
                                           use_zfuel_name =
                                             (uu___125_19888.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___125_19888.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___125_19888.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____19830 with
                             | (env',e1,t_norm1) ->
                                 let uu____19898 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____19898 with
                                  | ((binders,body,uu____19919,t_body),curry)
                                      ->
                                      ((let uu____19931 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____19931
                                        then
                                          let uu____19932 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____19933 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____19932 uu____19933
                                        else ());
                                       (let uu____19935 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____19935 with
                                        | (vars,guards,env'1,binder_decls,uu____19962)
                                            ->
                                            let body1 =
                                              let uu____19976 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____19976
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else
                                                FStar_Syntax_Util.ascribe
                                                  body
                                                  ((FStar_Util.Inl t_body),
                                                    FStar_Pervasives_Native.None)
                                               in
                                            let app =
                                              let uu____19993 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____19993 curry fvb
                                                vars
                                               in
                                            let uu____19994 =
                                              let uu____20003 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____20003
                                              then
                                                let uu____20014 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____20015 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____20014, uu____20015)
                                              else
                                                (let uu____20025 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____20025))
                                               in
                                            (match uu____19994 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20048 =
                                                     let uu____20055 =
                                                       let uu____20056 =
                                                         let uu____20067 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____20067)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20056
                                                        in
                                                     let uu____20078 =
                                                       let uu____20081 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20081
                                                        in
                                                     (uu____20055,
                                                       uu____20078,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20048
                                                    in
                                                 let uu____20084 =
                                                   let uu____20087 =
                                                     let uu____20090 =
                                                       let uu____20093 =
                                                         let uu____20096 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             fvb.smt_id app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____20096
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____20093
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20090
                                                      in
                                                   FStar_List.append decls1
                                                     uu____20087
                                                    in
                                                 (uu____20084, env2))))))
                        | uu____20101 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____20156 = varops.fresh "fuel"  in
                          (uu____20156, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____20159 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____20206  ->
                                  fun fvb  ->
                                    match uu____20206 with
                                    | (gtoks,env3) ->
                                        let flid = fvb.fvar_lid  in
                                        let g =
                                          let uu____20252 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____20252  in
                                        let gtok =
                                          let uu____20254 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____20254  in
                                        let env4 =
                                          let uu____20256 =
                                            let uu____20259 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_42  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_42) uu____20259
                                             in
                                          push_free_var env3 flid
                                            fvb.smt_arity gtok uu____20256
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____20159 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____20359 t_norm
                              uu____20361 =
                              match (uu____20359, uu____20361) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____20391;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____20392;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____20394;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____20395;_})
                                  ->
                                  let uu____20416 =
                                    let uu____20423 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____20423 with
                                    | (tcenv',uu____20445,e_t) ->
                                        let uu____20451 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20462 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____20451 with
                                         | (e1,t_norm1) ->
                                             ((let uu___126_20478 = env3  in
                                               {
                                                 bindings =
                                                   (uu___126_20478.bindings);
                                                 depth =
                                                   (uu___126_20478.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___126_20478.warn);
                                                 cache =
                                                   (uu___126_20478.cache);
                                                 nolabels =
                                                   (uu___126_20478.nolabels);
                                                 use_zfuel_name =
                                                   (uu___126_20478.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___126_20478.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___126_20478.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____20416 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20493 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____20493
                                         then
                                           let uu____20494 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____20495 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____20496 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20494 uu____20495
                                             uu____20496
                                         else ());
                                        (let uu____20498 =
                                           destruct_bound_function
                                             fvb.fvar_lid t_norm1 e1
                                            in
                                         match uu____20498 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20535 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____20535
                                               then
                                                 let uu____20536 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____20537 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____20538 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____20539 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20536 uu____20537
                                                   uu____20538 uu____20539
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20543 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____20543 with
                                               | (vars,guards,env'1,binder_decls,uu____20574)
                                                   ->
                                                   let decl_g =
                                                     let uu____20588 =
                                                       let uu____20599 =
                                                         let uu____20602 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20602
                                                          in
                                                       (g, uu____20599,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20588
                                                      in
                                                   let env02 =
                                                     push_zfuel_name env01
                                                       fvb.fvar_lid g
                                                      in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications"))
                                                      in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars
                                                      in
                                                   let app =
                                                     let uu____20627 =
                                                       let uu____20634 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.smt_id),
                                                         uu____20634)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20627
                                                      in
                                                   let gsapp =
                                                     let uu____20644 =
                                                       let uu____20651 =
                                                         let uu____20654 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____20654 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20651)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20644
                                                      in
                                                   let gmax =
                                                     let uu____20660 =
                                                       let uu____20667 =
                                                         let uu____20670 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____20670 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____20667)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20660
                                                      in
                                                   let body1 =
                                                     let uu____20676 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____20676
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____20678 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____20678 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____20696 =
                                                            let uu____20703 =
                                                              let uu____20704
                                                                =
                                                                let uu____20719
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                   in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____20719)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____20704
                                                               in
                                                            let uu____20740 =
                                                              let uu____20743
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____20743
                                                               in
                                                            (uu____20703,
                                                              uu____20740,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20696
                                                           in
                                                        let eqn_f =
                                                          let uu____20747 =
                                                            let uu____20754 =
                                                              let uu____20755
                                                                =
                                                                let uu____20766
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____20766)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20755
                                                               in
                                                            (uu____20754,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20747
                                                           in
                                                        let eqn_g' =
                                                          let uu____20780 =
                                                            let uu____20787 =
                                                              let uu____20788
                                                                =
                                                                let uu____20799
                                                                  =
                                                                  let uu____20800
                                                                    =
                                                                    let uu____20805
                                                                    =
                                                                    let uu____20806
                                                                    =
                                                                    let uu____20813
                                                                    =
                                                                    let uu____20816
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____20816
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____20813)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____20806
                                                                     in
                                                                    (gsapp,
                                                                    uu____20805)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____20800
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____20799)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20788
                                                               in
                                                            (uu____20787,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20780
                                                           in
                                                        let uu____20839 =
                                                          let uu____20848 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____20848
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____20877)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1
                                                                 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                 in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____20902
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____20902
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____20907
                                                                  =
                                                                  let uu____20914
                                                                    =
                                                                    let uu____20915
                                                                    =
                                                                    let uu____20926
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20926)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20915
                                                                     in
                                                                  (uu____20914,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____20907
                                                                 in
                                                              let uu____20947
                                                                =
                                                                let uu____20954
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____20954
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____20967
                                                                    =
                                                                    let uu____20970
                                                                    =
                                                                    let uu____20971
                                                                    =
                                                                    let uu____20978
                                                                    =
                                                                    let uu____20979
                                                                    =
                                                                    let uu____20990
                                                                    =
                                                                    let uu____20991
                                                                    =
                                                                    let uu____20996
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____20996,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____20991
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20990)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20979
                                                                     in
                                                                    (uu____20978,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____20971
                                                                     in
                                                                    [uu____20970]
                                                                     in
                                                                    (d3,
                                                                    uu____20967)
                                                                 in
                                                              (match uu____20947
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                           in
                                                        (match uu____20839
                                                         with
                                                         | (aux_decls,g_typing)
                                                             ->
                                                             ((FStar_List.append
                                                                 binder_decls
                                                                 (FStar_List.append
                                                                    decls2
                                                                    (
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                               (FStar_List.append
                                                                  [eqn_g;
                                                                  eqn_g';
                                                                  eqn_f]
                                                                  g_typing),
                                                               env02))))))))
                               in
                            let uu____21061 =
                              let uu____21074 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____21135  ->
                                   fun uu____21136  ->
                                     match (uu____21135, uu____21136) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21261 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____21261 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21074
                               in
                            (match uu____21061 with
                             | (decls2,eqns,env01) ->
                                 let uu____21334 =
                                   let isDeclFun uu___92_21346 =
                                     match uu___92_21346 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21347 -> true
                                     | uu____21358 -> false  in
                                   let uu____21359 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____21359
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____21334 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____21399 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___93_21403  ->
                                 match uu___93_21403 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21404 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21410 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21410)))
                         in
                      if uu____21399
                      then (decls1, env1)
                      else
                        (try
                           if Prims.op_Negation is_rec
                           then
                             encode_non_rec_lbdef bindings typs1 toks_fvbs
                               env1
                           else
                             encode_rec_lbdefs bindings typs1 toks_fvbs env1
                         with | Inner_let_rec  -> (decls1, env1)))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____21462 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____21462
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec (encode_sigelt :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____21511 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____21511 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____21515 = encode_sigelt' env se  in
      match uu____21515 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21531 =
                  let uu____21532 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____21532  in
                [uu____21531]
            | uu____21533 ->
                let uu____21534 =
                  let uu____21537 =
                    let uu____21538 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21538  in
                  uu____21537 :: g  in
                let uu____21539 =
                  let uu____21542 =
                    let uu____21543 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____21543  in
                  [uu____21542]  in
                FStar_List.append uu____21534 uu____21539
             in
          (g1, env1)

and (encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____21556 =
          let uu____21557 = FStar_Syntax_Subst.compress t  in
          uu____21557.FStar_Syntax_Syntax.n  in
        match uu____21556 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21561)) -> s = "opaque_to_smt"
        | uu____21562 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____21567 =
          let uu____21568 = FStar_Syntax_Subst.compress t  in
          uu____21568.FStar_Syntax_Syntax.n  in
        match uu____21567 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21572)) -> s = "uninterpreted_by_smt"
        | uu____21573 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21578 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____21583 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21588 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21591 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21594 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____21609 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21613 =
            let uu____21614 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____21614 Prims.op_Negation  in
          if uu____21613
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____21640 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____21660 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____21660 with
               | (formals,uu____21678) ->
                   let arity = FStar_List.length formals  in
                   let uu____21696 =
                     new_term_constant_and_tok_from_lid env1
                       a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____21696 with
                    | (aname,atok,env2) ->
                        let uu____21716 =
                          let uu____21721 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____21721 env2  in
                        (match uu____21716 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____21733 =
                                 let uu____21734 =
                                   let uu____21745 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____21761  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____21745,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____21734
                                  in
                               [uu____21733;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____21774 =
                               let aux uu____21826 uu____21827 =
                                 match (uu____21826, uu____21827) with
                                 | ((bv,uu____21879),(env3,acc_sorts,acc)) ->
                                     let uu____21917 = gen_term_var env3 bv
                                        in
                                     (match uu____21917 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____21774 with
                              | (uu____21989,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____22012 =
                                      let uu____22019 =
                                        let uu____22020 =
                                          let uu____22031 =
                                            let uu____22032 =
                                              let uu____22037 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____22037)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22032
                                             in
                                          ([[app]], xs_sorts, uu____22031)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22020
                                         in
                                      (uu____22019,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22012
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____22057 =
                                      let uu____22064 =
                                        let uu____22065 =
                                          let uu____22076 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____22076)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22065
                                         in
                                      (uu____22064,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22057
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____22095 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____22095 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22123,uu____22124)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22125 =
            new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4")
             in
          (match uu____22125 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22142,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____22148 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___94_22152  ->
                      match uu___94_22152 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22153 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22158 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22159 -> false))
               in
            Prims.op_Negation uu____22148  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____22168 =
               let uu____22175 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____22175 env fv t quals  in
             match uu____22168 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____22190 =
                   let uu____22193 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____22193  in
                 (uu____22190, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22201 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____22201 with
           | (uu____22210,f1) ->
               let uu____22212 = encode_formula f1 env  in
               (match uu____22212 with
                | (f2,decls) ->
                    let g =
                      let uu____22226 =
                        let uu____22227 =
                          let uu____22234 =
                            let uu____22237 =
                              let uu____22238 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____22238
                               in
                            FStar_Pervasives_Native.Some uu____22237  in
                          let uu____22239 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____22234, uu____22239)  in
                        FStar_SMTEncoding_Util.mkAssume uu____22227  in
                      [uu____22226]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22245) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____22257 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22275 =
                       let uu____22278 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____22278.FStar_Syntax_Syntax.fv_name  in
                     uu____22275.FStar_Syntax_Syntax.v  in
                   let uu____22279 =
                     let uu____22280 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____22280  in
                   if uu____22279
                   then
                     let val_decl =
                       let uu___129_22308 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___129_22308.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___129_22308.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___129_22308.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____22313 = encode_sigelt' env1 val_decl  in
                     match uu____22313 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____22257 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22341,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22343;
                          FStar_Syntax_Syntax.lbtyp = uu____22344;
                          FStar_Syntax_Syntax.lbeff = uu____22345;
                          FStar_Syntax_Syntax.lbdef = uu____22346;
                          FStar_Syntax_Syntax.lbattrs = uu____22347;
                          FStar_Syntax_Syntax.lbpos = uu____22348;_}::[]),uu____22349)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22372 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____22372 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____22401 =
                   let uu____22404 =
                     let uu____22405 =
                       let uu____22412 =
                         let uu____22413 =
                           let uu____22424 =
                             let uu____22425 =
                               let uu____22430 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____22430)  in
                             FStar_SMTEncoding_Util.mkEq uu____22425  in
                           ([[b2t_x]], [xx], uu____22424)  in
                         FStar_SMTEncoding_Util.mkForall uu____22413  in
                       (uu____22412,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____22405  in
                   [uu____22404]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22401
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22463,uu____22464) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___95_22473  ->
                  match uu___95_22473 with
                  | FStar_Syntax_Syntax.Discriminator uu____22474 -> true
                  | uu____22475 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22478,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22489 =
                     let uu____22490 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____22490.FStar_Ident.idText  in
                   uu____22489 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___96_22494  ->
                     match uu___96_22494 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22495 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22499) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___97_22516  ->
                  match uu___97_22516 with
                  | FStar_Syntax_Syntax.Projector uu____22517 -> true
                  | uu____22522 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____22525 = try_lookup_free_var env l  in
          (match uu____22525 with
           | FStar_Pervasives_Native.Some uu____22532 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___130_22536 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___130_22536.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___130_22536.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___130_22536.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22543) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22561) ->
          let uu____22570 = encode_sigelts env ses  in
          (match uu____22570 with
           | (g,env1) ->
               let uu____22587 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___98_22610  ->
                         match uu___98_22610 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22611;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22612;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22613;_}
                             -> false
                         | uu____22616 -> true))
                  in
               (match uu____22587 with
                | (g',inversions) ->
                    let uu____22631 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___99_22652  ->
                              match uu___99_22652 with
                              | FStar_SMTEncoding_Term.DeclFun uu____22653 ->
                                  true
                              | uu____22664 -> false))
                       in
                    (match uu____22631 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____22682,tps,k,uu____22685,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___100_22702  ->
                    match uu___100_22702 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____22703 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____22712 = c  in
              match uu____22712 with
              | (name,args,uu____22717,uu____22718,uu____22719) ->
                  let uu____22724 =
                    let uu____22725 =
                      let uu____22736 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____22753  ->
                                match uu____22753 with
                                | (uu____22760,sort,uu____22762) -> sort))
                         in
                      (name, uu____22736, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____22725  in
                  [uu____22724]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____22789 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____22795 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____22795 FStar_Option.isNone))
               in
            if uu____22789
            then []
            else
              (let uu____22827 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____22827 with
               | (xxsym,xx) ->
                   let uu____22836 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____22875  ->
                             fun l  ->
                               match uu____22875 with
                               | (out,decls) ->
                                   let uu____22895 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____22895 with
                                    | (uu____22906,data_t) ->
                                        let uu____22908 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____22908 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____22954 =
                                                 let uu____22955 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____22955.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____22954 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____22966,indices) ->
                                                   indices
                                               | uu____22988 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23012  ->
                                                         match uu____23012
                                                         with
                                                         | (x,uu____23018) ->
                                                             let uu____23019
                                                               =
                                                               let uu____23020
                                                                 =
                                                                 let uu____23027
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____23027,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23020
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____23019)
                                                    env)
                                                in
                                             let uu____23030 =
                                               encode_args indices env1  in
                                             (match uu____23030 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____23056 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23072
                                                                 =
                                                                 let uu____23077
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____23077,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23072)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____23056
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____23080 =
                                                      let uu____23081 =
                                                        let uu____23086 =
                                                          let uu____23087 =
                                                            let uu____23092 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____23092,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23087
                                                           in
                                                        (out, uu____23086)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23081
                                                       in
                                                    (uu____23080,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____22836 with
                    | (data_ax,decls) ->
                        let uu____23105 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____23105 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23116 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23116 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____23120 =
                                 let uu____23127 =
                                   let uu____23128 =
                                     let uu____23139 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____23154 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____23139,
                                       uu____23154)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23128
                                    in
                                 let uu____23169 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____23127,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23169)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____23120
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____23172 =
            let uu____23185 =
              let uu____23186 = FStar_Syntax_Subst.compress k  in
              uu____23186.FStar_Syntax_Syntax.n  in
            match uu____23185 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23231 -> (tps, k)  in
          (match uu____23172 with
           | (formals,res) ->
               let uu____23254 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____23254 with
                | (formals1,res1) ->
                    let uu____23265 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____23265 with
                     | (vars,guards,env',binder_decls,uu____23290) ->
                         let arity = FStar_List.length vars  in
                         let uu____23304 =
                           new_term_constant_and_tok_from_lid env t arity  in
                         (match uu____23304 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____23327 =
                                  let uu____23334 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____23334)  in
                                FStar_SMTEncoding_Util.mkApp uu____23327  in
                              let uu____23343 =
                                let tname_decl =
                                  let uu____23353 =
                                    let uu____23354 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23386  ->
                                              match uu____23386 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____23399 = varops.next_id ()  in
                                    (tname, uu____23354,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23399, false)
                                     in
                                  constructor_or_logic_type_decl uu____23353
                                   in
                                let uu____23408 =
                                  match vars with
                                  | [] ->
                                      let uu____23421 =
                                        let uu____23422 =
                                          let uu____23425 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_43  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_43) uu____23425
                                           in
                                        push_free_var env1 t arity tname
                                          uu____23422
                                         in
                                      ([], uu____23421)
                                  | uu____23436 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____23445 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23445
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____23459 =
                                          let uu____23466 =
                                            let uu____23467 =
                                              let uu____23482 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23482)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23467
                                             in
                                          (uu____23466,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23459
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____23408 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____23343 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23522 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____23522 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23540 =
                                               let uu____23541 =
                                                 let uu____23548 =
                                                   let uu____23549 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23549
                                                    in
                                                 (uu____23548,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23541
                                                in
                                             [uu____23540]
                                           else []  in
                                         let uu____23553 =
                                           let uu____23556 =
                                             let uu____23559 =
                                               let uu____23560 =
                                                 let uu____23567 =
                                                   let uu____23568 =
                                                     let uu____23579 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____23579)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23568
                                                    in
                                                 (uu____23567,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23560
                                                in
                                             [uu____23559]  in
                                           FStar_List.append karr uu____23556
                                            in
                                         FStar_List.append decls1 uu____23553
                                      in
                                   let aux =
                                     let uu____23595 =
                                       let uu____23598 =
                                         inversion_axioms tapp vars  in
                                       let uu____23601 =
                                         let uu____23604 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____23604]  in
                                       FStar_List.append uu____23598
                                         uu____23601
                                        in
                                     FStar_List.append kindingAx uu____23595
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23611,uu____23612,uu____23613,uu____23614,uu____23615)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23623,t,uu____23625,n_tps,uu____23627) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____23635 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____23635 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____23675 =
                 new_term_constant_and_tok_from_lid env d arity  in
               (match uu____23675 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____23696 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____23696 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____23710 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____23710 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____23780 =
                                            mk_term_projector_name d x  in
                                          (uu____23780,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____23782 =
                                  let uu____23801 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____23801, true)
                                   in
                                FStar_All.pipe_right uu____23782
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                 in
                              let app = mk_Apply ddtok_tm vars  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars
                                 in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars)
                                 in
                              let uu____23840 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____23840 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____23852::uu____23853 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort)
                                            in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff
                                            in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff]  in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)]
                                            in
                                         let uu____23898 =
                                           let uu____23909 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____23909)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____23898
                                     | uu____23934 -> tok_typing  in
                                   let uu____23943 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____23943 with
                                    | (vars',guards',env'',decls_formals,uu____23968)
                                        ->
                                        let uu____23981 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars'
                                             in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1)
                                             in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1
                                           in
                                        (match uu____23981 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24012 ->
                                                   let uu____24019 =
                                                     let uu____24020 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24020
                                                      in
                                                   [uu____24019]
                                                in
                                             let encode_elim uu____24030 =
                                               let uu____24031 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____24031 with
                                               | (head1,args) ->
                                                   let uu____24074 =
                                                     let uu____24075 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____24075.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____24074 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24085;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24086;_},uu____24087)
                                                        ->
                                                        let uu____24096 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____24096
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____24109
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____24109
                                                              with
                                                              | (encoded_args,arg_decls)
                                                                  ->
                                                                  let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____24152
                                                                    ->
                                                                    let uu____24153
                                                                    =
                                                                    let uu____24158
                                                                    =
                                                                    let uu____24159
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24159
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24158)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24153
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24175
                                                                    =
                                                                    let uu____24176
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24176
                                                                     in
                                                                    if
                                                                    uu____24175
                                                                    then
                                                                    let uu____24189
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24189]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____24191
                                                                    =
                                                                    let uu____24204
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24254
                                                                     ->
                                                                    fun
                                                                    uu____24255
                                                                     ->
                                                                    match 
                                                                    (uu____24254,
                                                                    uu____24255)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24350
                                                                    =
                                                                    let uu____24357
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24357
                                                                     in
                                                                    (match uu____24350
                                                                    with
                                                                    | 
                                                                    (uu____24370,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24378
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24378
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24380
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24380
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____24204
                                                                     in
                                                                  (match uu____24191
                                                                   with
                                                                   | 
                                                                   (uu____24395,arg_vars,elim_eqns_or_guards,uu____24398)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                    let ty =
                                                                    maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1
                                                                     in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____24426
                                                                    =
                                                                    let uu____24433
                                                                    =
                                                                    let uu____24434
                                                                    =
                                                                    let uu____24445
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24456
                                                                    =
                                                                    let uu____24457
                                                                    =
                                                                    let uu____24462
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24462)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24457
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24445,
                                                                    uu____24456)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24434
                                                                     in
                                                                    (uu____24433,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24426
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24485
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____24485,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____24487
                                                                    =
                                                                    let uu____24494
                                                                    =
                                                                    let uu____24495
                                                                    =
                                                                    let uu____24506
                                                                    =
                                                                    let uu____24511
                                                                    =
                                                                    let uu____24514
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____24514]
                                                                     in
                                                                    [uu____24511]
                                                                     in
                                                                    let uu____24519
                                                                    =
                                                                    let uu____24520
                                                                    =
                                                                    let uu____24525
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____24526
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____24525,
                                                                    uu____24526)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24520
                                                                     in
                                                                    (uu____24506,
                                                                    [x],
                                                                    uu____24519)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24495
                                                                     in
                                                                    let uu____24545
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____24494,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24545)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24487
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24552
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____24580
                                                                    =
                                                                    let uu____24581
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24581
                                                                    dapp1  in
                                                                    [uu____24580])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____24552
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____24588
                                                                    =
                                                                    let uu____24595
                                                                    =
                                                                    let uu____24596
                                                                    =
                                                                    let uu____24607
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24618
                                                                    =
                                                                    let uu____24619
                                                                    =
                                                                    let uu____24624
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____24624)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24619
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24607,
                                                                    uu____24618)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24596
                                                                     in
                                                                    (uu____24595,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24588)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____24644 =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____24644
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____24657
                                                               =
                                                               encode_args
                                                                 args env'
                                                                in
                                                             (match uu____24657
                                                              with
                                                              | (encoded_args,arg_decls)
                                                                  ->
                                                                  let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____24700
                                                                    ->
                                                                    let uu____24701
                                                                    =
                                                                    let uu____24706
                                                                    =
                                                                    let uu____24707
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24707
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24706)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24701
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24723
                                                                    =
                                                                    let uu____24724
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24724
                                                                     in
                                                                    if
                                                                    uu____24723
                                                                    then
                                                                    let uu____24737
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24737]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____24739
                                                                    =
                                                                    let uu____24752
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____24802
                                                                     ->
                                                                    fun
                                                                    uu____24803
                                                                     ->
                                                                    match 
                                                                    (uu____24802,
                                                                    uu____24803)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24898
                                                                    =
                                                                    let uu____24905
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24905
                                                                     in
                                                                    (match uu____24898
                                                                    with
                                                                    | 
                                                                    (uu____24918,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24926
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24926
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24928
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24928
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____24752
                                                                     in
                                                                  (match uu____24739
                                                                   with
                                                                   | 
                                                                   (uu____24943,arg_vars,elim_eqns_or_guards,uu____24946)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                    let ty =
                                                                    maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1
                                                                     in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____24974
                                                                    =
                                                                    let uu____24981
                                                                    =
                                                                    let uu____24982
                                                                    =
                                                                    let uu____24993
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25004
                                                                    =
                                                                    let uu____25005
                                                                    =
                                                                    let uu____25010
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25010)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25005
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24993,
                                                                    uu____25004)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24982
                                                                     in
                                                                    (uu____24981,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24974
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25033
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25033,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25035
                                                                    =
                                                                    let uu____25042
                                                                    =
                                                                    let uu____25043
                                                                    =
                                                                    let uu____25054
                                                                    =
                                                                    let uu____25059
                                                                    =
                                                                    let uu____25062
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25062]
                                                                     in
                                                                    [uu____25059]
                                                                     in
                                                                    let uu____25067
                                                                    =
                                                                    let uu____25068
                                                                    =
                                                                    let uu____25073
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25074
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25073,
                                                                    uu____25074)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25068
                                                                     in
                                                                    (uu____25054,
                                                                    [x],
                                                                    uu____25067)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25043
                                                                     in
                                                                    let uu____25093
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25042,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25093)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25035
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25100
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____25128
                                                                    =
                                                                    let uu____25129
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25129
                                                                    dapp1  in
                                                                    [uu____25128])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25100
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25136
                                                                    =
                                                                    let uu____25143
                                                                    =
                                                                    let uu____25144
                                                                    =
                                                                    let uu____25155
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25166
                                                                    =
                                                                    let uu____25167
                                                                    =
                                                                    let uu____25172
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25172)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25167
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25155,
                                                                    uu____25166)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25144
                                                                     in
                                                                    (uu____25143,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25136)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____25191 ->
                                                        ((let uu____25193 =
                                                            let uu____25198 =
                                                              let uu____25199
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____25200
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25199
                                                                uu____25200
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25198)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25193);
                                                         ([], [])))
                                                in
                                             let uu____25205 = encode_elim ()
                                                in
                                             (match uu____25205 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25225 =
                                                      let uu____25228 =
                                                        let uu____25231 =
                                                          let uu____25234 =
                                                            let uu____25237 =
                                                              let uu____25238
                                                                =
                                                                let uu____25249
                                                                  =
                                                                  let uu____25252
                                                                    =
                                                                    let uu____25253
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25253
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25252
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25249)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25238
                                                               in
                                                            [uu____25237]  in
                                                          let uu____25258 =
                                                            let uu____25261 =
                                                              let uu____25264
                                                                =
                                                                let uu____25267
                                                                  =
                                                                  let uu____25270
                                                                    =
                                                                    let uu____25273
                                                                    =
                                                                    let uu____25276
                                                                    =
                                                                    let uu____25277
                                                                    =
                                                                    let uu____25284
                                                                    =
                                                                    let uu____25285
                                                                    =
                                                                    let uu____25296
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25296)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25285
                                                                     in
                                                                    (uu____25284,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25277
                                                                     in
                                                                    let uu____25309
                                                                    =
                                                                    let uu____25312
                                                                    =
                                                                    let uu____25313
                                                                    =
                                                                    let uu____25320
                                                                    =
                                                                    let uu____25321
                                                                    =
                                                                    let uu____25332
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____25343
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25332,
                                                                    uu____25343)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25321
                                                                     in
                                                                    (uu____25320,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25313
                                                                     in
                                                                    [uu____25312]
                                                                     in
                                                                    uu____25276
                                                                    ::
                                                                    uu____25309
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25273
                                                                     in
                                                                  FStar_List.append
                                                                    uu____25270
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25267
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25264
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25261
                                                             in
                                                          FStar_List.append
                                                            uu____25234
                                                            uu____25258
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____25231
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____25228
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25225
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and (encode_sigelts :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____25389  ->
              fun se  ->
                match uu____25389 with
                | (g,env1) ->
                    let uu____25409 = encode_sigelt env1 se  in
                    (match uu____25409 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25466 =
        match uu____25466 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25498 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____25504 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____25504
                   then
                     let uu____25505 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____25506 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____25507 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25505 uu____25506 uu____25507
                   else ());
                  (let uu____25509 = encode_term t1 env1  in
                   match uu____25509 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____25525 =
                         let uu____25532 =
                           let uu____25533 =
                             let uu____25534 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____25534
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____25533  in
                         new_term_constant_from_string env1 x uu____25532  in
                       (match uu____25525 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____25550 = FStar_Options.log_queries ()
                                 in
                              if uu____25550
                              then
                                let uu____25553 =
                                  let uu____25554 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____25555 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____25556 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25554 uu____25555 uu____25556
                                   in
                                FStar_Pervasives_Native.Some uu____25553
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25572,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____25586 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____25586 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25609,se,uu____25611) ->
                 let uu____25616 = encode_sigelt env1 se  in
                 (match uu____25616 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25633,se) ->
                 let uu____25639 = encode_sigelt env1 se  in
                 (match uu____25639 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____25656 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____25656 with | (uu____25679,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____25691 'Auu____25692 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____25691,'Auu____25692)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____25760  ->
              match uu____25760 with
              | (l,uu____25772,uu____25773) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____25819  ->
              match uu____25819 with
              | (l,uu____25833,uu____25834) ->
                  let uu____25843 =
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_SMTEncoding_Term.Echo _0_44)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____25844 =
                    let uu____25847 =
                      let uu____25848 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____25848  in
                    [uu____25847]  in
                  uu____25843 :: uu____25844))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    let uu____25873 =
      let uu____25876 =
        let uu____25877 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____25880 =
          let uu____25881 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____25881 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____25877;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____25880
        }  in
      [uu____25876]  in
    FStar_ST.op_Colon_Equals last_env uu____25873
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____25911 = FStar_ST.op_Bang last_env  in
      match uu____25911 with
      | [] -> failwith "No env; call init first!"
      | e::uu____25938 ->
          let uu___131_25941 = e  in
          let uu____25942 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___131_25941.bindings);
            depth = (uu___131_25941.depth);
            tcenv;
            warn = (uu___131_25941.warn);
            cache = (uu___131_25941.cache);
            nolabels = (uu___131_25941.nolabels);
            use_zfuel_name = (uu___131_25941.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___131_25941.encode_non_total_function_typ);
            current_module_name = uu____25942
          }
  
let (set_env : env_t -> Prims.unit) =
  fun env  ->
    let uu____25946 = FStar_ST.op_Bang last_env  in
    match uu____25946 with
    | [] -> failwith "Empty env stack"
    | uu____25972::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : Prims.unit -> Prims.unit) =
  fun uu____26001  ->
    let uu____26002 = FStar_ST.op_Bang last_env  in
    match uu____26002 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___132_26036 = hd1  in
          {
            bindings = (uu___132_26036.bindings);
            depth = (uu___132_26036.depth);
            tcenv = (uu___132_26036.tcenv);
            warn = (uu___132_26036.warn);
            cache = refs;
            nolabels = (uu___132_26036.nolabels);
            use_zfuel_name = (uu___132_26036.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_26036.encode_non_total_function_typ);
            current_module_name = (uu___132_26036.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : Prims.unit -> Prims.unit) =
  fun uu____26062  ->
    let uu____26063 = FStar_ST.op_Bang last_env  in
    match uu____26063 with
    | [] -> failwith "Popping an empty stack"
    | uu____26089::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (init : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (push : Prims.string -> Prims.unit) =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg 
let (pop : Prims.string -> Prims.unit) =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg 
let (open_fact_db_tags :
  env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list) = fun env  -> [] 
let (place_decl_in_fact_dbs :
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____26153::uu____26154,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___133_26162 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___133_26162.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___133_26162.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___133_26162.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26163 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____26178 =
        let uu____26181 =
          let uu____26182 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____26182  in
        let uu____26183 = open_fact_db_tags env  in uu____26181 ::
          uu____26183
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26178
  
let (encode_top_level_facts :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____26205 = encode_sigelt env se  in
      match uu____26205 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____26241 = FStar_Options.log_queries ()  in
        if uu____26241
        then
          let uu____26244 =
            let uu____26245 =
              let uu____26246 =
                let uu____26247 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____26247 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____26246  in
            FStar_SMTEncoding_Term.Caption uu____26245  in
          uu____26244 :: decls
        else decls  in
      (let uu____26258 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26258
       then
         let uu____26259 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26259
       else ());
      (let env =
         let uu____26262 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____26262 tcenv  in
       let uu____26263 = encode_top_level_facts env se  in
       match uu____26263 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26277 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____26277)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit) =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____26289 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26289
       then
         let uu____26290 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26290
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26325  ->
                 fun se  ->
                   match uu____26325 with
                   | (g,env2) ->
                       let uu____26345 = encode_top_level_facts env2 se  in
                       (match uu____26345 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____26368 =
         encode_signature
           (let uu___134_26377 = env  in
            {
              bindings = (uu___134_26377.bindings);
              depth = (uu___134_26377.depth);
              tcenv = (uu___134_26377.tcenv);
              warn = false;
              cache = (uu___134_26377.cache);
              nolabels = (uu___134_26377.nolabels);
              use_zfuel_name = (uu___134_26377.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_26377.encode_non_total_function_typ);
              current_module_name = (uu___134_26377.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____26368 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26394 = FStar_Options.log_queries ()  in
             if uu____26394
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___135_26402 = env1  in
               {
                 bindings = (uu___135_26402.bindings);
                 depth = (uu___135_26402.depth);
                 tcenv = (uu___135_26402.tcenv);
                 warn = true;
                 cache = (uu___135_26402.cache);
                 nolabels = (uu___135_26402.nolabels);
                 use_zfuel_name = (uu___135_26402.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___135_26402.encode_non_total_function_typ);
                 current_module_name = (uu___135_26402.current_module_name)
               });
            (let uu____26404 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____26404
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let (encode_query :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____26456 =
           let uu____26457 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____26457.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26456);
        (let env =
           let uu____26459 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____26459 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____26471 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____26506 = aux rest  in
                 (match uu____26506 with
                  | (out,rest1) ->
                      let t =
                        let uu____26536 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____26536 with
                        | FStar_Pervasives_Native.Some uu____26541 ->
                            let uu____26542 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____26542
                              x.FStar_Syntax_Syntax.sort
                        | uu____26543 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____26547 =
                        let uu____26550 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___136_26553 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_26553.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_26553.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____26550 :: out  in
                      (uu____26547, rest1))
             | uu____26558 -> ([], bindings1)  in
           let uu____26565 = aux bindings  in
           match uu____26565 with
           | (closing,bindings1) ->
               let uu____26590 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____26590, bindings1)
            in
         match uu____26471 with
         | (q1,bindings1) ->
             let uu____26613 =
               let uu____26618 =
                 FStar_List.filter
                   (fun uu___101_26623  ->
                      match uu___101_26623 with
                      | FStar_TypeChecker_Env.Binding_sig uu____26624 ->
                          false
                      | uu____26631 -> true) bindings1
                  in
               encode_env_bindings env uu____26618  in
             (match uu____26613 with
              | (env_decls,env1) ->
                  ((let uu____26649 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____26649
                    then
                      let uu____26650 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____26650
                    else ());
                   (let uu____26652 = encode_formula q1 env1  in
                    match uu____26652 with
                    | (phi,qdecls) ->
                        let uu____26673 =
                          let uu____26678 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____26678 phi
                           in
                        (match uu____26673 with
                         | (labels,phi1) ->
                             let uu____26695 = encode_labels labels  in
                             (match uu____26695 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____26732 =
                                      let uu____26739 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____26740 =
                                        varops.mk_unique "@query"  in
                                      (uu____26739,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____26740)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____26732
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  