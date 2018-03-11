open Prims
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t) =
  fun g  ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
  
let (guard_form :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.FStar_TypeChecker_Env.guard_f 
let (is_trivial : FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = [];
        FStar_TypeChecker_Env.univ_ineqs = uu____30;
        FStar_TypeChecker_Env.implicits = uu____31;_} -> true
    | uu____58 -> false
  
let (trivial_guard : FStar_TypeChecker_Env.guard_t) =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  } 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun bs  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___116_91 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___116_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___116_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___116_91.FStar_TypeChecker_Env.implicits)
          }
  
let (abstract_guard :
  FStar_Syntax_Syntax.binder ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun vset  ->
        fun t  ->
          let uu____114 = FStar_Options.defensive ()  in
          if uu____114
          then
            let s = FStar_Syntax_Free.names_full t  in
            let uu____118 =
              let uu____119 =
                let uu____120 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____120  in
              Prims.op_Negation uu____119  in
            (if uu____118
             then
               let uu____125 =
                 let uu____130 =
                   let uu____131 = FStar_Syntax_Print.term_to_string t  in
                   let uu____132 =
                     let uu____133 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____133
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____131 uu____132
                    in
                 (FStar_Errors.Warning_Defensive, uu____130)  in
               FStar_Errors.log_issue rng uu____125
             else ())
          else ()
  
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun t  ->
        let uu____149 =
          let uu____150 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____150  in
        if uu____149
        then ()
        else def_check_vars_in_set rng msg FStar_Syntax_Free.empty t
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____168 =
            let uu____169 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____169  in
          if uu____168
          then ()
          else
            (let uu____171 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv
                in
             def_check_vars_in_set rng msg uu____171 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____186 =
            let uu____187 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____187  in
          if uu____186
          then ()
          else
            (let uu____189 = FStar_TypeChecker_Env.bound_vars e  in
             def_check_closed_in rng msg uu____189 t)
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___117_199 = g  in
          let uu____200 =
            let uu____201 =
              let uu____202 =
                let uu____205 =
                  let uu____206 =
                    let uu____221 =
                      let uu____224 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____224]  in
                    (f, uu____221)  in
                  FStar_Syntax_Syntax.Tm_app uu____206  in
                FStar_Syntax_Syntax.mk uu____205  in
              uu____202 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____201
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____200;
            FStar_TypeChecker_Env.deferred =
              (uu___117_199.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___117_199.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___117_199.FStar_TypeChecker_Env.implicits)
          }
  
let (map_guard :
  FStar_TypeChecker_Env.guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___118_242 = g  in
          let uu____243 =
            let uu____244 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____244  in
          {
            FStar_TypeChecker_Env.guard_f = uu____243;
            FStar_TypeChecker_Env.deferred =
              (uu___118_242.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___118_242.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___118_242.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____248 -> failwith "impossible"
  
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
          let uu____259 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____259
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____263 =
      let uu____264 = FStar_Syntax_Util.unmeta t  in
      uu____264.FStar_Syntax_Syntax.n  in
    match uu____263 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____268 -> FStar_TypeChecker_Common.NonTrivial t
  
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
    ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____299 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____299;
          FStar_TypeChecker_Env.deferred =
            (FStar_List.append g1.FStar_TypeChecker_Env.deferred
               g2.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            ((FStar_List.append
                (FStar_Pervasives_Native.fst
                   g1.FStar_TypeChecker_Env.univ_ineqs)
                (FStar_Pervasives_Native.fst
                   g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append
                 (FStar_Pervasives_Native.snd
                    g1.FStar_TypeChecker_Env.univ_ineqs)
                 (FStar_Pervasives_Native.snd
                    g2.FStar_TypeChecker_Env.univ_ineqs)));
          FStar_TypeChecker_Env.implicits =
            (FStar_List.append g1.FStar_TypeChecker_Env.implicits
               g2.FStar_TypeChecker_Env.implicits)
        }
  
let (conj_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____366 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____366
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___119_368 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___119_368.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___119_368.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___119_368.FStar_TypeChecker_Env.implicits)
            }
  
let (close_forall :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____387 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____387
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___120_400 = g  in
            let uu____401 =
              let uu____402 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____402  in
            {
              FStar_TypeChecker_Env.guard_f = uu____401;
              FStar_TypeChecker_Env.deferred =
                (uu___120_400.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___120_400.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___120_400.FStar_TypeChecker_Env.implicits)
            }
  
let (new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Syntax_Unionfind.fresh ()  in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                FStar_Pervasives_Native.None r
               in
            (uv1, uv1)
        | uu____432 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____457 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____457  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r
               in
            let uu____465 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r
               in
            (uu____465, uv1)
  
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____512 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____552 -> false
  
let (__proj__UNIV__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env }[@@deriving show]
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__smt_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__tcenv
  
type solution =
  | Success of FStar_TypeChecker_Common.deferred 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____738 -> false
  
let (__proj__Success__item___0 :
  solution -> FStar_TypeChecker_Common.deferred) =
  fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____754 -> false
  
let (__proj__Failed__item___0 :
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT [@@deriving show]
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____777 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____781 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____785 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___86_808  ->
    match uu___86_808 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t  in
    let detail =
      let uu____814 =
        let uu____815 = FStar_Syntax_Subst.compress t  in
        uu____815.FStar_Syntax_Syntax.n  in
      match uu____814 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____844 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____845 = FStar_Syntax_Print.term_to_string t1  in
          FStar_Util.format2 "%s : %s" uu____844 uu____845
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____848;
             FStar_Syntax_Syntax.vars = uu____849;_},args)
          ->
          let uu____899 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____900 = FStar_Syntax_Print.term_to_string ty  in
          let uu____901 = FStar_Syntax_Print.args_to_string args  in
          FStar_Util.format3 "(%s : %s) %s" uu____899 uu____900 uu____901
      | uu____902 -> "--"  in
    let uu____903 = FStar_Syntax_Print.tag_of_term t  in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____903 detail
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___87_909  ->
      match uu___87_909 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____915 =
            let uu____918 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____919 =
              let uu____922 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____923 =
                let uu____926 =
                  let uu____929 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____929]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____926
                 in
              uu____922 :: uu____923  in
            uu____918 :: uu____919  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____915
      | FStar_TypeChecker_Common.CProb p ->
          let uu____935 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____936 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____937 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____935 uu____936
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____937
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___88_943  ->
      match uu___88_943 with
      | UNIV (u,t) ->
          let x =
            let uu____947 = FStar_Options.hide_uvar_nums ()  in
            if uu____947
            then "?"
            else
              (let uu____949 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____949 FStar_Util.string_of_int)
             in
          let uu____950 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____950
      | TERM ((u,uu____952),t) ->
          let x =
            let uu____959 = FStar_Options.hide_uvar_nums ()  in
            if uu____959
            then "?"
            else
              (let uu____961 = FStar_Syntax_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____961 FStar_Util.string_of_int)
             in
          let uu____962 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____962
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____973 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____973 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____985 =
      let uu____988 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____988
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____985 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____999 .
    (FStar_Syntax_Syntax.term,'Auu____999) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1016 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1034  ->
              match uu____1034 with
              | (x,uu____1040) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1016 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1046 =
      let uu____1047 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1047  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1046;
      smt_ok = true;
      tcenv = env
    }
  
let (singleton' :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.bool -> worklist)
  =
  fun env  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___121_1063 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___121_1063.wl_deferred);
          ctr = (uu___121_1063.ctr);
          defer_ok = (uu___121_1063.defer_ok);
          smt_ok;
          tcenv = (uu___121_1063.tcenv)
        }
  
let (singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist) =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard :
  'Auu____1073 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1073,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___122_1094 = empty_worklist env  in
      let uu____1095 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1095;
        wl_deferred = (uu___122_1094.wl_deferred);
        ctr = (uu___122_1094.ctr);
        defer_ok = false;
        smt_ok = (uu___122_1094.smt_ok);
        tcenv = (uu___122_1094.tcenv)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___123_1109 = wl  in
        {
          attempting = (uu___123_1109.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___123_1109.ctr);
          defer_ok = (uu___123_1109.defer_ok);
          smt_ok = (uu___123_1109.smt_ok);
          tcenv = (uu___123_1109.tcenv)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___124_1126 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___124_1126.wl_deferred);
        ctr = (uu___124_1126.ctr);
        defer_ok = (uu___124_1126.defer_ok);
        smt_ok = (uu___124_1126.smt_ok);
        tcenv = (uu___124_1126.tcenv)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1137 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1137
         then
           let uu____1138 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1138
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___89_1142  ->
    match uu___89_1142 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1146 'Auu____1147 .
    ('Auu____1146,'Auu____1147) FStar_TypeChecker_Common.problem ->
      ('Auu____1146,'Auu____1147) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___125_1164 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___125_1164.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___125_1164.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___125_1164.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___125_1164.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___125_1164.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___125_1164.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___125_1164.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1172 'Auu____1173 .
    ('Auu____1172,'Auu____1173) FStar_TypeChecker_Common.problem ->
      ('Auu____1172,'Auu____1173) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___90_1193  ->
    match uu___90_1193 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___91_1217  ->
      match uu___91_1217 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___92_1220  ->
    match uu___92_1220 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___93_1233  ->
    match uu___93_1233 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___94_1248  ->
    match uu___94_1248 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___95_1263  ->
    match uu___95_1263 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___96_1280  ->
    match uu___96_1280 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let def_scope_wf :
  'Auu____1299 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1299) FStar_Pervasives_Native.tuple2
          Prims.list -> Prims.unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1324 =
          let uu____1325 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1325  in
        if uu____1324
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1355)::bs ->
                 (def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
      | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1392 =
          let uu____1393 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1393  in
        if uu____1392
        then ()
        else
          (let uu____1395 =
             let uu____1398 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1398
              in
           def_check_closed_in (p_loc prob) msg uu____1395 phi)
  
let (def_check_prob :
  Prims.string -> FStar_TypeChecker_Common.prob -> Prims.unit) =
  fun msg  ->
    fun prob  ->
      (let uu____1424 =
         let uu____1425 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1425  in
       if uu____1424
       then ()
       else
         (let uu____1427 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1427));
      (let uu____1435 =
         FStar_All.pipe_left FStar_Pervasives_Native.fst (p_guard prob)  in
       def_check_scoped (Prims.strcat msg ".guard") prob uu____1435);
      (let uu____1441 =
         FStar_All.pipe_left FStar_Pervasives_Native.snd (p_guard prob)  in
       def_check_scoped (Prims.strcat msg ".guard_type") prob uu____1441);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1452 -> ())
  
let (mk_eq2 :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun prob  ->
    fun t1  ->
      fun t2  ->
        let uu____1467 = FStar_Syntax_Util.type_u ()  in
        match uu____1467 with
        | (t_type,u) ->
            let uu____1474 =
              let uu____1479 = p_scope prob  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____1479 t_type  in
            (match uu____1474 with
             | (tt,uu____1481) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___97_1484  ->
    match uu___97_1484 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1506 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1506 = (Prims.parse_int "1")
  
let (next_pid : Prims.unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1518  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1603 'Auu____1604 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1603 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1603 ->
              'Auu____1604 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1603,'Auu____1604)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1641 = next_pid ()  in
                let uu____1642 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1641;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1642;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let new_problem :
  'Auu____1656 'Auu____1657 .
    FStar_TypeChecker_Env.env ->
      'Auu____1656 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1656 ->
            'Auu____1657 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1656,'Auu____1657)
                    FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              fun reason  ->
                let scope = FStar_TypeChecker_Env.all_binders env  in
                let uu____1695 = next_pid ()  in
                let uu____1696 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1695;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1696;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let problem_using_guard :
  'Auu____1709 'Auu____1710 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1709 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1709 ->
            'Auu____1710 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1709,'Auu____1710) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1743 = next_pid ()  in
              let uu____1744 = p_scope orig  in
              {
                FStar_TypeChecker_Common.pid = uu____1743;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.scope = uu____1744;
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
  
let guard_on_element :
  'Auu____1750 .
    worklist ->
      ('Auu____1750,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun wl  ->
    fun problem  ->
      fun x  ->
        fun phi  ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None  ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort
                 in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1800 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1800
        then
          let uu____1801 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1802 = prob_to_string env d  in
          let uu____1803 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1801 uu____1802 uu____1803 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1809 -> failwith "impossible"  in
           let uu____1810 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1824 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1825 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1824, uu____1825)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1831 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1832 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1831, uu____1832)
              in
           match uu____1810 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> Prims.unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___98_1848  ->
            match uu___98_1848 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1860 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1862),t) ->
                (def_check_closed t.FStar_Syntax_Syntax.pos "commit" t;
                 FStar_Syntax_Util.set_uvar u t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___99_1883  ->
           match uu___99_1883 with
           | UNIV uu____1886 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1892),t) ->
               let uu____1898 = FStar_Syntax_Unionfind.equiv uv u  in
               if uu____1898
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___100_1918  ->
           match uu___100_1918 with
           | UNIV (u',t) ->
               let uu____1923 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____1923
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1927 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____1934 =
        let uu____1935 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1935
         in
      FStar_Syntax_Subst.compress uu____1934
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____1942 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1942
  
let norm_arg :
  'Auu____1946 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1946) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1946)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1967 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____1967, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1998  ->
              match uu____1998 with
              | (x,imp) ->
                  let uu____2009 =
                    let uu___126_2010 = x  in
                    let uu____2011 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___126_2010.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___126_2010.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2011
                    }  in
                  (uu____2009, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2026 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2026
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2030 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2030
        | uu____2033 -> u2  in
      let uu____2034 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2034
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                                FStar_Syntax_Syntax.term'
                                                                  FStar_Syntax_Syntax.syntax)
                                                                FStar_Pervasives_Native.tuple2
                                                                FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2)
  =
  fun should_delta  ->
    fun env  ->
      fun t1  ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Normalize.Weak;
              FStar_TypeChecker_Normalize.HNF;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
            else
              [FStar_TypeChecker_Normalize.Weak;
              FStar_TypeChecker_Normalize.HNF]
             in
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2146 = norm_refinement env t12  in
                 match uu____2146 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2163;
                     FStar_Syntax_Syntax.vars = uu____2164;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2194 =
                       let uu____2195 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2196 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2195 uu____2196
                        in
                     failwith uu____2194)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2212 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2212
          | FStar_Syntax_Syntax.Tm_uinst uu____2213 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2250 =
                   let uu____2251 = FStar_Syntax_Subst.compress t1'  in
                   uu____2251.FStar_Syntax_Syntax.n  in
                 match uu____2250 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2268 -> aux true t1'
                 | uu____2275 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2290 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2321 =
                   let uu____2322 = FStar_Syntax_Subst.compress t1'  in
                   uu____2322.FStar_Syntax_Syntax.n  in
                 match uu____2321 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2339 -> aux true t1'
                 | uu____2346 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2361 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2406 =
                   let uu____2407 = FStar_Syntax_Subst.compress t1'  in
                   uu____2407.FStar_Syntax_Syntax.n  in
                 match uu____2406 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2424 -> aux true t1'
                 | uu____2431 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2446 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2461 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2476 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2491 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2506 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2533 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2564 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2595 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2622 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2659 ->
              let uu____2666 =
                let uu____2667 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2668 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2667 uu____2668
                 in
              failwith uu____2666
          | FStar_Syntax_Syntax.Tm_ascribed uu____2683 ->
              let uu____2710 =
                let uu____2711 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2712 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2711 uu____2712
                 in
              failwith uu____2710
          | FStar_Syntax_Syntax.Tm_delayed uu____2727 ->
              let uu____2752 =
                let uu____2753 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2754 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2753 uu____2754
                 in
              failwith uu____2752
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2769 =
                let uu____2770 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2771 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2770 uu____2771
                 in
              failwith uu____2769
           in
        let uu____2786 = whnf env t1  in aux false uu____2786
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____2808 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2808 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____2831 = base_and_refinement env t  in
      FStar_All.pipe_right uu____2831 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____2865 = FStar_Syntax_Syntax.null_bv t  in
    (uu____2865, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____2871 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2871 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2892 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____2892 with
          | (t_base,refinement) ->
              (match refinement with
               | FStar_Pervasives_Native.None  -> trivial_refinement t_base
               | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                              FStar_Pervasives_Native.tuple2
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun uu____2971  ->
    match uu____2971 with
    | (t_base,refopt) ->
        let uu____2998 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____2998 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3030 =
      let uu____3033 =
        let uu____3036 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3059  ->
                  match uu____3059 with | (uu____3066,uu____3067,x) -> x))
           in
        FStar_List.append wl.attempting uu____3036  in
      FStar_List.map (wl_prob_to_string wl) uu____3033  in
    FStar_All.pipe_right uu____3030 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3080 =
          let uu____3093 =
            let uu____3094 = FStar_Syntax_Subst.compress k  in
            uu____3094.FStar_Syntax_Syntax.n  in
          match uu____3093 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3147 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3147)
              else
                (let uu____3161 = FStar_Syntax_Util.abs_formals t  in
                 match uu____3161 with
                 | (ys',t1,uu____3184) ->
                     let uu____3189 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____3189))
          | uu____3230 ->
              let uu____3231 =
                let uu____3242 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____3242)  in
              ((ys, t), uu____3231)
           in
        match uu____3080 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____3291 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____3291 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi  in
             let uu____3320 = p_guard prob  in
             match uu____3320 with
             | (uu____3325,uv) ->
                 ((let uu____3328 =
                     let uu____3329 = FStar_Syntax_Subst.compress uv  in
                     uu____3329.FStar_Syntax_Syntax.n  in
                   match uu____3328 with
                   | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                       let bs = p_scope prob  in
                       let phi1 = u_abs k bs phi  in
                       ((let uu____3361 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug wl.tcenv)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____3361
                         then
                           let uu____3362 =
                             FStar_Util.string_of_int (p_pid prob)  in
                           let uu____3363 =
                             FStar_Syntax_Print.term_to_string uv  in
                           let uu____3364 =
                             FStar_Syntax_Print.term_to_string phi1  in
                           FStar_Util.print3
                             "Solving %s (%s) with formula %s\n" uu____3362
                             uu____3363 uu____3364
                         else ());
                        def_check_closed (p_loc prob) "solve_prob'" phi1;
                        FStar_Syntax_Util.set_uvar uvar phi1)
                   | uu____3367 ->
                       if Prims.op_Negation resolve_ok
                       then
                         failwith
                           "Impossible: this instance has already been assigned a solution"
                       else ());
                  commit uvis;
                  (let uu___127_3370 = wl  in
                   {
                     attempting = (uu___127_3370.attempting);
                     wl_deferred = (uu___127_3370.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___127_3370.defer_ok);
                     smt_ok = (uu___127_3370.smt_ok);
                     tcenv = (uu___127_3370.tcenv)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3385 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____3385
         then
           let uu____3386 = FStar_Util.string_of_int pid  in
           let uu____3387 =
             let uu____3388 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____3388 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3386 uu____3387
         else ());
        commit sol;
        (let uu___128_3395 = wl  in
         {
           attempting = (uu___128_3395.attempting);
           wl_deferred = (uu___128_3395.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___128_3395.defer_ok);
           smt_ok = (uu___128_3395.smt_ok);
           tcenv = (uu___128_3395.tcenv)
         })
  
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let conj_guard1 t g =
             match (t, g) with
             | (uu____3435,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____3447 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____3447
              in
           (let uu____3453 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____3453
            then
              let uu____3454 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____3455 =
                let uu____3456 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____3456 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____3454 uu____3455
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let rec occurs :
  'b .
    worklist ->
      (FStar_Syntax_Syntax.uvar,'b) FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun wl  ->
    fun uk  ->
      fun t  ->
        let uu____3488 =
          let uu____3495 = FStar_Syntax_Free.uvars t  in
          FStar_All.pipe_right uu____3495 FStar_Util.set_elements  in
        FStar_All.pipe_right uu____3488
          (FStar_Util.for_some
             (fun uu____3531  ->
                match uu____3531 with
                | (uv,uu____3537) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
  
let occurs_check :
  'Auu____3544 'Auu____3545 .
    'Auu____3544 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3545)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.typ ->
            (Prims.bool,Prims.string FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun uk  ->
        fun t  ->
          let occurs_ok =
            let uu____3577 = occurs wl uk t  in Prims.op_Negation uu____3577
             in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3584 =
                 let uu____3585 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk)
                    in
                 let uu____3586 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3585 uu____3586
                  in
               FStar_Pervasives_Native.Some uu____3584)
             in
          (occurs_ok, msg)
  
let occurs_and_freevars_check :
  'Auu____3596 'Auu____3597 .
    'Auu____3596 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3597)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.bv FStar_Util.set ->
            FStar_Syntax_Syntax.term ->
              (Prims.bool,Prims.bool,(Prims.string
                                        FStar_Pervasives_Native.option,
                                       FStar_Syntax_Syntax.bv FStar_Util.set,
                                       FStar_Syntax_Syntax.bv FStar_Util.set)
                                       FStar_Pervasives_Native.tuple3)
                FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun wl  ->
      fun uk  ->
        fun fvs  ->
          fun t  ->
            let fvs_t = FStar_Syntax_Free.names t  in
            let uu____3651 = occurs_check env wl uk t  in
            match uu____3651 with
            | (occurs_ok,msg) ->
                let uu____3682 = FStar_Util.set_is_subset_of fvs_t fvs  in
                (occurs_ok, uu____3682, (msg, fvs, fvs_t))
  
let intersect_vars :
  'Auu____3705 'Auu____3706 .
    (FStar_Syntax_Syntax.bv,'Auu____3705) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3706) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3706) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun v1  ->
    fun v2  ->
      let as_set1 v3 =
        FStar_All.pipe_right v3
          (FStar_List.fold_left
             (fun out  ->
                fun x  ->
                  FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
             FStar_Syntax_Syntax.no_names)
         in
      let v1_set = as_set1 v1  in
      let uu____3790 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3844  ->
                fun uu____3845  ->
                  match (uu____3844, uu____3845) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3926 =
                        let uu____3927 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____3927  in
                      if uu____3926
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____3952 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____3952
                         then
                           let uu____3965 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____3965)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____3790 with | (isect,uu____4006) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____4031 'Auu____4032 .
    (FStar_Syntax_Syntax.bv,'Auu____4031) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4032) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4087  ->
              fun uu____4088  ->
                match (uu____4087, uu____4088) with
                | ((a,uu____4106),(b,uu____4108)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt :
  'Auu____4122 'Auu____4123 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4122) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4123)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4123)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg  in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4174 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4188  ->
                      match uu____4188 with
                      | (b,uu____4194) -> FStar_Syntax_Syntax.bv_eq a b))
               in
            if uu____4174
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4210 -> FStar_Pervasives_Native.None
  
let rec (pat_vars :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____4283 = pat_var_opt env seen hd1  in
            (match uu____4283 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4297 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____4297
                   then
                     let uu____4298 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4298
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4316 =
      let uu____4317 = FStar_Syntax_Subst.compress t  in
      uu____4317.FStar_Syntax_Syntax.n  in
    match uu____4316 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4320 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4337;
           FStar_Syntax_Syntax.pos = uu____4338;
           FStar_Syntax_Syntax.vars = uu____4339;_},uu____4340)
        -> true
    | uu____4381 -> false
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option
                                                             FStar_Unionfind.p_uvar,
                                                            FStar_Syntax_Syntax.version)
                                                            FStar_Pervasives_Native.tuple2,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                              FStar_Syntax_Syntax.syntax,
                                                             FStar_Syntax_Syntax.aqual)
                                                             FStar_Pervasives_Native.tuple2
                                                             Prims.list)
      FStar_Pervasives_Native.tuple4)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
           FStar_Syntax_Syntax.pos = uu____4505;
           FStar_Syntax_Syntax.vars = uu____4506;_},args)
        -> (t, uv, k, args)
    | uu____4578 -> failwith "Not a flex-uvar"
  
let (destruct_flex_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                                FStar_Syntax_Syntax.syntax
                                                                FStar_Pervasives_Native.option
                                                                FStar_Unionfind.p_uvar,
                                                               FStar_Syntax_Syntax.version)
                                                               FStar_Pervasives_Native.tuple2,
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax,
                                                                FStar_Syntax_Syntax.aqual)
                                                                FStar_Pervasives_Native.tuple2
                                                                Prims.list)
         FStar_Pervasives_Native.tuple4,FStar_Syntax_Syntax.binders
                                          FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun t  ->
      let uu____4655 = destruct_flex_t t  in
      match uu____4655 with
      | (t1,uv,k,args) ->
          let uu____4770 = pat_vars env [] args  in
          (match uu____4770 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4868 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4949 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4984 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4988 -> false
  
let string_of_option :
  'Auu____4992 .
    ('Auu____4992 -> Prims.string) ->
      'Auu____4992 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___101_5005  ->
      match uu___101_5005 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5011 = f x  in Prims.strcat "Some " uu____5011
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___102_5014  ->
    match uu___102_5014 with
    | MisMatch (d1,d2) ->
        let uu____5025 =
          let uu____5026 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5027 =
            let uu____5028 =
              let uu____5029 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5029 ")"  in
            Prims.strcat ") (" uu____5028  in
          Prims.strcat uu____5026 uu____5027  in
        Prims.strcat "MisMatch (" uu____5025
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___103_5032  ->
    match uu___103_5032 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5047 -> HeadMatch
  
let (and_match :
  match_result -> (Prims.unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5073 = m2 ()  in
          (match uu____5073 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5088 -> HeadMatch)
      | FullMatch  -> m2 ()
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      match fv.FStar_Syntax_Syntax.fv_delta with
      | FStar_Syntax_Syntax.Delta_abstract d ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d
          else FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5097 ->
          let uu____5098 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5098 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5109 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____5128 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5137 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5165 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5165
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5166 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5167 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5168 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5185 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5198 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5222) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5228,uu____5229) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5271) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5292;
             FStar_Syntax_Syntax.index = uu____5293;
             FStar_Syntax_Syntax.sort = t2;_},uu____5295)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5302 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5303 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5304 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5317 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5335 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5335
  
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____5362 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5362
            then FullMatch
            else
              (let uu____5364 =
                 let uu____5373 =
                   let uu____5376 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5376  in
                 let uu____5377 =
                   let uu____5380 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5380  in
                 (uu____5373, uu____5377)  in
               MisMatch uu____5364)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5386),FStar_Syntax_Syntax.Tm_uinst (g,uu____5388)) ->
            let uu____5397 = head_matches env f g  in
            FStar_All.pipe_right uu____5397 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5400 = FStar_Const.eq_const c d  in
            if uu____5400
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5407),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5409)) ->
            let uu____5458 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5458
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5465),FStar_Syntax_Syntax.Tm_refine (y,uu____5467)) ->
            let uu____5476 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5476 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5478),uu____5479) ->
            let uu____5484 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5484 head_match
        | (uu____5485,FStar_Syntax_Syntax.Tm_refine (x,uu____5487)) ->
            let uu____5492 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5492 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5493,FStar_Syntax_Syntax.Tm_type
           uu____5494) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5495,FStar_Syntax_Syntax.Tm_arrow uu____5496) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            if (FStar_List.length bs1) = (FStar_List.length bs2)
            then
              let uu____5625 =
                let uu____5626 = FStar_List.zip bs1 bs2  in
                let uu____5661 = head_matches env t12 t22  in
                FStar_List.fold_right
                  (fun uu____5670  ->
                     fun a  ->
                       match uu____5670 with
                       | (b1,b2) ->
                           and_match a
                             (fun uu____5679  -> branch_matches env b1 b2))
                  uu____5626 uu____5661
                 in
              FStar_All.pipe_right uu____5625 head_match
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5686),FStar_Syntax_Syntax.Tm_app (head',uu____5688))
            ->
            let uu____5729 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____5729 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5731),uu____5732) ->
            let uu____5753 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____5753 head_match
        | (uu____5754,FStar_Syntax_Syntax.Tm_app (head1,uu____5756)) ->
            let uu____5777 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____5777 head_match
        | uu____5778 ->
            let uu____5783 =
              let uu____5792 = delta_depth_of_term env t11  in
              let uu____5795 = delta_depth_of_term env t21  in
              (uu____5792, uu____5795)  in
            MisMatch uu____5783

and (branch_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch -> match_result)
  =
  fun env  ->
    fun b1  ->
      fun b2  ->
        let related_by f o1 o2 =
          match (o1, o2) with
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
              true
          | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y)
              -> f x y
          | (uu____5847,uu____5848) -> false  in
        let uu____5857 = b1  in
        match uu____5857 with
        | (p1,w1,t1) ->
            let uu____5877 = b2  in
            (match uu____5877 with
             | (p2,w2,t2) ->
                 let uu____5897 = FStar_Syntax_Syntax.eq_pat p1 p2  in
                 if uu____5897
                 then
                   let uu____5898 =
                     (let uu____5901 = FStar_Syntax_Util.eq_tm t1 t2  in
                      uu____5901 = FStar_Syntax_Util.Equal) &&
                       (related_by
                          (fun t11  ->
                             fun t21  ->
                               let uu____5910 =
                                 FStar_Syntax_Util.eq_tm t11 t21  in
                               uu____5910 = FStar_Syntax_Util.Equal) w1 w2)
                      in
                   (if uu____5898
                    then FullMatch
                    else
                      MisMatch
                        (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.None))
                 else
                   MisMatch
                     (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None))

let head_matches_delta :
  'Auu____5926 .
    FStar_TypeChecker_Env.env ->
      'Auu____5926 ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (match_result,(FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                            FStar_Pervasives_Native.tuple2
                            FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let uu____5959 = FStar_Syntax_Util.head_and_args t  in
            match uu____5959 with
            | (head1,uu____5977) ->
                let uu____5998 =
                  let uu____5999 = FStar_Syntax_Util.un_uinst head1  in
                  uu____5999.FStar_Syntax_Syntax.n  in
                (match uu____5998 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6005 =
                       let uu____6006 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6006 FStar_Option.isSome
                        in
                     if uu____6005
                     then
                       let uu____6025 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6025
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____6029 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 r = (r, FStar_Pervasives_Native.None)  in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ),uu____6132)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6150 =
                     let uu____6159 = maybe_inline t11  in
                     let uu____6162 = maybe_inline t21  in
                     (uu____6159, uu____6162)  in
                   match uu____6150 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail1 r
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.None ) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t21
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t11 t22
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (uu____6199,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6217 =
                     let uu____6226 = maybe_inline t11  in
                     let uu____6229 = maybe_inline t21  in
                     (uu____6226, uu____6229)  in
                   match uu____6217 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail1 r
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.None ) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t21
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t11 t22
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                when d1 = d2 ->
                let uu____6272 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6272 with
                 | FStar_Pervasives_Native.None  -> fail1 r
                 | FStar_Pervasives_Native.Some d ->
                     let t12 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t11
                        in
                     let t22 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21
                        in
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
                let uu____6295 =
                  if d1_greater_than_d2
                  then
                    let t1' =
                      normalize_refinement
                        [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                        FStar_TypeChecker_Normalize.Weak;
                        FStar_TypeChecker_Normalize.HNF] env wl t11
                       in
                    (t1', t21)
                  else
                    (let t2' =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21
                        in
                     (t11, t2'))
                   in
                (match uu____6295 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6319 -> fail1 r
            | uu____6328 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6341 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6341
           then
             let uu____6342 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6343 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6344 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6342
               uu____6343 uu____6344
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6384 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6420 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___104_6432  ->
    match uu___104_6432 with
    | T (t,uu____6434) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6450 = FStar_Syntax_Util.type_u ()  in
      match uu____6450 with
      | (t,uu____6456) ->
          let uu____6457 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6457
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6468 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6468 FStar_Pervasives_Native.fst
  
let rec (decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (tc Prims.list -> FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term ->
                                                   Prims.bool,(FStar_Syntax_Syntax.binder
                                                                 FStar_Pervasives_Native.option,
                                                                variance,
                                                                tc)
                                                                FStar_Pervasives_Native.tuple3
                                                                Prims.list)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____6532 = head_matches env t1 t'  in
        match uu____6532 with
        | MisMatch uu____6533 -> false
        | uu____6542 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6638,imp),T (t2,uu____6641)) -> (t2, imp)
                     | uu____6660 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6727  ->
                    match uu____6727 with
                    | (t2,uu____6741) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6784 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6784 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6859))::tcs2) ->
                       aux
                         (((let uu___129_6894 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___129_6894.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___129_6894.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6912 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___105_6965 =
                 match uu___105_6965 with
                 | [] ->
                     FStar_List.rev
                       ((FStar_Pervasives_Native.None, COVARIANT, (C c1)) ::
                       out)
                 | hd1::rest ->
                     decompose1
                       (((FStar_Pervasives_Native.Some hd1), CONTRAVARIANT,
                          (T
                             (((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____7082 = decompose1 [] bs1  in
               (rebuild, matches, uu____7082))
      | uu____7131 ->
          let rebuild uu___106_7137 =
            match uu___106_7137 with
            | [] -> t1
            | uu____7140 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___107_7171  ->
    match uu___107_7171 with
    | T (t,uu____7173) -> t
    | uu____7182 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___108_7185  ->
    match uu___108_7185 with
    | T (t,uu____7187) -> FStar_Syntax_Syntax.as_arg t
    | uu____7196 -> failwith "Impossible"
  
let (imitation_sub_probs :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,
            variance,tc) FStar_Pervasives_Native.tuple3 Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list,tc Prims.list,FStar_Syntax_Syntax.formula)
              FStar_Pervasives_Native.tuple3)
  =
  fun orig  ->
    fun env  ->
      fun scope  ->
        fun ps  ->
          fun qs  ->
            let r = p_loc orig  in
            let rel = p_rel orig  in
            let sub_prob scope1 args q =
              match q with
              | (uu____7312,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7337 = new_uvar r scope1 k  in
                  (match uu____7337 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7355 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7372 =
                         let uu____7373 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7373
                          in
                       ((T (gi_xs, mk_kind)), uu____7372))
              | (uu____7386,uu____7387,C uu____7388) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7535 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7552;
                         FStar_Syntax_Syntax.vars = uu____7553;_})
                        ->
                        let uu____7580 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7580 with
                         | (T (gi_xs,uu____7604),prob) ->
                             let uu____7614 =
                               let uu____7615 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7615
                                in
                             (uu____7614, [prob])
                         | uu____7618 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7633;
                         FStar_Syntax_Syntax.vars = uu____7634;_})
                        ->
                        let uu____7661 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7661 with
                         | (T (gi_xs,uu____7685),prob) ->
                             let uu____7695 =
                               let uu____7696 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7696
                                in
                             (uu____7695, [prob])
                         | uu____7699 -> failwith "impossible")
                    | (uu____7710,uu____7711,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7713;
                         FStar_Syntax_Syntax.vars = uu____7714;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (FStar_Pervasives_Native.None, INVARIANT,
                                    (T
                                       ((FStar_Pervasives_Native.fst t),
                                         generic_kind)))))
                           in
                        let components1 =
                          (FStar_Pervasives_Native.None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components  in
                        let uu____7849 =
                          let uu____7858 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____7858 FStar_List.unzip
                           in
                        (match uu____7849 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7912 =
                                 let uu____7913 =
                                   let uu____7916 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____7916 un_T  in
                                 let uu____7917 =
                                   let uu____7926 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____7926
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7913;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7917;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7912
                                in
                             ((C gi_xs), sub_probs))
                    | uu____7935 ->
                        let uu____7948 = sub_prob scope1 args q  in
                        (match uu____7948 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7535 with
                   | (tc,probs) ->
                       let uu____7979 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____8042,uu____8043),T
                            (t,uu____8045)) ->
                             let b1 =
                               ((let uu___130_8082 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___130_8082.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___130_8082.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____8083 =
                               let uu____8090 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____8090 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____8083)
                         | uu____8125 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____7979 with
                        | (bopt,scope2,args1) ->
                            let uu____8209 = aux scope2 args1 qs2  in
                            (match uu____8209 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8247 =
                                           let uu____8250 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8250  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8247
                                          in
                                       (def_check_closed (p_loc orig)
                                          "imitation_sub_probs (1)" f1;
                                        f1)
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let f1 =
                                         let uu____8275 =
                                           let uu____8278 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8279 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8278 :: uu____8279  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8275
                                          in
                                       (def_check_closed (p_loc orig)
                                          "imitation_sub_probs (2)" f1;
                                        f1)
                                    in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1))))
               in
            aux scope ps qs
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ,
    FStar_Syntax_Syntax.args) FStar_Pervasives_Native.tuple4[@@deriving show]
type im_or_proj_t =
  (((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
     FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.arg Prims.list,
    (tc Prims.list -> FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ ->
                                                Prims.bool,(FStar_Syntax_Syntax.binder
                                                              FStar_Pervasives_Native.option,
                                                             variance,
                                                             tc)
                                                             FStar_Pervasives_Native.tuple3
                                                             Prims.list)
      FStar_Pervasives_Native.tuple3)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let (rigid_rigid : Prims.int) = (Prims.parse_int "0") 
let (flex_rigid_eq : Prims.int) = (Prims.parse_int "1") 
let (flex_refine_inner : Prims.int) = (Prims.parse_int "2") 
let (flex_refine : Prims.int) = (Prims.parse_int "3") 
let (flex_rigid : Prims.int) = (Prims.parse_int "4") 
let (rigid_flex : Prims.int) = (Prims.parse_int "5") 
let (refine_flex : Prims.int) = (Prims.parse_int "6") 
let (flex_flex : Prims.int) = (Prims.parse_int "7") 
let compress_tprob :
  'Auu____8348 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8348)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8348)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___131_8369 = p  in
      let uu____8374 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8375 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___131_8369.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8374;
        FStar_TypeChecker_Common.relation =
          (uu___131_8369.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8375;
        FStar_TypeChecker_Common.element =
          (uu___131_8369.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___131_8369.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___131_8369.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___131_8369.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___131_8369.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___131_8369.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8387 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8387
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8396 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8416 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8416 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8426 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8426 with
           | (lh,uu____8446) ->
               let uu____8467 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8467 with
                | (rh,uu____8487) ->
                    let uu____8508 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8525,FStar_Syntax_Syntax.Tm_uvar uu____8526)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8563,uu____8564)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8585,FStar_Syntax_Syntax.Tm_uvar uu____8586)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8607,uu____8608)
                          ->
                          let uu____8625 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____8625 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8674 ->
                                    let rank =
                                      let uu____8682 = is_top_level_prob prob
                                         in
                                      if uu____8682
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____8684 =
                                      let uu___132_8689 = tp  in
                                      let uu____8694 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___132_8689.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___132_8689.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___132_8689.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8694;
                                        FStar_TypeChecker_Common.element =
                                          (uu___132_8689.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___132_8689.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___132_8689.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___132_8689.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___132_8689.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___132_8689.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____8684)))
                      | (uu____8705,FStar_Syntax_Syntax.Tm_uvar uu____8706)
                          ->
                          let uu____8723 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____8723 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8772 ->
                                    let uu____8779 =
                                      let uu___133_8786 = tp  in
                                      let uu____8791 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___133_8786.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8791;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___133_8786.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___133_8786.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___133_8786.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___133_8786.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___133_8786.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___133_8786.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___133_8786.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___133_8786.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____8779)))
                      | (uu____8808,uu____8809) -> (rigid_rigid, tp)  in
                    (match uu____8508 with
                     | (rank,tp1) ->
                         let uu____8828 =
                           FStar_All.pipe_right
                             (let uu___134_8834 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___134_8834.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___134_8834.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___134_8834.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___134_8834.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___134_8834.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___134_8834.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___134_8834.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___134_8834.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___134_8834.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____8828))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8844 =
            FStar_All.pipe_right
              (let uu___135_8850 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___135_8850.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___135_8850.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___135_8850.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___135_8850.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___135_8850.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___135_8850.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___135_8850.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___135_8850.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___135_8850.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____8844)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____8905 probs =
      match uu____8905 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8958 = rank wl hd1  in
               (match uu____8958 with
                | (rank1,hd2) ->
                    if rank1 <= flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out (m :: tl1)), rank1))
                    else
                      if rank1 < min_rank
                      then
                        (match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2),
                                 out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2), (m
                                 :: out)) tl1)
                      else aux (min_rank, min1, (hd2 :: out)) tl1))
       in
    aux
      ((flex_flex + (Prims.parse_int "1")), FStar_Pervasives_Native.None, [])
      wl.attempting
  
let (is_flex_rigid : Prims.int -> Prims.bool) =
  fun rank1  -> (flex_refine_inner <= rank1) && (rank1 <= flex_rigid) 
let (is_rigid_flex : Prims.int -> Prims.bool) =
  fun rank1  -> (rigid_flex <= rank1) && (rank1 <= refine_flex) 
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string [@@deriving show]
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____9065 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9077 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9089 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> Prims.string) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____9129 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9129 with
                        | (k,uu____9135) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9145 -> false)))
            | uu____9146 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9194 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9200 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9200 = (Prims.parse_int "0")))
                           in
                        if uu____9194 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9214 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9220 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9220 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9214)
               in
            let uu____9221 = filter1 u12  in
            let uu____9224 = filter1 u22  in (uu____9221, uu____9224)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9247 = filter_out_common_univs us1 us2  in
                (match uu____9247 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9300 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9300 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9303 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9313 =
                          let uu____9314 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9315 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9314
                            uu____9315
                           in
                        UFailed uu____9313))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9335 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9335 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9357 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9357 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9360 ->
                let uu____9365 =
                  let uu____9366 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9367 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9366
                    uu____9367 msg
                   in
                UFailed uu____9365
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9368,uu____9369) ->
              let uu____9370 =
                let uu____9371 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9372 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9371 uu____9372
                 in
              failwith uu____9370
          | (FStar_Syntax_Syntax.U_unknown ,uu____9373) ->
              let uu____9374 =
                let uu____9375 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9376 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9375 uu____9376
                 in
              failwith uu____9374
          | (uu____9377,FStar_Syntax_Syntax.U_bvar uu____9378) ->
              let uu____9379 =
                let uu____9380 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9381 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9380 uu____9381
                 in
              failwith uu____9379
          | (uu____9382,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9383 =
                let uu____9384 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9385 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9384 uu____9385
                 in
              failwith uu____9383
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9409 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9409
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9431 = occurs_univ v1 u3  in
              if uu____9431
              then
                let uu____9432 =
                  let uu____9433 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9434 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9433 uu____9434
                   in
                try_umax_components u11 u21 uu____9432
              else
                (let uu____9436 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9436)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9456 = occurs_univ v1 u3  in
              if uu____9456
              then
                let uu____9457 =
                  let uu____9458 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9459 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9458 uu____9459
                   in
                try_umax_components u11 u21 uu____9457
              else
                (let uu____9461 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9461)
          | (FStar_Syntax_Syntax.U_max uu____9470,uu____9471) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9477 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9477
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9479,FStar_Syntax_Syntax.U_max uu____9480) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9486 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9486
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9488,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9489,FStar_Syntax_Syntax.U_name
             uu____9490) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9491) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9492) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9493,FStar_Syntax_Syntax.U_succ
             uu____9494) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9495,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
  
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
  
let match_num_binders :
  'a 'b .
    ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
      ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
        (('a Prims.list,'b) FStar_Pervasives_Native.tuple2,('a Prims.list,
                                                             'b)
                                                             FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2
  =
  fun bc1  ->
    fun bc2  ->
      let uu____9581 = bc1  in
      match uu____9581 with
      | (bs1,mk_cod1) ->
          let uu____9622 = bc2  in
          (match uu____9622 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9726 = aux xs ys  in
                     (match uu____9726 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9809 =
                       let uu____9816 = mk_cod1 xs  in ([], uu____9816)  in
                     let uu____9819 =
                       let uu____9826 = mk_cod2 ys  in ([], uu____9826)  in
                     (uu____9809, uu____9819)
                  in
               aux bs1 bs2)
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9937 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9937
       then
         let uu____9938 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9938
       else ());
      (let uu____9940 = next_prob probs  in
       match uu____9940 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___136_9961 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___136_9961.wl_deferred);
               ctr = (uu___136_9961.ctr);
               defer_ok = (uu___136_9961.defer_ok);
               smt_ok = (uu___136_9961.smt_ok);
               tcenv = (uu___136_9961.tcenv)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                if
                  ((Prims.op_Negation probs1.defer_ok) &&
                     (flex_refine_inner <= rank1))
                    && (rank1 <= flex_rigid)
                then
                  let uu____9972 = solve_flex_rigid_join env tp probs1  in
                  (match uu____9972 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9977 = solve_rigid_flex_meet env tp probs1  in
                     match uu____9977 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9982,uu____9983) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____10000 ->
                let uu____10009 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10068  ->
                          match uu____10068 with
                          | (c,uu____10076,uu____10077) -> c < probs.ctr))
                   in
                (match uu____10009 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10118 =
                            FStar_List.map
                              (fun uu____10133  ->
                                 match uu____10133 with
                                 | (uu____10144,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____10118
                      | uu____10147 ->
                          let uu____10156 =
                            let uu___137_10157 = probs  in
                            let uu____10158 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10179  ->
                                      match uu____10179 with
                                      | (uu____10186,uu____10187,y) -> y))
                               in
                            {
                              attempting = uu____10158;
                              wl_deferred = rest;
                              ctr = (uu___137_10157.ctr);
                              defer_ok = (uu___137_10157.defer_ok);
                              smt_ok = (uu___137_10157.smt_ok);
                              tcenv = (uu___137_10157.tcenv)
                            }  in
                          solve env uu____10156))))

and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____10194 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10194 with
            | USolved wl1 ->
                let uu____10196 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10196
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env  ->
    fun orig  ->
      fun t1  ->
        fun t2  ->
          fun wl  ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([],[]) -> USolved wl1
              | (u1::us11,u2::us21) ->
                  let uu____10242 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10242 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10245 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10257;
                  FStar_Syntax_Syntax.vars = uu____10258;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10261;
                  FStar_Syntax_Syntax.vars = uu____10262;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10284,uu____10285) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10292,FStar_Syntax_Syntax.Tm_uinst uu____10293) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10300 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____10310 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10310
              then
                let uu____10311 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10311 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10320 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10320
         then
           let uu____10321 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10321
         else ());
        (let uu____10323 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____10323 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10385 = head_matches_delta env () t1 t2  in
               match uu____10385 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10426 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10475 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10490 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10491 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10490, uu____10491)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10496 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10497 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10496, uu____10497)
                           in
                        (match uu____10475 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10523 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10523
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10554 =
                                    let uu____10563 =
                                      let uu____10566 =
                                        let uu____10569 =
                                          let uu____10570 =
                                            let uu____10577 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____10577)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10570
                                           in
                                        FStar_Syntax_Syntax.mk uu____10569
                                         in
                                      uu____10566
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____10585 =
                                      let uu____10588 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____10588]  in
                                    (uu____10563, uu____10585)  in
                                  FStar_Pervasives_Native.Some uu____10554
                              | (uu____10601,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10603)) ->
                                  let uu____10608 =
                                    let uu____10615 =
                                      let uu____10618 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____10618]  in
                                    (t11, uu____10615)  in
                                  FStar_Pervasives_Native.Some uu____10608
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10628),uu____10629) ->
                                  let uu____10634 =
                                    let uu____10641 =
                                      let uu____10644 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____10644]  in
                                    (t21, uu____10641)  in
                                  FStar_Pervasives_Native.Some uu____10634
                              | uu____10653 ->
                                  let uu____10658 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____10658 with
                                   | (head1,uu____10682) ->
                                       let uu____10703 =
                                         let uu____10704 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____10704.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____10703 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10715;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10717;_}
                                            ->
                                            let prev =
                                              if i > (Prims.parse_int "1")
                                              then
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                  (i - (Prims.parse_int "1"))
                                              else
                                                FStar_Syntax_Syntax.Delta_constant
                                               in
                                            let t12 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11
                                               in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t21
                                               in
                                            disjoin t12 t22
                                        | uu____10724 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10737) ->
                  let uu____10762 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___109_10788  ->
                            match uu___109_10788 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10795 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____10795 with
                                      | (u',uu____10811) ->
                                          let uu____10832 =
                                            let uu____10833 = whnf env u'  in
                                            uu____10833.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____10832 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10837) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10862 -> false))
                                 | uu____10863 -> false)
                            | uu____10866 -> false))
                     in
                  (match uu____10762 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10900 tps =
                         match uu____10900 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10948 =
                                    let uu____10957 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____10957  in
                                  (match uu____10948 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10992 -> FStar_Pervasives_Native.None)
                          in
                       let uu____11001 =
                         let uu____11010 =
                           let uu____11017 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____11017, [])  in
                         make_lower_bound uu____11010 lower_bounds  in
                       (match uu____11001 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____11029 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11029
                              then
                                FStar_Util.print_string "No lower bounds\n"
                              else ());
                             FStar_Pervasives_Native.None)
                        | FStar_Pervasives_Native.Some (lhs_bound,sub_probs)
                            ->
                            let eq_prob =
                              new_problem env lhs_bound
                                FStar_TypeChecker_Common.EQ
                                tp.FStar_TypeChecker_Common.rhs
                                FStar_Pervasives_Native.None
                                tp.FStar_TypeChecker_Common.loc
                                "meeting refinements"
                               in
                            ((let uu____11049 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____11049
                              then
                                let wl' =
                                  let uu___138_11051 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___138_11051.wl_deferred);
                                    ctr = (uu___138_11051.ctr);
                                    defer_ok = (uu___138_11051.defer_ok);
                                    smt_ok = (uu___138_11051.smt_ok);
                                    tcenv = (uu___138_11051.tcenv)
                                  }  in
                                let uu____11052 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____11052
                              else ());
                             (let uu____11054 =
                                solve_t env eq_prob
                                  (let uu___139_11056 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___139_11056.wl_deferred);
                                     ctr = (uu___139_11056.ctr);
                                     defer_ok = (uu___139_11056.defer_ok);
                                     smt_ok = (uu___139_11056.smt_ok);
                                     tcenv = (uu___139_11056.tcenv)
                                   })
                                 in
                              match uu____11054 with
                              | Success uu____11059 ->
                                  let wl1 =
                                    let uu___140_11061 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___140_11061.wl_deferred);
                                      ctr = (uu___140_11061.ctr);
                                      defer_ok = (uu___140_11061.defer_ok);
                                      smt_ok = (uu___140_11061.smt_ok);
                                      tcenv = (uu___140_11061.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____11063 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____11068 -> FStar_Pervasives_Native.None))))
              | uu____11069 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11078 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____11078
         then
           let uu____11079 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____11079
         else ());
        (let uu____11081 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____11081 with
         | (u,args) ->
             let uu____11120 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____11120 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____11161 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____11161 with
                    | (h1,args1) ->
                        let uu____11202 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____11202 with
                         | (h2,uu____11222) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11249 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____11249
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11267 =
                                          let uu____11270 =
                                            let uu____11271 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____11271
                                             in
                                          [uu____11270]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11267))
                                  else FStar_Pervasives_Native.None
                              | (FStar_Syntax_Syntax.Tm_name
                                 a,FStar_Syntax_Syntax.Tm_name b) ->
                                  if FStar_Syntax_Syntax.bv_eq a b
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11304 =
                                          let uu____11307 =
                                            let uu____11308 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____11308
                                             in
                                          [uu____11307]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11304))
                                  else FStar_Pervasives_Native.None
                              | uu____11322 -> FStar_Pervasives_Native.None))
                     in
                  let conjoin t1 t2 =
                    match ((t1.FStar_Syntax_Syntax.n),
                            (t2.FStar_Syntax_Syntax.n))
                    with
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,phi1),FStar_Syntax_Syntax.Tm_refine (y,phi2)) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort
                            y.FStar_Syntax_Syntax.sort
                           in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x  in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)]
                                in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                                in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2
                                in
                             let uu____11412 =
                               let uu____11421 =
                                 let uu____11424 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____11424  in
                               (uu____11421, m1)  in
                             FStar_Pervasives_Native.Some uu____11412)
                    | (uu____11437,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11439)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11487),uu____11488) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11535 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11588) ->
                       let uu____11613 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___110_11639  ->
                                 match uu___110_11639 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11646 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____11646 with
                                           | (u',uu____11662) ->
                                               let uu____11683 =
                                                 let uu____11684 =
                                                   whnf env u'  in
                                                 uu____11684.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____11683 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11688) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11713 -> false))
                                      | uu____11714 -> false)
                                 | uu____11717 -> false))
                          in
                       (match uu____11613 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11755 tps =
                              match uu____11755 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11817 =
                                         let uu____11828 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____11828  in
                                       (match uu____11817 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11879 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____11890 =
                              let uu____11901 =
                                let uu____11910 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____11910, [])  in
                              make_upper_bound uu____11901 upper_bounds  in
                            (match uu____11890 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11924 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11924
                                   then
                                     FStar_Util.print_string
                                       "No upper bounds\n"
                                   else ());
                                  FStar_Pervasives_Native.None)
                             | FStar_Pervasives_Native.Some
                                 (rhs_bound,sub_probs) ->
                                 let eq_prob =
                                   new_problem env
                                     tp.FStar_TypeChecker_Common.lhs
                                     FStar_TypeChecker_Common.EQ rhs_bound
                                     FStar_Pervasives_Native.None
                                     tp.FStar_TypeChecker_Common.loc
                                     "joining refinements"
                                    in
                                 ((let uu____11950 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11950
                                   then
                                     let wl' =
                                       let uu___141_11952 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___141_11952.wl_deferred);
                                         ctr = (uu___141_11952.ctr);
                                         defer_ok = (uu___141_11952.defer_ok);
                                         smt_ok = (uu___141_11952.smt_ok);
                                         tcenv = (uu___141_11952.tcenv)
                                       }  in
                                     let uu____11953 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11953
                                   else ());
                                  (let uu____11955 =
                                     solve_t env eq_prob
                                       (let uu___142_11957 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___142_11957.wl_deferred);
                                          ctr = (uu___142_11957.ctr);
                                          defer_ok =
                                            (uu___142_11957.defer_ok);
                                          smt_ok = (uu___142_11957.smt_ok);
                                          tcenv = (uu___142_11957.tcenv)
                                        })
                                      in
                                   match uu____11955 with
                                   | Success uu____11960 ->
                                       let wl1 =
                                         let uu___143_11962 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___143_11962.wl_deferred);
                                           ctr = (uu___143_11962.ctr);
                                           defer_ok =
                                             (uu___143_11962.defer_ok);
                                           smt_ok = (uu___143_11962.smt_ok);
                                           tcenv = (uu___143_11962.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____11964 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11969 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11970 -> failwith "Impossible: Not a flex-rigid")))

and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (FStar_Syntax_Syntax.binders ->
               FStar_TypeChecker_Env.env ->
                 FStar_Syntax_Syntax.subst_elt Prims.list ->
                   FStar_TypeChecker_Common.prob)
              -> solution)
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              let rec aux scope env1 subst1 xs ys =
                match (xs, ys) with
                | ([],[]) ->
                    let rhs_prob = rhs scope env1 subst1  in
                    ((let uu____12045 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12045
                      then
                        let uu____12046 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____12046
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___144_12100 = hd1  in
                      let uu____12101 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___144_12100.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___144_12100.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12101
                      }  in
                    let hd21 =
                      let uu___145_12105 = hd2  in
                      let uu____12106 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___145_12105.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___145_12105.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12106
                      }  in
                    let prob =
                      let uu____12110 =
                        let uu____12115 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____12115 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____12110
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____12126 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____12126
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____12130 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1
                       in
                    (match uu____12130 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____12168 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____12173 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____12168 uu____12173
                            in
                         ((let uu____12183 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____12183
                           then
                             let uu____12184 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____12185 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____12184 uu____12185
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail1 -> fail1)
                | uu____12208 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____12218 = aux scope env [] bs1 bs2  in
              match uu____12218 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl
                     in
                  solve env (attempt sub_probs wl1)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____12243 = compress_tprob wl problem  in
         solve_t' env uu____12243 wl)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____12277 = head_matches_delta env1 wl1 t1 t2  in
           match uu____12277 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____12308,uu____12309) ->
                    let rec may_relate head3 =
                      let uu____12334 =
                        let uu____12335 = FStar_Syntax_Subst.compress head3
                           in
                        uu____12335.FStar_Syntax_Syntax.n  in
                      match uu____12334 with
                      | FStar_Syntax_Syntax.Tm_name uu____12338 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____12339 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12362;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational ;
                            FStar_Syntax_Syntax.fv_qual = uu____12363;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12366;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____12367;
                            FStar_Syntax_Syntax.fv_qual = uu____12368;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____12372,uu____12373) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____12415) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____12421) ->
                          may_relate t
                      | uu____12426 -> false  in
                    let uu____12427 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____12427
                    then
                      let guard =
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then mk_eq2 orig t1 t2
                        else
                          (let has_type_guard t11 t21 =
                             match problem.FStar_TypeChecker_Common.element
                             with
                             | FStar_Pervasives_Native.Some t ->
                                 FStar_Syntax_Util.mk_has_type t11 t t21
                             | FStar_Pervasives_Native.None  ->
                                 let x =
                                   FStar_Syntax_Syntax.new_bv
                                     FStar_Pervasives_Native.None t11
                                    in
                                 let u_x =
                                   env1.FStar_TypeChecker_Env.universe_of
                                     env1 t11
                                    in
                                 let uu____12444 =
                                   let uu____12445 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____12445 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____12444
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then has_type_guard t1 t2
                           else has_type_guard t2 t1)
                         in
                      let uu____12447 =
                        solve_prob orig (FStar_Pervasives_Native.Some guard)
                          [] wl1
                         in
                      solve env1 uu____12447
                    else
                      (let uu____12449 =
                         let uu____12450 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12451 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____12450 uu____12451
                          in
                       giveup env1 uu____12449 orig)
                | (uu____12452,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___146_12466 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___146_12466.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___146_12466.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___146_12466.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___146_12466.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___146_12466.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___146_12466.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___146_12466.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___146_12466.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____12467,FStar_Pervasives_Native.None ) ->
                    ((let uu____12479 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12479
                      then
                        let uu____12480 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____12481 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____12482 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____12483 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____12480
                          uu____12481 uu____12482 uu____12483
                      else ());
                     (let uu____12485 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____12485 with
                      | (head11,args1) ->
                          let uu____12522 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____12522 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____12576 =
                                   let uu____12577 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____12578 = args_to_string args1  in
                                   let uu____12579 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____12580 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____12577 uu____12578 uu____12579
                                     uu____12580
                                    in
                                 giveup env1 uu____12576 orig
                               else
                                 (let uu____12582 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____12588 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____12588 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____12582
                                  then
                                    let uu____12589 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____12589 with
                                    | USolved wl2 ->
                                        let uu____12591 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____12591
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____12595 =
                                       base_and_refinement env1 t1  in
                                     match uu____12595 with
                                     | (base1,refinement1) ->
                                         let uu____12620 =
                                           base_and_refinement env1 t2  in
                                         (match uu____12620 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____12677 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____12677 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let subprobs =
                                                          FStar_List.map2
                                                            (fun uu____12699 
                                                               ->
                                                               fun
                                                                 uu____12700 
                                                                 ->
                                                                 match 
                                                                   (uu____12699,
                                                                    uu____12700)
                                                                 with
                                                                 | ((a,uu____12718),
                                                                    (a',uu____12720))
                                                                    ->
                                                                    let uu____12729
                                                                    =
                                                                    let uu____12734
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____12734
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_56  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_56)
                                                                    uu____12729)
                                                            args1 args2
                                                           in
                                                        let formula =
                                                          let uu____12740 =
                                                            FStar_List.map
                                                              (fun p  ->
                                                                 FStar_Pervasives_Native.fst
                                                                   (p_guard p))
                                                              subprobs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____12740
                                                           in
                                                        let wl3 =
                                                          solve_prob orig
                                                            (FStar_Pervasives_Native.Some
                                                               formula) []
                                                            wl2
                                                           in
                                                        solve env1
                                                          (attempt subprobs
                                                             wl3))
                                               | uu____12746 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___147_12782 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___147_12782.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___147_12782.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___147_12782.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___147_12782.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.scope
                                                          =
                                                          (uu___147_12782.FStar_TypeChecker_Common.scope);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___147_12782.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___147_12782.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___147_12782.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let force_quasi_pattern xs_opt uu____12815 =
           match uu____12815 with
           | (t,u,k,args) ->
               let debug1 f =
                 let uu____12857 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____12857 then f () else ()  in
               let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                 seen_formals formals res_t args1 =
                 debug1
                   (fun uu____12953  ->
                      let uu____12954 =
                        FStar_Syntax_Print.binders_to_string ", " pat_args
                         in
                      FStar_Util.print1 "pat_args so far: {%s}\n" uu____12954);
                 (match (formals, args1) with
                  | ([],[]) ->
                      let pat_args1 =
                        FStar_All.pipe_right (FStar_List.rev pat_args)
                          (FStar_List.map
                             (fun uu____13022  ->
                                match uu____13022 with
                                | (x,imp) ->
                                    let uu____13033 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____13033, imp)))
                         in
                      let pattern_vars1 = FStar_List.rev pattern_vars  in
                      let kk =
                        let uu____13046 = FStar_Syntax_Util.type_u ()  in
                        match uu____13046 with
                        | (t1,uu____13052) ->
                            let uu____13053 =
                              new_uvar t1.FStar_Syntax_Syntax.pos
                                pattern_vars1 t1
                               in
                            FStar_Pervasives_Native.fst uu____13053
                         in
                      let uu____13058 =
                        new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                         in
                      (match uu____13058 with
                       | (t',tm_u1) ->
                           let uu____13071 = destruct_flex_t t'  in
                           (match uu____13071 with
                            | (uu____13108,u1,k1,uu____13111) ->
                                let all_formals = FStar_List.rev seen_formals
                                   in
                                let k2 =
                                  let uu____13170 =
                                    FStar_Syntax_Syntax.mk_Total res_t  in
                                  FStar_Syntax_Util.arrow all_formals
                                    uu____13170
                                   in
                                let sol =
                                  let uu____13174 =
                                    let uu____13183 = u_abs k2 all_formals t'
                                       in
                                    ((u, k2), uu____13183)  in
                                  TERM uu____13174  in
                                let t_app =
                                  FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                    pat_args1 FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                FStar_Pervasives_Native.Some
                                  (sol, (t_app, u1, k1, pat_args1))))
                  | (formal::formals1,hd1::tl1) ->
                      (debug1
                         (fun uu____13318  ->
                            let uu____13319 =
                              FStar_Syntax_Print.binder_to_string formal  in
                            let uu____13320 =
                              FStar_Syntax_Print.args_to_string [hd1]  in
                            FStar_Util.print2
                              "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                              uu____13319 uu____13320);
                       (let uu____13333 = pat_var_opt env pat_args hd1  in
                        match uu____13333 with
                        | FStar_Pervasives_Native.None  ->
                            (debug1
                               (fun uu____13353  ->
                                  FStar_Util.print_string
                                    "not a pattern var\n");
                             aux pat_args pat_args_set pattern_vars
                               pattern_var_set (formal :: seen_formals)
                               formals1 res_t tl1)
                        | FStar_Pervasives_Native.Some y ->
                            let maybe_pat =
                              match xs_opt with
                              | FStar_Pervasives_Native.None  -> true
                              | FStar_Pervasives_Native.Some xs ->
                                  FStar_All.pipe_right xs
                                    (FStar_Util.for_some
                                       (fun uu____13396  ->
                                          match uu____13396 with
                                          | (x,uu____13402) ->
                                              FStar_Syntax_Syntax.bv_eq x
                                                (FStar_Pervasives_Native.fst
                                                   y)))
                               in
                            if Prims.op_Negation maybe_pat
                            then
                              aux pat_args pat_args_set pattern_vars
                                pattern_var_set (formal :: seen_formals)
                                formals1 res_t tl1
                            else
                              (debug1
                                 (fun uu____13417  ->
                                    let uu____13418 =
                                      FStar_Syntax_Print.args_to_string [hd1]
                                       in
                                    let uu____13431 =
                                      FStar_Syntax_Print.binder_to_string y
                                       in
                                    FStar_Util.print2
                                      "%s (var = %s) maybe pat\n" uu____13418
                                      uu____13431);
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                   in
                                let uu____13435 =
                                  let uu____13436 =
                                    FStar_Util.set_is_subset_of fvs
                                      pat_args_set
                                     in
                                  Prims.op_Negation uu____13436  in
                                if uu____13435
                                then
                                  (debug1
                                     (fun uu____13448  ->
                                        let uu____13449 =
                                          let uu____13452 =
                                            FStar_Syntax_Print.args_to_string
                                              [hd1]
                                             in
                                          let uu____13465 =
                                            let uu____13468 =
                                              FStar_Syntax_Print.binder_to_string
                                                y
                                               in
                                            let uu____13469 =
                                              let uu____13472 =
                                                FStar_Syntax_Print.term_to_string
                                                  (FStar_Pervasives_Native.fst
                                                     y).FStar_Syntax_Syntax.sort
                                                 in
                                              let uu____13473 =
                                                let uu____13476 =
                                                  names_to_string fvs  in
                                                let uu____13477 =
                                                  let uu____13480 =
                                                    names_to_string
                                                      pattern_var_set
                                                     in
                                                  [uu____13480]  in
                                                uu____13476 :: uu____13477
                                                 in
                                              uu____13472 :: uu____13473  in
                                            uu____13468 :: uu____13469  in
                                          uu____13452 :: uu____13465  in
                                        FStar_Util.print
                                          "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                          uu____13449);
                                   aux pat_args pat_args_set pattern_vars
                                     pattern_var_set (formal :: seen_formals)
                                     formals1 res_t tl1)
                                else
                                  (let uu____13482 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst y)
                                       pat_args_set
                                      in
                                   let uu____13485 =
                                     FStar_Util.set_add
                                       (FStar_Pervasives_Native.fst formal)
                                       pattern_var_set
                                      in
                                   aux (y :: pat_args) uu____13482 (formal ::
                                     pattern_vars) uu____13485 (formal ::
                                     seen_formals) formals1 res_t tl1)))))
                  | ([],uu____13492::uu____13493) ->
                      let uu____13524 =
                        let uu____13537 =
                          FStar_TypeChecker_Normalize.unfold_whnf env res_t
                           in
                        FStar_Syntax_Util.arrow_formals uu____13537  in
                      (match uu____13524 with
                       | (more_formals,res_t1) ->
                           (match more_formals with
                            | [] -> FStar_Pervasives_Native.None
                            | uu____13576 ->
                                aux pat_args pat_args_set pattern_vars
                                  pattern_var_set seen_formals more_formals
                                  res_t1 args1))
                  | (uu____13583::uu____13584,[]) ->
                      FStar_Pervasives_Native.None)
                  in
               let uu____13607 =
                 let uu____13620 =
                   FStar_TypeChecker_Normalize.unfold_whnf env k  in
                 FStar_Syntax_Util.arrow_formals uu____13620  in
               (match uu____13607 with
                | (all_formals,res_t) ->
                    (debug1
                       (fun uu____13656  ->
                          let uu____13657 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____13658 =
                            FStar_Syntax_Print.binders_to_string ", "
                              all_formals
                             in
                          let uu____13659 =
                            FStar_Syntax_Print.term_to_string res_t  in
                          let uu____13660 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.print4
                            "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                            uu____13657 uu____13658 uu____13659 uu____13660);
                     (let uu____13661 = FStar_Syntax_Syntax.new_bv_set ()  in
                      let uu____13664 = FStar_Syntax_Syntax.new_bv_set ()  in
                      aux [] uu____13661 [] uu____13664 [] all_formals res_t
                        args)))
            in
         let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
           let uu____13698 = lhs  in
           match uu____13698 with
           | (t1,uv,k_uv,args_lhs) ->
               let sol =
                 match pat_vars1 with
                 | [] -> rhs
                 | uu____13708 ->
                     let uu____13709 = sn_binders env1 pat_vars1  in
                     u_abs k_uv uu____13709 rhs
                  in
               let wl2 =
                 solve_prob orig FStar_Pervasives_Native.None
                   [TERM ((uv, k_uv), sol)] wl1
                  in
               solve env1 wl2
            in
         let imitate orig env1 wl1 p =
           let uu____13732 = p  in
           match uu____13732 with
           | (((u,k),xs,c),ps,(h,uu____13743,qs)) ->
               let xs1 = sn_binders env1 xs  in
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____13825 = imitation_sub_probs orig env1 xs1 ps qs  in
               (match uu____13825 with
                | (sub_probs,gs_xs,formula) ->
                    let im =
                      let uu____13848 = h gs_xs  in
                      let uu____13849 =
                        FStar_All.pipe_right
                          (FStar_Syntax_Util.residual_comp_of_comp c)
                          (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                         in
                      FStar_Syntax_Util.abs xs1 uu____13848 uu____13849  in
                    ((let uu____13855 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13855
                      then
                        let uu____13856 =
                          let uu____13859 =
                            let uu____13860 =
                              FStar_List.map tc_to_string gs_xs  in
                            FStar_All.pipe_right uu____13860
                              (FStar_String.concat "\n\t>")
                             in
                          let uu____13865 =
                            let uu____13868 =
                              FStar_Syntax_Print.binders_to_string ", " xs1
                               in
                            let uu____13869 =
                              let uu____13872 =
                                FStar_Syntax_Print.comp_to_string c  in
                              let uu____13873 =
                                let uu____13876 =
                                  FStar_Syntax_Print.term_to_string im  in
                                let uu____13877 =
                                  let uu____13880 =
                                    FStar_Syntax_Print.tag_of_term im  in
                                  let uu____13881 =
                                    let uu____13884 =
                                      let uu____13885 =
                                        FStar_List.map (prob_to_string env1)
                                          sub_probs
                                         in
                                      FStar_All.pipe_right uu____13885
                                        (FStar_String.concat ", ")
                                       in
                                    let uu____13890 =
                                      let uu____13893 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env1 formula
                                         in
                                      [uu____13893]  in
                                    uu____13884 :: uu____13890  in
                                  uu____13880 :: uu____13881  in
                                uu____13876 :: uu____13877  in
                              uu____13872 :: uu____13873  in
                            uu____13868 :: uu____13869  in
                          uu____13859 :: uu____13865  in
                        FStar_Util.print
                          "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                          uu____13856
                      else ());
                     def_check_closed (p_loc orig) "imitate" im;
                     (let wl2 =
                        solve_prob orig
                          (FStar_Pervasives_Native.Some formula)
                          [TERM ((u, k), im)] wl1
                         in
                      solve env1 (attempt sub_probs wl2))))
            in
         let imitate' orig env1 wl1 uu___111_13915 =
           match uu___111_13915 with
           | FStar_Pervasives_Native.None  ->
               giveup env1 "unable to compute subterms" orig
           | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
         let project orig env1 wl1 i p =
           let uu____13947 = p  in
           match uu____13947 with
           | ((u,xs,c),ps,(h,matches,qs)) ->
               let r = FStar_TypeChecker_Env.get_range env1  in
               let uu____14038 = FStar_List.nth ps i  in
               (match uu____14038 with
                | (pi,uu____14042) ->
                    let uu____14047 = FStar_List.nth xs i  in
                    (match uu____14047 with
                     | (xi,uu____14059) ->
                         let rec gs k =
                           let uu____14072 =
                             let uu____14085 =
                               FStar_TypeChecker_Normalize.unfold_whnf env1 k
                                in
                             FStar_Syntax_Util.arrow_formals uu____14085  in
                           match uu____14072 with
                           | (bs,k1) ->
                               let rec aux subst1 bs1 =
                                 match bs1 with
                                 | [] -> ([], [])
                                 | (a,uu____14160)::tl1 ->
                                     let k_a =
                                       FStar_Syntax_Subst.subst subst1
                                         a.FStar_Syntax_Syntax.sort
                                        in
                                     let uu____14173 = new_uvar r xs k_a  in
                                     (match uu____14173 with
                                      | (gi_xs,gi) ->
                                          let gi_xs1 =
                                            FStar_TypeChecker_Normalize.eta_expand
                                              env1 gi_xs
                                             in
                                          let gi_ps =
                                            FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps FStar_Pervasives_Native.None
                                              r
                                             in
                                          let subst2 =
                                            (FStar_Syntax_Syntax.NT
                                               (a, gi_xs1))
                                            :: subst1  in
                                          let uu____14195 = aux subst2 tl1
                                             in
                                          (match uu____14195 with
                                           | (gi_xs',gi_ps') ->
                                               let uu____14222 =
                                                 let uu____14225 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_xs1
                                                    in
                                                 uu____14225 :: gi_xs'  in
                                               let uu____14226 =
                                                 let uu____14229 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     gi_ps
                                                    in
                                                 uu____14229 :: gi_ps'  in
                                               (uu____14222, uu____14226)))
                                  in
                               aux [] bs
                            in
                         let uu____14234 =
                           let uu____14235 = matches pi  in
                           FStar_All.pipe_left Prims.op_Negation uu____14235
                            in
                         if uu____14234
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____14239 = gs xi.FStar_Syntax_Syntax.sort
                               in
                            match uu____14239 with
                            | (g_xs,uu____14251) ->
                                let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                   in
                                let proj =
                                  let uu____14262 =
                                    FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                      FStar_Pervasives_Native.None r
                                     in
                                  let uu____14263 =
                                    FStar_All.pipe_right
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         c)
                                      (fun _0_58  ->
                                         FStar_Pervasives_Native.Some _0_58)
                                     in
                                  FStar_Syntax_Util.abs xs uu____14262
                                    uu____14263
                                   in
                                let sub1 =
                                  let uu____14269 =
                                    let uu____14274 = p_scope orig  in
                                    let uu____14275 =
                                      FStar_Syntax_Syntax.mk_Tm_app proj ps
                                        FStar_Pervasives_Native.None r
                                       in
                                    let uu____14278 =
                                      let uu____14281 =
                                        FStar_List.map
                                          (fun uu____14296  ->
                                             match uu____14296 with
                                             | (uu____14305,uu____14306,y) ->
                                                 y) qs
                                         in
                                      FStar_All.pipe_left h uu____14281  in
                                    mk_problem uu____14274 orig uu____14275
                                      (p_rel orig) uu____14278
                                      FStar_Pervasives_Native.None
                                      "projection"
                                     in
                                  FStar_All.pipe_left
                                    (fun _0_59  ->
                                       FStar_TypeChecker_Common.TProb _0_59)
                                    uu____14269
                                   in
                                ((let uu____14321 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14321
                                  then
                                    let uu____14322 =
                                      FStar_Syntax_Print.term_to_string proj
                                       in
                                    let uu____14323 =
                                      prob_to_string env1 sub1  in
                                    FStar_Util.print2
                                      "Projecting %s\n\tsubprob=%s\n"
                                      uu____14322 uu____14323
                                  else ());
                                 (let wl2 =
                                    let uu____14326 =
                                      let uu____14329 =
                                        FStar_All.pipe_left
                                          FStar_Pervasives_Native.fst
                                          (p_guard sub1)
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____14329
                                       in
                                    solve_prob orig uu____14326
                                      [TERM (u, proj)] wl1
                                     in
                                  let uu____14338 =
                                    solve env1 (attempt [sub1] wl2)  in
                                  FStar_All.pipe_left
                                    (fun _0_60  ->
                                       FStar_Pervasives_Native.Some _0_60)
                                    uu____14338)))))
            in
         let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
           let uu____14369 = lhs  in
           match uu____14369 with
           | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
               let subterms ps =
                 let uu____14405 = FStar_Syntax_Util.arrow_formals_comp k_uv
                    in
                 match uu____14405 with
                 | (xs,c) ->
                     if (FStar_List.length xs) = (FStar_List.length ps)
                     then
                       let uu____14438 =
                         let uu____14485 = decompose env t2  in
                         (((uv, k_uv), xs, c), ps, uu____14485)  in
                       FStar_Pervasives_Native.Some uu____14438
                     else
                       (let rec elim k args =
                          let k1 =
                            FStar_TypeChecker_Normalize.unfold_whnf env k  in
                          let uu____14629 =
                            let uu____14636 =
                              let uu____14637 =
                                FStar_Syntax_Subst.compress k1  in
                              uu____14637.FStar_Syntax_Syntax.n  in
                            (uu____14636, args)  in
                          match uu____14629 with
                          | (uu____14648,[]) ->
                              let uu____14651 =
                                let uu____14662 =
                                  FStar_Syntax_Syntax.mk_Total k1  in
                                ([], uu____14662)  in
                              FStar_Pervasives_Native.Some uu____14651
                          | (FStar_Syntax_Syntax.Tm_uvar
                             uu____14683,uu____14684) ->
                              let uu____14705 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____14705 with
                               | (uv1,uv_args) ->
                                   let uu____14748 =
                                     let uu____14749 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____14749.FStar_Syntax_Syntax.n  in
                                   (match uu____14748 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____14759) ->
                                        let uu____14784 =
                                          pat_vars env [] uv_args  in
                                        (match uu____14784 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____14811  ->
                                                       let uu____14812 =
                                                         let uu____14813 =
                                                           let uu____14814 =
                                                             let uu____14819
                                                               =
                                                               let uu____14820
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____14820
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____14819
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____14814
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____14813
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____14812))
                                                in
                                             let c1 =
                                               let uu____14830 =
                                                 let uu____14831 =
                                                   let uu____14836 =
                                                     let uu____14837 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14837
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____14836
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____14831
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____14830
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____14850 =
                                                 let uu____14853 =
                                                   let uu____14854 =
                                                     let uu____14857 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____14857
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____14854
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____14853
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____14850
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____14876 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_app
                             uu____14881,uu____14882) ->
                              let uu____14901 =
                                FStar_Syntax_Util.head_and_args k1  in
                              (match uu____14901 with
                               | (uv1,uv_args) ->
                                   let uu____14944 =
                                     let uu____14945 =
                                       FStar_Syntax_Subst.compress uv1  in
                                     uu____14945.FStar_Syntax_Syntax.n  in
                                   (match uu____14944 with
                                    | FStar_Syntax_Syntax.Tm_uvar
                                        (uvar,uu____14955) ->
                                        let uu____14980 =
                                          pat_vars env [] uv_args  in
                                        (match uu____14980 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some scope
                                             ->
                                             let xs1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.map
                                                    (fun uu____15007  ->
                                                       let uu____15008 =
                                                         let uu____15009 =
                                                           let uu____15010 =
                                                             let uu____15015
                                                               =
                                                               let uu____15016
                                                                 =
                                                                 FStar_Syntax_Util.type_u
                                                                   ()
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15016
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             new_uvar
                                                               k1.FStar_Syntax_Syntax.pos
                                                               scope
                                                               uu____15015
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____15010
                                                            in
                                                         FStar_Syntax_Syntax.new_bv
                                                           (FStar_Pervasives_Native.Some
                                                              (k1.FStar_Syntax_Syntax.pos))
                                                           uu____15009
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Syntax.mk_binder
                                                         uu____15008))
                                                in
                                             let c1 =
                                               let uu____15026 =
                                                 let uu____15027 =
                                                   let uu____15032 =
                                                     let uu____15033 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15033
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   new_uvar
                                                     k1.FStar_Syntax_Syntax.pos
                                                     scope uu____15032
                                                    in
                                                 FStar_Pervasives_Native.fst
                                                   uu____15027
                                                  in
                                               FStar_Syntax_Syntax.mk_Total
                                                 uu____15026
                                                in
                                             let k' =
                                               FStar_Syntax_Util.arrow xs1 c1
                                                in
                                             let uv_sol =
                                               let uu____15046 =
                                                 let uu____15049 =
                                                   let uu____15050 =
                                                     let uu____15053 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____15053
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_Syntax_Util.residual_tot
                                                     uu____15050
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____15049
                                                  in
                                               FStar_Syntax_Util.abs scope k'
                                                 uu____15046
                                                in
                                             (def_check_closed (p_loc orig)
                                                "solve_t_flex_rigid.subterms"
                                                uv_sol;
                                              FStar_Syntax_Util.set_uvar uvar
                                                uv_sol;
                                              FStar_Pervasives_Native.Some
                                                (xs1, c1)))
                                    | uu____15072 ->
                                        FStar_Pervasives_Native.None))
                          | (FStar_Syntax_Syntax.Tm_arrow
                             (xs1,c1),uu____15079) ->
                              let n_args = FStar_List.length args  in
                              let n_xs = FStar_List.length xs1  in
                              if n_xs = n_args
                              then
                                let uu____15120 =
                                  FStar_Syntax_Subst.open_comp xs1 c1  in
                                FStar_All.pipe_right uu____15120
                                  (fun _0_61  ->
                                     FStar_Pervasives_Native.Some _0_61)
                              else
                                if n_xs < n_args
                                then
                                  (let uu____15156 =
                                     FStar_Util.first_N n_xs args  in
                                   match uu____15156 with
                                   | (args1,rest) ->
                                       let uu____15185 =
                                         FStar_Syntax_Subst.open_comp xs1 c1
                                          in
                                       (match uu____15185 with
                                        | (xs2,c2) ->
                                            let uu____15198 =
                                              elim
                                                (FStar_Syntax_Util.comp_result
                                                   c2) rest
                                               in
                                            FStar_Util.bind_opt uu____15198
                                              (fun uu____15222  ->
                                                 match uu____15222 with
                                                 | (xs',c3) ->
                                                     FStar_Pervasives_Native.Some
                                                       ((FStar_List.append
                                                           xs2 xs'), c3))))
                                else
                                  (let uu____15262 =
                                     FStar_Util.first_N n_args xs1  in
                                   match uu____15262 with
                                   | (xs2,rest) ->
                                       let t =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))
                                           FStar_Pervasives_Native.None
                                           k1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____15330 =
                                         let uu____15335 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Subst.open_comp xs2
                                           uu____15335
                                          in
                                       FStar_All.pipe_right uu____15330
                                         (fun _0_62  ->
                                            FStar_Pervasives_Native.Some
                                              _0_62))
                          | uu____15350 ->
                              let uu____15357 =
                                let uu____15362 =
                                  let uu____15363 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let uu____15364 =
                                    FStar_Syntax_Print.term_to_string k1  in
                                  let uu____15365 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    uu____15363 uu____15364 uu____15365
                                   in
                                (FStar_Errors.Fatal_IllTyped, uu____15362)
                                 in
                              FStar_Errors.raise_error uu____15357
                                t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____15372 = elim k_uv ps  in
                        FStar_Util.bind_opt uu____15372
                          (fun uu____15427  ->
                             match uu____15427 with
                             | (xs1,c1) ->
                                 let uu____15476 =
                                   let uu____15517 = decompose env t2  in
                                   (((uv, k_uv), xs1, c1), ps, uu____15517)
                                    in
                                 FStar_Pervasives_Native.Some uu____15476))
                  in
               let imitate_or_project n1 lhs1 rhs stopt =
                 let fail1 uu____15638 =
                   giveup env
                     "flex-rigid case failed all backtracking attempts" orig
                    in
                 let rec try_project st i =
                   if i >= n1
                   then fail1 ()
                   else
                     (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                      let uu____15652 = project orig env wl1 i st  in
                      match uu____15652 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____15666) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           try_project st (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)
                    in
                 if FStar_Option.isSome stopt
                 then
                   let st = FStar_Util.must stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   let uu____15681 = imitate orig env wl1 st  in
                   match uu____15681 with
                   | Failed uu____15686 ->
                       (FStar_Syntax_Unionfind.rollback tx;
                        try_project st (Prims.parse_int "0"))
                   | sol -> sol
                 else fail1 ()  in
               let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                 let uu____15717 =
                   force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                 match uu____15717 with
                 | FStar_Pervasives_Native.None  ->
                     imitate_or_project n1 lhs1 rhs stopt
                 | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                     let uu____15740 = forced_lhs_pattern  in
                     (match uu____15740 with
                      | (lhs_t,uu____15742,uu____15743,uu____15744) ->
                          ((let uu____15746 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15746
                            then
                              let uu____15747 = lhs1  in
                              match uu____15747 with
                              | (t0,uu____15749,uu____15750,uu____15751) ->
                                  let uu____15752 = forced_lhs_pattern  in
                                  (match uu____15752 with
                                   | (t11,uu____15754,uu____15755,uu____15756)
                                       ->
                                       let uu____15757 =
                                         FStar_Syntax_Print.term_to_string t0
                                          in
                                       let uu____15758 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       FStar_Util.print2
                                         "force_quasi_pattern succeeded, turning %s into %s\n"
                                         uu____15757 uu____15758)
                            else ());
                           (let rhs_vars = FStar_Syntax_Free.names rhs  in
                            let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                            let uu____15766 =
                              FStar_Util.set_is_subset_of rhs_vars lhs_vars
                               in
                            if uu____15766
                            then
                              ((let uu____15768 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____15768
                                then
                                  let uu____15769 =
                                    FStar_Syntax_Print.term_to_string rhs  in
                                  let uu____15770 = names_to_string rhs_vars
                                     in
                                  let uu____15771 = names_to_string lhs_vars
                                     in
                                  FStar_Util.print3
                                    "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                    uu____15769 uu____15770 uu____15771
                                else ());
                               (let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let wl2 =
                                  extend_solution (p_pid orig) [sol] wl1  in
                                let uu____15775 =
                                  let uu____15776 =
                                    FStar_TypeChecker_Common.as_tprob orig
                                     in
                                  solve_t env uu____15776 wl2  in
                                match uu____15775 with
                                | Failed uu____15777 ->
                                    (FStar_Syntax_Unionfind.rollback tx;
                                     imitate_or_project n1 lhs1 rhs stopt)
                                | sol1 -> sol1))
                            else
                              ((let uu____15786 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____15786
                                then
                                  FStar_Util.print_string
                                    "fvar check failed for quasi pattern ... im/proj\n"
                                else ());
                               imitate_or_project n1 lhs1 rhs stopt))))
                  in
               let check_head fvs1 t21 =
                 let uu____15799 = FStar_Syntax_Util.head_and_args t21  in
                 match uu____15799 with
                 | (hd1,uu____15815) ->
                     (match hd1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_arrow uu____15836 -> true
                      | FStar_Syntax_Syntax.Tm_constant uu____15849 -> true
                      | FStar_Syntax_Syntax.Tm_abs uu____15850 -> true
                      | uu____15867 ->
                          let fvs_hd = FStar_Syntax_Free.names hd1  in
                          let uu____15871 =
                            FStar_Util.set_is_subset_of fvs_hd fvs1  in
                          if uu____15871
                          then true
                          else
                            ((let uu____15874 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____15874
                              then
                                let uu____15875 = names_to_string fvs_hd  in
                                FStar_Util.print1 "Free variables are %s\n"
                                  uu____15875
                              else ());
                             false))
                  in
               (match maybe_pat_vars with
                | FStar_Pervasives_Native.Some vars ->
                    let t11 = sn env t1  in
                    let t21 = sn env t2  in
                    let lhs1 = (t11, uv, k_uv, args_lhs)  in
                    let fvs1 = FStar_Syntax_Free.names t11  in
                    let fvs2 = FStar_Syntax_Free.names t21  in
                    let uu____15895 = occurs_check env wl1 (uv, k_uv) t21  in
                    (match uu____15895 with
                     | (occurs_ok,msg) ->
                         if Prims.op_Negation occurs_ok
                         then
                           let uu____15908 =
                             let uu____15909 = FStar_Option.get msg  in
                             Prims.strcat "occurs-check failed: " uu____15909
                              in
                           giveup_or_defer1 orig uu____15908
                         else
                           (let uu____15911 =
                              FStar_Util.set_is_subset_of fvs2 fvs1  in
                            if uu____15911
                            then
                              let uu____15912 =
                                ((Prims.op_Negation patterns_only) &&
                                   (FStar_Syntax_Util.is_function_typ t21))
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                                 in
                              (if uu____15912
                               then
                                 let uu____15913 = subterms args_lhs  in
                                 imitate' orig env wl1 uu____15913
                               else
                                 ((let uu____15918 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____15918
                                   then
                                     let uu____15919 =
                                       FStar_Syntax_Print.term_to_string t11
                                        in
                                     let uu____15920 = names_to_string fvs1
                                        in
                                     let uu____15921 = names_to_string fvs2
                                        in
                                     FStar_Util.print3
                                       "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                       uu____15919 uu____15920 uu____15921
                                   else ());
                                  use_pattern_equality orig env wl1 lhs1 vars
                                    t21))
                            else
                              if
                                ((Prims.op_Negation patterns_only) &&
                                   wl1.defer_ok)
                                  &&
                                  ((p_rel orig) <>
                                     FStar_TypeChecker_Common.EQ)
                              then
                                solve env
                                  (defer
                                     "flex pattern/rigid: occurs or freevar check"
                                     orig wl1)
                              else
                                (let uu____15925 =
                                   (Prims.op_Negation patterns_only) &&
                                     (check_head fvs1 t21)
                                    in
                                 if uu____15925
                                 then
                                   ((let uu____15927 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____15927
                                     then
                                       let uu____15928 =
                                         FStar_Syntax_Print.term_to_string
                                           t11
                                          in
                                       let uu____15929 = names_to_string fvs1
                                          in
                                       let uu____15930 = names_to_string fvs2
                                          in
                                       FStar_Util.print3
                                         "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                         uu____15928 uu____15929 uu____15930
                                     else ());
                                    (let uu____15932 = subterms args_lhs  in
                                     imitate_or_project
                                       (FStar_List.length args_lhs) lhs1 t21
                                       uu____15932))
                                 else
                                   giveup env
                                     "free-variable check failed on a non-redex"
                                     orig)))
                | FStar_Pervasives_Native.None  when patterns_only ->
                    giveup env "not a pattern" orig
                | FStar_Pervasives_Native.None  ->
                    if wl1.defer_ok
                    then solve env (defer "not a pattern" orig wl1)
                    else
                      (let uu____15943 =
                         let uu____15944 = FStar_Syntax_Free.names t1  in
                         check_head uu____15944 t2  in
                       if uu____15943
                       then
                         let n_args_lhs = FStar_List.length args_lhs  in
                         ((let uu____15955 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15955
                           then
                             let uu____15956 =
                               FStar_Syntax_Print.term_to_string t1  in
                             let uu____15957 =
                               FStar_Util.string_of_int n_args_lhs  in
                             FStar_Util.print2
                               "Not a pattern (%s) ... (lhs has %s args)\n"
                               uu____15956 uu____15957
                           else ());
                          (let uu____15965 = subterms args_lhs  in
                           pattern_eq_imitate_or_project n_args_lhs
                             (FStar_Pervasives_Native.fst lhs) t2 uu____15965))
                       else giveup env "head-symbol is free" orig))
            in
         let flex_flex1 orig lhs rhs =
           if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
           then solve env (defer "flex-flex deferred" orig wl)
           else
             (let solve_both_pats wl1 uu____16042 uu____16043 r =
                match (uu____16042, uu____16043) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____16241 =
                      (FStar_Syntax_Unionfind.equiv u1 u2) &&
                        (binders_eq xs ys)
                       in
                    if uu____16241
                    then
                      let uu____16242 =
                        solve_prob orig FStar_Pervasives_Native.None [] wl1
                         in
                      solve env uu____16242
                    else
                      (let xs1 = sn_binders env xs  in
                       let ys1 = sn_binders env ys  in
                       let zs = intersect_vars xs1 ys1  in
                       (let uu____16266 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____16266
                        then
                          let uu____16267 =
                            FStar_Syntax_Print.binders_to_string ", " xs1  in
                          let uu____16268 =
                            FStar_Syntax_Print.binders_to_string ", " ys1  in
                          let uu____16269 =
                            FStar_Syntax_Print.binders_to_string ", " zs  in
                          let uu____16270 =
                            FStar_Syntax_Print.term_to_string k1  in
                          let uu____16271 =
                            FStar_Syntax_Print.term_to_string k2  in
                          FStar_Util.print5
                            "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                            uu____16267 uu____16268 uu____16269 uu____16270
                            uu____16271
                        else ());
                       (let subst_k k xs2 args =
                          let xs_len = FStar_List.length xs2  in
                          let args_len = FStar_List.length args  in
                          if xs_len = args_len
                          then
                            let uu____16331 =
                              FStar_Syntax_Util.subst_of_list xs2 args  in
                            FStar_Syntax_Subst.subst uu____16331 k
                          else
                            if args_len < xs_len
                            then
                              (let uu____16345 =
                                 FStar_Util.first_N args_len xs2  in
                               match uu____16345 with
                               | (xs3,xs_rest) ->
                                   let k3 =
                                     let uu____16399 =
                                       FStar_Syntax_Syntax.mk_GTotal k  in
                                     FStar_Syntax_Util.arrow xs_rest
                                       uu____16399
                                      in
                                   let uu____16402 =
                                     FStar_Syntax_Util.subst_of_list xs3 args
                                      in
                                   FStar_Syntax_Subst.subst uu____16402 k3)
                            else
                              (let uu____16406 =
                                 let uu____16407 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 let uu____16408 =
                                   FStar_Syntax_Print.binders_to_string ", "
                                     xs2
                                    in
                                 let uu____16409 =
                                   FStar_Syntax_Print.args_to_string args  in
                                 FStar_Util.format3
                                   "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                   uu____16407 uu____16408 uu____16409
                                  in
                               failwith uu____16406)
                           in
                        let uu____16410 =
                          let uu____16417 =
                            let uu____16430 =
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1
                               in
                            FStar_Syntax_Util.arrow_formals uu____16430  in
                          match uu____16417 with
                          | (bs,k1') ->
                              let uu____16455 =
                                let uu____16468 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2
                                   in
                                FStar_Syntax_Util.arrow_formals uu____16468
                                 in
                              (match uu____16455 with
                               | (cs,k2') ->
                                   let k1'_xs = subst_k k1' bs args1  in
                                   let k2'_ys = subst_k k2' cs args2  in
                                   let sub_prob =
                                     let uu____16496 =
                                       let uu____16501 = p_scope orig  in
                                       mk_problem uu____16501 orig k1'_xs
                                         FStar_TypeChecker_Common.EQ k2'_ys
                                         FStar_Pervasives_Native.None
                                         "flex-flex kinding"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_63  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_63) uu____16496
                                      in
                                   let uu____16506 =
                                     let uu____16511 =
                                       let uu____16512 =
                                         FStar_Syntax_Subst.compress k1'  in
                                       uu____16512.FStar_Syntax_Syntax.n  in
                                     let uu____16515 =
                                       let uu____16516 =
                                         FStar_Syntax_Subst.compress k2'  in
                                       uu____16516.FStar_Syntax_Syntax.n  in
                                     (uu____16511, uu____16515)  in
                                   (match uu____16506 with
                                    | (FStar_Syntax_Syntax.Tm_type
                                       uu____16525,uu____16526) ->
                                        (k1'_xs, [sub_prob])
                                    | (uu____16529,FStar_Syntax_Syntax.Tm_type
                                       uu____16530) -> (k2'_ys, [sub_prob])
                                    | uu____16533 ->
                                        let uu____16538 =
                                          FStar_Syntax_Util.type_u ()  in
                                        (match uu____16538 with
                                         | (t,uu____16550) ->
                                             let uu____16551 =
                                               new_uvar r zs t  in
                                             (match uu____16551 with
                                              | (k_zs,uu____16563) ->
                                                  let kprob =
                                                    let uu____16565 =
                                                      let uu____16570 =
                                                        p_scope orig  in
                                                      mk_problem uu____16570
                                                        orig k1'_xs
                                                        FStar_TypeChecker_Common.EQ
                                                        k_zs
                                                        FStar_Pervasives_Native.None
                                                        "flex-flex kinding"
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _0_64  ->
                                                         FStar_TypeChecker_Common.TProb
                                                           _0_64) uu____16565
                                                     in
                                                  (k_zs, [sub_prob; kprob])))))
                           in
                        match uu____16410 with
                        | (k_u',sub_probs) ->
                            let uu____16583 =
                              let uu____16594 =
                                let uu____16595 = new_uvar r zs k_u'  in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____16595
                                 in
                              let uu____16604 =
                                let uu____16607 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow xs1 uu____16607  in
                              let uu____16610 =
                                let uu____16613 =
                                  FStar_Syntax_Syntax.mk_Total k_u'  in
                                FStar_Syntax_Util.arrow ys1 uu____16613  in
                              (uu____16594, uu____16604, uu____16610)  in
                            (match uu____16583 with
                             | (u_zs,knew1,knew2) ->
                                 let sub1 = u_abs knew1 xs1 u_zs  in
                                 let uu____16632 =
                                   occurs_check env wl1 (u1, k1) sub1  in
                                 (match uu____16632 with
                                  | (occurs_ok,msg) ->
                                      if Prims.op_Negation occurs_ok
                                      then
                                        giveup_or_defer1 orig
                                          "flex-flex: failed occcurs check"
                                      else
                                        (let sol1 = TERM ((u1, k1), sub1)  in
                                         let uu____16651 =
                                           FStar_Syntax_Unionfind.equiv u1 u2
                                            in
                                         if uu____16651
                                         then
                                           let wl2 =
                                             solve_prob orig
                                               FStar_Pervasives_Native.None
                                               [sol1] wl1
                                              in
                                           solve env wl2
                                         else
                                           (let sub2 = u_abs knew2 ys1 u_zs
                                               in
                                            let uu____16655 =
                                              occurs_check env wl1 (u2, k2)
                                                sub2
                                               in
                                            match uu____16655 with
                                            | (occurs_ok1,msg1) ->
                                                if
                                                  Prims.op_Negation
                                                    occurs_ok1
                                                then
                                                  giveup_or_defer1 orig
                                                    "flex-flex: failed occurs check"
                                                else
                                                  (let sol2 =
                                                     TERM ((u2, k2), sub2)
                                                      in
                                                   let wl2 =
                                                     solve_prob orig
                                                       FStar_Pervasives_Native.None
                                                       [sol1; sol2] wl1
                                                      in
                                                   solve env
                                                     (attempt sub_probs wl2))))))))
                 in
              let solve_one_pat uu____16708 uu____16709 =
                match (uu____16708, uu____16709) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____16827 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____16827
                      then
                        let uu____16828 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____16829 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.print2
                          "Trying flex-flex one pattern (%s) with %s\n"
                          uu____16828 uu____16829
                      else ());
                     (let uu____16831 = FStar_Syntax_Unionfind.equiv u1 u2
                         in
                      if uu____16831
                      then
                        let sub_probs =
                          FStar_List.map2
                            (fun uu____16850  ->
                               fun uu____16851  ->
                                 match (uu____16850, uu____16851) with
                                 | ((a,uu____16869),(t21,uu____16871)) ->
                                     let uu____16880 =
                                       let uu____16885 = p_scope orig  in
                                       let uu____16886 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_problem uu____16885 orig
                                         uu____16886
                                         FStar_TypeChecker_Common.EQ t21
                                         FStar_Pervasives_Native.None
                                         "flex-flex index"
                                        in
                                     FStar_All.pipe_right uu____16880
                                       (fun _0_65  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_65)) xs args2
                           in
                        let guard =
                          let uu____16892 =
                            FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p)
                                   FStar_Pervasives_Native.fst) sub_probs
                             in
                          FStar_Syntax_Util.mk_conj_l uu____16892  in
                        let wl1 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl
                           in
                        solve env (attempt sub_probs wl1)
                      else
                        (let t21 = sn env t2  in
                         let rhs_vars = FStar_Syntax_Free.names t21  in
                         let uu____16907 = occurs_check env wl (u1, k1) t21
                            in
                         match uu____16907 with
                         | (occurs_ok,uu____16915) ->
                             let lhs_vars =
                               FStar_Syntax_Free.names_of_binders xs  in
                             let uu____16923 =
                               occurs_ok &&
                                 (FStar_Util.set_is_subset_of rhs_vars
                                    lhs_vars)
                                in
                             if uu____16923
                             then
                               let sol =
                                 let uu____16925 =
                                   let uu____16934 = u_abs k1 xs t21  in
                                   ((u1, k1), uu____16934)  in
                                 TERM uu____16925  in
                               let wl1 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [sol] wl
                                  in
                               solve env wl1
                             else
                               (let uu____16941 =
                                  occurs_ok &&
                                    (FStar_All.pipe_left Prims.op_Negation
                                       wl.defer_ok)
                                   in
                                if uu____16941
                                then
                                  let uu____16942 =
                                    force_quasi_pattern
                                      (FStar_Pervasives_Native.Some xs)
                                      (t21, u2, k2, args2)
                                     in
                                  match uu____16942 with
                                  | FStar_Pervasives_Native.None  ->
                                      giveup_or_defer1 orig
                                        "flex-flex constraint"
                                  | FStar_Pervasives_Native.Some
                                      (sol,(uu____16966,u21,k21,ys)) ->
                                      let wl1 =
                                        extend_solution (p_pid orig) [sol] wl
                                         in
                                      ((let uu____16992 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other
                                               "QuasiPattern")
                                           in
                                        if uu____16992
                                        then
                                          let uu____16993 =
                                            uvi_to_string env sol  in
                                          FStar_Util.print1
                                            "flex-flex quasi pattern (2): %s\n"
                                            uu____16993
                                        else ());
                                       (match orig with
                                        | FStar_TypeChecker_Common.TProb p ->
                                            solve_t env p wl1
                                        | uu____17000 ->
                                            giveup env "impossible" orig))
                                else
                                  giveup_or_defer1 orig
                                    "flex-flex constraint"))))
                 in
              let uu____17002 = lhs  in
              match uu____17002 with
              | (t1,u1,k1,args1) ->
                  let uu____17007 = rhs  in
                  (match uu____17007 with
                   | (t2,u2,k2,args2) ->
                       let maybe_pat_vars1 = pat_vars env [] args1  in
                       let maybe_pat_vars2 = pat_vars env [] args2  in
                       let r = t2.FStar_Syntax_Syntax.pos  in
                       (match (maybe_pat_vars1, maybe_pat_vars2) with
                        | (FStar_Pervasives_Native.Some
                           xs,FStar_Pervasives_Native.Some ys) ->
                            solve_both_pats wl (u1, k1, xs, args1)
                              (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos
                        | (FStar_Pervasives_Native.Some
                           xs,FStar_Pervasives_Native.None ) ->
                            solve_one_pat (t1, u1, k1, xs) rhs
                        | (FStar_Pervasives_Native.None
                           ,FStar_Pervasives_Native.Some ys) ->
                            solve_one_pat (t2, u2, k2, ys) lhs
                        | uu____17047 ->
                            if wl.defer_ok
                            then
                              giveup_or_defer1 orig
                                "flex-flex: neither side is a pattern"
                            else
                              (let uu____17057 =
                                 force_quasi_pattern
                                   FStar_Pervasives_Native.None
                                   (t1, u1, k1, args1)
                                  in
                               match uu____17057 with
                               | FStar_Pervasives_Native.None  ->
                                   giveup env
                                     "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                     orig
                               | FStar_Pervasives_Native.Some
                                   (sol,uu____17075) ->
                                   let wl1 =
                                     extend_solution (p_pid orig) [sol] wl
                                      in
                                   ((let uu____17082 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "QuasiPattern")
                                        in
                                     if uu____17082
                                     then
                                       let uu____17083 =
                                         uvi_to_string env sol  in
                                       FStar_Util.print1
                                         "flex-flex quasi pattern (1): %s\n"
                                         uu____17083
                                     else ());
                                    (match orig with
                                     | FStar_TypeChecker_Common.TProb p ->
                                         solve_t env p wl1
                                     | uu____17090 ->
                                         giveup env "impossible" orig))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____17093 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____17093
          then
            let uu____17094 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____17094
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             let uu____17098 = FStar_Util.physical_equality t1 t2  in
             if uu____17098
             then
               let uu____17099 =
                 solve_prob orig FStar_Pervasives_Native.None [] wl  in
               solve env uu____17099
             else
               ((let uu____17102 =
                   FStar_TypeChecker_Env.debug env
                     (FStar_Options.Other "RelCheck")
                    in
                 if uu____17102
                 then
                   let uu____17103 =
                     FStar_Util.string_of_int
                       problem.FStar_TypeChecker_Common.pid
                      in
                   let uu____17104 = FStar_Syntax_Print.tag_of_term t1  in
                   let uu____17105 = FStar_Syntax_Print.tag_of_term t2  in
                   FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____17103
                     uu____17104 uu____17105
                 else ());
                (let r = FStar_TypeChecker_Env.get_range env  in
                 let not_quote t =
                   let uu____17112 =
                     let uu____17113 = FStar_Syntax_Subst.compress t  in
                     uu____17113.FStar_Syntax_Syntax.n  in
                   match uu____17112 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu____17116,FStar_Syntax_Syntax.Meta_quoted
                        uu____17117)
                       -> false
                   | uu____17128 -> true  in
                 match ((t1.FStar_Syntax_Syntax.n),
                         (t2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.Tm_delayed uu____17129,uu____17130)
                     -> failwith "Impossible: terms were not compressed"
                 | (uu____17155,FStar_Syntax_Syntax.Tm_delayed uu____17156)
                     -> failwith "Impossible: terms were not compressed"
                 | (FStar_Syntax_Syntax.Tm_ascribed uu____17181,uu____17182)
                     ->
                     let uu____17209 =
                       let uu___148_17210 = problem  in
                       let uu____17211 = FStar_Syntax_Util.unascribe t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___148_17210.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____17211;
                         FStar_TypeChecker_Common.relation =
                           (uu___148_17210.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___148_17210.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___148_17210.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___148_17210.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___148_17210.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___148_17210.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___148_17210.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___148_17210.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17209 wl
                 | (FStar_Syntax_Syntax.Tm_meta uu____17212,uu____17213) when
                     not_quote t1 ->
                     let uu____17220 =
                       let uu___149_17221 = problem  in
                       let uu____17222 = FStar_Syntax_Util.unmeta t1  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___149_17221.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____17222;
                         FStar_TypeChecker_Common.relation =
                           (uu___149_17221.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___149_17221.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___149_17221.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___149_17221.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___149_17221.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___149_17221.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___149_17221.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___149_17221.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17220 wl
                 | (uu____17223,FStar_Syntax_Syntax.Tm_ascribed uu____17224)
                     ->
                     let uu____17251 =
                       let uu___150_17252 = problem  in
                       let uu____17253 = FStar_Syntax_Util.unascribe t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___150_17252.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___150_17252.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___150_17252.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17253;
                         FStar_TypeChecker_Common.element =
                           (uu___150_17252.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___150_17252.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___150_17252.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___150_17252.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___150_17252.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___150_17252.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17251 wl
                 | (uu____17254,FStar_Syntax_Syntax.Tm_meta uu____17255) when
                     not_quote t2 ->
                     let uu____17262 =
                       let uu___151_17263 = problem  in
                       let uu____17264 = FStar_Syntax_Util.unmeta t2  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___151_17263.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___151_17263.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___151_17263.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____17264;
                         FStar_TypeChecker_Common.element =
                           (uu___151_17263.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___151_17263.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___151_17263.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___151_17263.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___151_17263.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___151_17263.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_t' env uu____17262 wl
                 | (FStar_Syntax_Syntax.Tm_meta
                    (uu____17265,FStar_Syntax_Syntax.Meta_quoted
                     (t11,uu____17267)),FStar_Syntax_Syntax.Tm_meta
                    (uu____17268,FStar_Syntax_Syntax.Meta_quoted
                     (t21,uu____17270))) ->
                     let uu____17287 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____17287
                 | (FStar_Syntax_Syntax.Tm_bvar uu____17288,uu____17289) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (uu____17290,FStar_Syntax_Syntax.Tm_bvar uu____17291) ->
                     failwith
                       "Only locally nameless! We should never see a de Bruijn variable"
                 | (FStar_Syntax_Syntax.Tm_type
                    u1,FStar_Syntax_Syntax.Tm_type u2) ->
                     solve_one_universe_eq env orig u1 u2 wl
                 | (FStar_Syntax_Syntax.Tm_arrow
                    (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                     let mk_c c uu___112_17346 =
                       match uu___112_17346 with
                       | [] -> c
                       | bs ->
                           let uu____17368 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                               FStar_Pervasives_Native.None
                               c.FStar_Syntax_Syntax.pos
                              in
                           FStar_Syntax_Syntax.mk_Total uu____17368
                        in
                     let uu____17377 =
                       match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                        in
                     (match uu____17377 with
                      | ((bs11,c11),(bs21,c21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let c12 =
                                     FStar_Syntax_Subst.subst_comp subst1 c11
                                      in
                                   let c22 =
                                     FStar_Syntax_Subst.subst_comp subst1 c21
                                      in
                                   let rel =
                                     let uu____17519 =
                                       FStar_Options.use_eq_at_higher_order
                                         ()
                                        in
                                     if uu____17519
                                     then FStar_TypeChecker_Common.EQ
                                     else
                                       problem.FStar_TypeChecker_Common.relation
                                      in
                                   let uu____17521 =
                                     mk_problem scope orig c12 rel c22
                                       FStar_Pervasives_Native.None
                                       "function co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_66  ->
                                        FStar_TypeChecker_Common.CProb _0_66)
                                     uu____17521))
                 | (FStar_Syntax_Syntax.Tm_abs
                    (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                    (bs2,tbody2,lopt2)) ->
                     let mk_t t l uu___113_17597 =
                       match uu___113_17597 with
                       | [] -> t
                       | bs ->
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                        in
                     let uu____17631 =
                       match_num_binders (bs1, (mk_t tbody1 lopt1))
                         (bs2, (mk_t tbody2 lopt2))
                        in
                     (match uu____17631 with
                      | ((bs11,tbody11),(bs21,tbody21)) ->
                          solve_binders env bs11 bs21 orig wl
                            (fun scope  ->
                               fun env1  ->
                                 fun subst1  ->
                                   let uu____17767 =
                                     let uu____17772 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody11
                                        in
                                     let uu____17773 =
                                       FStar_Syntax_Subst.subst subst1
                                         tbody21
                                        in
                                     mk_problem scope orig uu____17772
                                       problem.FStar_TypeChecker_Common.relation
                                       uu____17773
                                       FStar_Pervasives_Native.None
                                       "lambda co-domain"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_67  ->
                                        FStar_TypeChecker_Common.TProb _0_67)
                                     uu____17767))
                 | (FStar_Syntax_Syntax.Tm_abs uu____17778,uu____17779) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____17804 -> true
                       | uu____17821 -> false  in
                     let maybe_eta t =
                       if is_abs t
                       then FStar_Util.Inl t
                       else
                         (let t3 =
                            FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                             in
                          if is_abs t3
                          then FStar_Util.Inl t3
                          else FStar_Util.Inr t3)
                        in
                     let force_eta t =
                       if is_abs t
                       then t
                       else
                         (let uu____17868 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___152_17876 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___152_17876.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___152_17876.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___152_17876.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___152_17876.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___152_17876.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___152_17876.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___152_17876.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___152_17876.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___152_17876.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___152_17876.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___152_17876.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___152_17876.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___152_17876.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___152_17876.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___152_17876.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___152_17876.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___152_17876.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___152_17876.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___152_17876.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___152_17876.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___152_17876.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___152_17876.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___152_17876.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___152_17876.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___152_17876.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___152_17876.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___152_17876.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___152_17876.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___152_17876.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___152_17876.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___152_17876.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___152_17876.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___152_17876.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____17868 with
                          | (uu____17879,ty,uu____17881) ->
                              let uu____17882 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____17882)
                        in
                     let uu____17883 =
                       let uu____17900 = maybe_eta t1  in
                       let uu____17907 = maybe_eta t2  in
                       (uu____17900, uu____17907)  in
                     (match uu____17883 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___153_17949 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___153_17949.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___153_17949.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___153_17949.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___153_17949.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___153_17949.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___153_17949.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___153_17949.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___153_17949.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____17972 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____17972
                          then
                            let uu____17973 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____17973 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_17988 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_17988.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_17988.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_17988.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_17988.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_17988.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_17988.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_17988.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_17988.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____18012 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18012
                          then
                            let uu____18013 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18013 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_18028 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_18028.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_18028.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_18028.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_18028.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_18028.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_18028.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_18028.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_18028.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____18032 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (uu____18049,FStar_Syntax_Syntax.Tm_abs uu____18050) ->
                     let is_abs t =
                       match t.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_abs uu____18075 -> true
                       | uu____18092 -> false  in
                     let maybe_eta t =
                       if is_abs t
                       then FStar_Util.Inl t
                       else
                         (let t3 =
                            FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                             in
                          if is_abs t3
                          then FStar_Util.Inl t3
                          else FStar_Util.Inr t3)
                        in
                     let force_eta t =
                       if is_abs t
                       then t
                       else
                         (let uu____18139 =
                            env.FStar_TypeChecker_Env.type_of
                              (let uu___152_18147 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___152_18147.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___152_18147.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___152_18147.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___152_18147.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___152_18147.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___152_18147.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   FStar_Pervasives_Native.None;
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___152_18147.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___152_18147.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___152_18147.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___152_18147.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___152_18147.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___152_18147.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___152_18147.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___152_18147.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___152_18147.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___152_18147.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___152_18147.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___152_18147.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___152_18147.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___152_18147.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___152_18147.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___152_18147.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___152_18147.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___152_18147.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___152_18147.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___152_18147.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___152_18147.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___152_18147.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___152_18147.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___152_18147.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___152_18147.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___152_18147.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___152_18147.FStar_TypeChecker_Env.dep_graph)
                               }) t
                             in
                          match uu____18139 with
                          | (uu____18150,ty,uu____18152) ->
                              let uu____18153 =
                                FStar_TypeChecker_Normalize.unfold_whnf env
                                  ty
                                 in
                              FStar_TypeChecker_Normalize.eta_expand_with_type
                                env t uu____18153)
                        in
                     let uu____18154 =
                       let uu____18171 = maybe_eta t1  in
                       let uu____18178 = maybe_eta t2  in
                       (uu____18171, uu____18178)  in
                     (match uu____18154 with
                      | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                          solve_t env
                            (let uu___153_18220 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___153_18220.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t11;
                               FStar_TypeChecker_Common.relation =
                                 (uu___153_18220.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs = t21;
                               FStar_TypeChecker_Common.element =
                                 (uu___153_18220.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___153_18220.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___153_18220.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___153_18220.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___153_18220.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___153_18220.FStar_TypeChecker_Common.rank)
                             }) wl
                      | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                          let uu____18243 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18243
                          then
                            let uu____18244 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18244 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_18259 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_18259.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_18259.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_18259.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_18259.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_18259.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_18259.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_18259.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_18259.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                          let uu____18283 =
                            (is_flex not_abs) &&
                              ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                             in
                          if uu____18283
                          then
                            let uu____18284 =
                              destruct_flex_pattern env not_abs  in
                            solve_t_flex_rigid true orig uu____18284 t_abs wl
                          else
                            (let t11 = force_eta t1  in
                             let t21 = force_eta t2  in
                             if (is_abs t11) && (is_abs t21)
                             then
                               solve_t env
                                 (let uu___154_18299 = problem  in
                                  {
                                    FStar_TypeChecker_Common.pid =
                                      (uu___154_18299.FStar_TypeChecker_Common.pid);
                                    FStar_TypeChecker_Common.lhs = t11;
                                    FStar_TypeChecker_Common.relation =
                                      (uu___154_18299.FStar_TypeChecker_Common.relation);
                                    FStar_TypeChecker_Common.rhs = t21;
                                    FStar_TypeChecker_Common.element =
                                      (uu___154_18299.FStar_TypeChecker_Common.element);
                                    FStar_TypeChecker_Common.logical_guard =
                                      (uu___154_18299.FStar_TypeChecker_Common.logical_guard);
                                    FStar_TypeChecker_Common.scope =
                                      (uu___154_18299.FStar_TypeChecker_Common.scope);
                                    FStar_TypeChecker_Common.reason =
                                      (uu___154_18299.FStar_TypeChecker_Common.reason);
                                    FStar_TypeChecker_Common.loc =
                                      (uu___154_18299.FStar_TypeChecker_Common.loc);
                                    FStar_TypeChecker_Common.rank =
                                      (uu___154_18299.FStar_TypeChecker_Common.rank)
                                  }) wl
                             else
                               giveup env
                                 "head tag mismatch: RHS is an abstraction"
                                 orig)
                      | uu____18303 ->
                          failwith
                            "Impossible: at least one side is an abstraction")
                 | (FStar_Syntax_Syntax.Tm_refine
                    (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                     let should_delta =
                       ((let uu____18335 = FStar_Syntax_Free.uvars t1  in
                         FStar_Util.set_is_empty uu____18335) &&
                          (let uu____18347 = FStar_Syntax_Free.uvars t2  in
                           FStar_Util.set_is_empty uu____18347))
                         &&
                         (let uu____18362 =
                            head_matches env x1.FStar_Syntax_Syntax.sort
                              x2.FStar_Syntax_Syntax.sort
                             in
                          match uu____18362 with
                          | MisMatch
                              (FStar_Pervasives_Native.Some
                               d1,FStar_Pervasives_Native.Some d2)
                              ->
                              let is_unfoldable uu___114_18372 =
                                match uu___114_18372 with
                                | FStar_Syntax_Syntax.Delta_constant  -> true
                                | FStar_Syntax_Syntax.Delta_defined_at_level
                                    uu____18373 -> true
                                | uu____18374 -> false  in
                              (is_unfoldable d1) && (is_unfoldable d2)
                          | uu____18375 -> false)
                        in
                     let uu____18376 = as_refinement should_delta env wl t1
                        in
                     (match uu____18376 with
                      | (x11,phi1) ->
                          let uu____18383 =
                            as_refinement should_delta env wl t2  in
                          (match uu____18383 with
                           | (x21,phi21) ->
                               let base_prob =
                                 let uu____18391 =
                                   let uu____18396 = p_scope orig  in
                                   mk_problem uu____18396 orig
                                     x11.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.relation
                                     x21.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "refinement base type"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.TProb _0_68)
                                   uu____18391
                                  in
                               let x12 = FStar_Syntax_Syntax.freshen_bv x11
                                  in
                               let subst1 =
                                 [FStar_Syntax_Syntax.DB
                                    ((Prims.parse_int "0"), x12)]
                                  in
                               let phi11 =
                                 FStar_Syntax_Subst.subst subst1 phi1  in
                               let phi22 =
                                 FStar_Syntax_Subst.subst subst1 phi21  in
                               let env1 =
                                 FStar_TypeChecker_Env.push_bv env x12  in
                               let mk_imp1 imp phi12 phi23 =
                                 let uu____18430 = imp phi12 phi23  in
                                 FStar_All.pipe_right uu____18430
                                   (guard_on_element wl problem x12)
                                  in
                               let fallback uu____18434 =
                                 let impl =
                                   if
                                     problem.FStar_TypeChecker_Common.relation
                                       = FStar_TypeChecker_Common.EQ
                                   then
                                     mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                       phi22
                                   else
                                     mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                       phi22
                                    in
                                 let guard =
                                   let uu____18440 =
                                     FStar_All.pipe_right (p_guard base_prob)
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_Syntax_Util.mk_conj uu____18440 impl
                                    in
                                 let wl1 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl
                                    in
                                 solve env1 (attempt [base_prob] wl1)  in
                               if
                                 problem.FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ
                               then
                                 let ref_prob =
                                   let uu____18449 =
                                     let uu____18454 =
                                       let uu____18455 = p_scope orig  in
                                       let uu____18462 =
                                         let uu____18469 =
                                           FStar_Syntax_Syntax.mk_binder x12
                                            in
                                         [uu____18469]  in
                                       FStar_List.append uu____18455
                                         uu____18462
                                        in
                                     mk_problem uu____18454 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_69  ->
                                        FStar_TypeChecker_Common.TProb _0_69)
                                     uu____18449
                                    in
                                 let uu____18478 =
                                   solve env1
                                     (let uu___155_18480 = wl  in
                                      {
                                        attempting = [ref_prob];
                                        wl_deferred = [];
                                        ctr = (uu___155_18480.ctr);
                                        defer_ok = false;
                                        smt_ok = (uu___155_18480.smt_ok);
                                        tcenv = (uu___155_18480.tcenv)
                                      })
                                    in
                                 (match uu____18478 with
                                  | Failed uu____18487 -> fallback ()
                                  | Success uu____18492 ->
                                      let guard =
                                        let uu____18496 =
                                          FStar_All.pipe_right
                                            (p_guard base_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        let uu____18501 =
                                          let uu____18502 =
                                            FStar_All.pipe_right
                                              (p_guard ref_prob)
                                              FStar_Pervasives_Native.fst
                                             in
                                          FStar_All.pipe_right uu____18502
                                            (guard_on_element wl problem x12)
                                           in
                                        FStar_Syntax_Util.mk_conj uu____18496
                                          uu____18501
                                         in
                                      let wl1 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl
                                         in
                                      let wl2 =
                                        let uu___156_18511 = wl1  in
                                        {
                                          attempting =
                                            (uu___156_18511.attempting);
                                          wl_deferred =
                                            (uu___156_18511.wl_deferred);
                                          ctr =
                                            (wl1.ctr + (Prims.parse_int "1"));
                                          defer_ok =
                                            (uu___156_18511.defer_ok);
                                          smt_ok = (uu___156_18511.smt_ok);
                                          tcenv = (uu___156_18511.tcenv)
                                        }  in
                                      solve env1 (attempt [base_prob] wl2))
                               else fallback ()))
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18513,FStar_Syntax_Syntax.Tm_uvar uu____18514) ->
                     let uu____18547 = destruct_flex_t t1  in
                     let uu____18548 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18547 uu____18548
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18549;
                       FStar_Syntax_Syntax.pos = uu____18550;
                       FStar_Syntax_Syntax.vars = uu____18551;_},uu____18552),FStar_Syntax_Syntax.Tm_uvar
                    uu____18553) ->
                     let uu____18610 = destruct_flex_t t1  in
                     let uu____18611 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18610 uu____18611
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18612,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18613;
                       FStar_Syntax_Syntax.pos = uu____18614;
                       FStar_Syntax_Syntax.vars = uu____18615;_},uu____18616))
                     ->
                     let uu____18673 = destruct_flex_t t1  in
                     let uu____18674 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18673 uu____18674
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18675;
                       FStar_Syntax_Syntax.pos = uu____18676;
                       FStar_Syntax_Syntax.vars = uu____18677;_},uu____18678),FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18679;
                       FStar_Syntax_Syntax.pos = uu____18680;
                       FStar_Syntax_Syntax.vars = uu____18681;_},uu____18682))
                     ->
                     let uu____18763 = destruct_flex_t t1  in
                     let uu____18764 = destruct_flex_t t2  in
                     flex_flex1 orig uu____18763 uu____18764
                 | (FStar_Syntax_Syntax.Tm_uvar uu____18765,uu____18766) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18783 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____18783 t2 wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18790;
                       FStar_Syntax_Syntax.pos = uu____18791;
                       FStar_Syntax_Syntax.vars = uu____18792;_},uu____18793),uu____18794)
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     ->
                     let uu____18835 = destruct_flex_pattern env t1  in
                     solve_t_flex_rigid false orig uu____18835 t2 wl
                 | (uu____18842,FStar_Syntax_Syntax.Tm_uvar uu____18843) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (uu____18860,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18861;
                       FStar_Syntax_Syntax.pos = uu____18862;
                       FStar_Syntax_Syntax.vars = uu____18863;_},uu____18864))
                     when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.EQ
                     -> solve_t env (invert problem) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18905,FStar_Syntax_Syntax.Tm_type uu____18906) ->
                     solve_t' env
                       (let uu___157_18924 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18924.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18924.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18924.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18924.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18924.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18924.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18924.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18924.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18924.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____18925;
                       FStar_Syntax_Syntax.pos = uu____18926;
                       FStar_Syntax_Syntax.vars = uu____18927;_},uu____18928),FStar_Syntax_Syntax.Tm_type
                    uu____18929) ->
                     solve_t' env
                       (let uu___157_18971 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_18971.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_18971.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_18971.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_18971.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_18971.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_18971.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_18971.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_18971.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_18971.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar
                    uu____18972,FStar_Syntax_Syntax.Tm_arrow uu____18973) ->
                     solve_t' env
                       (let uu___157_19003 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_19003.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_19003.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_19003.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_19003.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_19003.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_19003.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_19003.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_19003.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_19003.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19004;
                       FStar_Syntax_Syntax.pos = uu____19005;
                       FStar_Syntax_Syntax.vars = uu____19006;_},uu____19007),FStar_Syntax_Syntax.Tm_arrow
                    uu____19008) ->
                     solve_t' env
                       (let uu___157_19062 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___157_19062.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___157_19062.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ;
                          FStar_TypeChecker_Common.rhs =
                            (uu___157_19062.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___157_19062.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___157_19062.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___157_19062.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___157_19062.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___157_19062.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___157_19062.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_uvar uu____19063,uu____19064) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____19083 =
                          let uu____19084 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____19084
                           in
                        if uu____19083
                        then
                          let uu____19085 =
                            FStar_All.pipe_left
                              (fun _0_70  ->
                                 FStar_TypeChecker_Common.TProb _0_70)
                              (let uu___158_19091 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_19091.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___158_19091.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___158_19091.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_19091.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_19091.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___158_19091.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_19091.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_19091.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_19091.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____19092 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____19085 uu____19092 t2
                            wl
                        else
                          (let uu____19100 = base_and_refinement env t2  in
                           match uu____19100 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19129 =
                                      FStar_All.pipe_left
                                        (fun _0_71  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_71)
                                        (let uu___159_19135 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___159_19135.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___159_19135.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___159_19135.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___159_19135.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___159_19135.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___159_19135.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___159_19135.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___159_19135.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___159_19135.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____19136 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____19129
                                      uu____19136 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___160_19150 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___160_19150.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___160_19150.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____19153 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type"
                                         in
                                      FStar_All.pipe_left
                                        (fun _0_72  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_72) uu____19153
                                       in
                                    let guard =
                                      let uu____19165 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____19165
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19173;
                       FStar_Syntax_Syntax.pos = uu____19174;
                       FStar_Syntax_Syntax.vars = uu____19175;_},uu____19176),uu____19177)
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "flex-rigid subtyping deferred" orig wl)
                     else
                       (let new_rel =
                          problem.FStar_TypeChecker_Common.relation  in
                        let uu____19220 =
                          let uu____19221 = is_top_level_prob orig  in
                          FStar_All.pipe_left Prims.op_Negation uu____19221
                           in
                        if uu____19220
                        then
                          let uu____19222 =
                            FStar_All.pipe_left
                              (fun _0_73  ->
                                 FStar_TypeChecker_Common.TProb _0_73)
                              (let uu___158_19228 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_19228.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___158_19228.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation = new_rel;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___158_19228.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_19228.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_19228.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___158_19228.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_19228.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_19228.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_19228.FStar_TypeChecker_Common.rank)
                               })
                             in
                          let uu____19229 = destruct_flex_pattern env t1  in
                          solve_t_flex_rigid false uu____19222 uu____19229 t2
                            wl
                        else
                          (let uu____19237 = base_and_refinement env t2  in
                           match uu____19237 with
                           | (t_base,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____19266 =
                                      FStar_All.pipe_left
                                        (fun _0_74  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_74)
                                        (let uu___159_19272 = problem  in
                                         {
                                           FStar_TypeChecker_Common.pid =
                                             (uu___159_19272.FStar_TypeChecker_Common.pid);
                                           FStar_TypeChecker_Common.lhs =
                                             (uu___159_19272.FStar_TypeChecker_Common.lhs);
                                           FStar_TypeChecker_Common.relation
                                             = new_rel;
                                           FStar_TypeChecker_Common.rhs =
                                             (uu___159_19272.FStar_TypeChecker_Common.rhs);
                                           FStar_TypeChecker_Common.element =
                                             (uu___159_19272.FStar_TypeChecker_Common.element);
                                           FStar_TypeChecker_Common.logical_guard
                                             =
                                             (uu___159_19272.FStar_TypeChecker_Common.logical_guard);
                                           FStar_TypeChecker_Common.scope =
                                             (uu___159_19272.FStar_TypeChecker_Common.scope);
                                           FStar_TypeChecker_Common.reason =
                                             (uu___159_19272.FStar_TypeChecker_Common.reason);
                                           FStar_TypeChecker_Common.loc =
                                             (uu___159_19272.FStar_TypeChecker_Common.loc);
                                           FStar_TypeChecker_Common.rank =
                                             (uu___159_19272.FStar_TypeChecker_Common.rank)
                                         })
                                       in
                                    let uu____19273 =
                                      destruct_flex_pattern env t1  in
                                    solve_t_flex_rigid false uu____19266
                                      uu____19273 t_base wl
                                | FStar_Pervasives_Native.Some (y,phi) ->
                                    let y' =
                                      let uu___160_19287 = y  in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___160_19287.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___160_19287.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = t1
                                      }  in
                                    let impl =
                                      guard_on_element wl problem y' phi  in
                                    let base_prob =
                                      let uu____19290 =
                                        mk_problem
                                          problem.FStar_TypeChecker_Common.scope
                                          orig t1 new_rel
                                          y.FStar_Syntax_Syntax.sort
                                          problem.FStar_TypeChecker_Common.element
                                          "flex-rigid: base type"
                                         in
                                      FStar_All.pipe_left
                                        (fun _0_75  ->
                                           FStar_TypeChecker_Common.TProb
                                             _0_75) uu____19290
                                       in
                                    let guard =
                                      let uu____19302 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_Syntax_Util.mk_conj uu____19302
                                        impl
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    solve env (attempt [base_prob] wl1))))
                 | (uu____19310,FStar_Syntax_Syntax.Tm_uvar uu____19311) ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19329 = base_and_refinement env t1  in
                        match uu____19329 with
                        | (t_base,uu____19341) ->
                            solve_t env
                              (let uu___161_19355 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___161_19355.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___161_19355.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___161_19355.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___161_19355.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___161_19355.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___161_19355.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___161_19355.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___161_19355.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (uu____19356,FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____19357;
                       FStar_Syntax_Syntax.pos = uu____19358;
                       FStar_Syntax_Syntax.vars = uu____19359;_},uu____19360))
                     ->
                     if wl.defer_ok
                     then
                       solve env
                         (defer "rigid-flex subtyping deferred" orig wl)
                     else
                       (let uu____19402 = base_and_refinement env t1  in
                        match uu____19402 with
                        | (t_base,uu____19414) ->
                            solve_t env
                              (let uu___161_19428 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___161_19428.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t_base;
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___161_19428.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___161_19428.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___161_19428.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___161_19428.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___161_19428.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___161_19428.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___161_19428.FStar_TypeChecker_Common.rank)
                               }) wl)
                 | (FStar_Syntax_Syntax.Tm_refine uu____19429,uu____19430) ->
                     let t21 =
                       let uu____19440 = base_and_refinement env t2  in
                       FStar_All.pipe_left force_refinement uu____19440  in
                     solve_t env
                       (let uu___162_19464 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___162_19464.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs =
                            (uu___162_19464.FStar_TypeChecker_Common.lhs);
                          FStar_TypeChecker_Common.relation =
                            (uu___162_19464.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___162_19464.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___162_19464.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___162_19464.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___162_19464.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___162_19464.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___162_19464.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (uu____19465,FStar_Syntax_Syntax.Tm_refine uu____19466) ->
                     let t11 =
                       let uu____19476 = base_and_refinement env t1  in
                       FStar_All.pipe_left force_refinement uu____19476  in
                     solve_t env
                       (let uu___163_19500 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___163_19500.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___163_19500.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs =
                            (uu___163_19500.FStar_TypeChecker_Common.rhs);
                          FStar_TypeChecker_Common.element =
                            (uu___163_19500.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___163_19500.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.scope =
                            (uu___163_19500.FStar_TypeChecker_Common.scope);
                          FStar_TypeChecker_Common.reason =
                            (uu___163_19500.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___163_19500.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___163_19500.FStar_TypeChecker_Common.rank)
                        }) wl
                 | (FStar_Syntax_Syntax.Tm_match uu____19503,uu____19504) ->
                     let head1 =
                       let uu____19530 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19530
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19574 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19574
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19616 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19616
                       then
                         let uu____19617 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19618 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19619 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19617 uu____19618 uu____19619
                       else ());
                      (let uu____19621 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19621
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19636 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19636
                          then
                            let guard =
                              let uu____19648 =
                                let uu____19649 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19649 = FStar_Syntax_Util.Equal  in
                              if uu____19648
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19653 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_76  ->
                                      FStar_Pervasives_Native.Some _0_76)
                                   uu____19653)
                               in
                            let uu____19656 = solve_prob orig guard [] wl  in
                            solve env uu____19656
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_uinst uu____19659,uu____19660) ->
                     let head1 =
                       let uu____19670 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19670
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19714 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19714
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19756 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19756
                       then
                         let uu____19757 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19758 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19759 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19757 uu____19758 uu____19759
                       else ());
                      (let uu____19761 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19761
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19776 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19776
                          then
                            let guard =
                              let uu____19788 =
                                let uu____19789 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19789 = FStar_Syntax_Util.Equal  in
                              if uu____19788
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19793 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_77  ->
                                      FStar_Pervasives_Native.Some _0_77)
                                   uu____19793)
                               in
                            let uu____19796 = solve_prob orig guard [] wl  in
                            solve env uu____19796
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_name uu____19799,uu____19800) ->
                     let head1 =
                       let uu____19804 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19804
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19848 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19848
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____19890 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____19890
                       then
                         let uu____19891 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____19892 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____19893 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____19891 uu____19892 uu____19893
                       else ());
                      (let uu____19895 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19895
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____19910 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____19910
                          then
                            let guard =
                              let uu____19922 =
                                let uu____19923 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____19923 = FStar_Syntax_Util.Equal  in
                              if uu____19922
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____19927 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_78  ->
                                      FStar_Pervasives_Native.Some _0_78)
                                   uu____19927)
                               in
                            let uu____19930 = solve_prob orig guard [] wl  in
                            solve env uu____19930
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_constant uu____19933,uu____19934)
                     ->
                     let head1 =
                       let uu____19938 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____19938
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____19982 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____19982
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20024 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20024
                       then
                         let uu____20025 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20026 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20027 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20025 uu____20026 uu____20027
                       else ());
                      (let uu____20029 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20029
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20044 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20044
                          then
                            let guard =
                              let uu____20056 =
                                let uu____20057 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20057 = FStar_Syntax_Util.Equal  in
                              if uu____20056
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20061 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_79  ->
                                      FStar_Pervasives_Native.Some _0_79)
                                   uu____20061)
                               in
                            let uu____20064 = solve_prob orig guard [] wl  in
                            solve env uu____20064
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_fvar uu____20067,uu____20068) ->
                     let head1 =
                       let uu____20072 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20072
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20116 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20116
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20158 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20158
                       then
                         let uu____20159 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20160 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20161 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20159 uu____20160 uu____20161
                       else ());
                      (let uu____20163 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20163
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20178 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20178
                          then
                            let guard =
                              let uu____20190 =
                                let uu____20191 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20191 = FStar_Syntax_Util.Equal  in
                              if uu____20190
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20195 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_80  ->
                                      FStar_Pervasives_Native.Some _0_80)
                                   uu____20195)
                               in
                            let uu____20198 = solve_prob orig guard [] wl  in
                            solve env uu____20198
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_app uu____20201,uu____20202) ->
                     let head1 =
                       let uu____20220 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20220
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20264 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20264
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20306 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20306
                       then
                         let uu____20307 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20308 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20309 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20307 uu____20308 uu____20309
                       else ());
                      (let uu____20311 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20311
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20326 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20326
                          then
                            let guard =
                              let uu____20338 =
                                let uu____20339 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20339 = FStar_Syntax_Util.Equal  in
                              if uu____20338
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20343 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_81  ->
                                      FStar_Pervasives_Native.Some _0_81)
                                   uu____20343)
                               in
                            let uu____20346 = solve_prob orig guard [] wl  in
                            solve env uu____20346
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20349,FStar_Syntax_Syntax.Tm_match uu____20350) ->
                     let head1 =
                       let uu____20376 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20376
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20420 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20420
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20462 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20462
                       then
                         let uu____20463 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20464 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20465 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20463 uu____20464 uu____20465
                       else ());
                      (let uu____20467 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20467
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20482 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20482
                          then
                            let guard =
                              let uu____20494 =
                                let uu____20495 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20495 = FStar_Syntax_Util.Equal  in
                              if uu____20494
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20499 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_82  ->
                                      FStar_Pervasives_Native.Some _0_82)
                                   uu____20499)
                               in
                            let uu____20502 = solve_prob orig guard [] wl  in
                            solve env uu____20502
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20505,FStar_Syntax_Syntax.Tm_uinst uu____20506) ->
                     let head1 =
                       let uu____20516 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20516
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20560 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20560
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20602 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20602
                       then
                         let uu____20603 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20604 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20605 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20603 uu____20604 uu____20605
                       else ());
                      (let uu____20607 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20607
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20622 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20622
                          then
                            let guard =
                              let uu____20634 =
                                let uu____20635 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20635 = FStar_Syntax_Util.Equal  in
                              if uu____20634
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20639 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_83  ->
                                      FStar_Pervasives_Native.Some _0_83)
                                   uu____20639)
                               in
                            let uu____20642 = solve_prob orig guard [] wl  in
                            solve env uu____20642
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20645,FStar_Syntax_Syntax.Tm_name uu____20646) ->
                     let head1 =
                       let uu____20650 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20650
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20694 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20694
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20736 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20736
                       then
                         let uu____20737 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20738 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20739 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20737 uu____20738 uu____20739
                       else ());
                      (let uu____20741 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20741
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20756 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20756
                          then
                            let guard =
                              let uu____20768 =
                                let uu____20769 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20769 = FStar_Syntax_Util.Equal  in
                              if uu____20768
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20773 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_84  ->
                                      FStar_Pervasives_Native.Some _0_84)
                                   uu____20773)
                               in
                            let uu____20776 = solve_prob orig guard [] wl  in
                            solve env uu____20776
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20779,FStar_Syntax_Syntax.Tm_constant uu____20780)
                     ->
                     let head1 =
                       let uu____20784 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20784
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20828 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20828
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____20870 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____20870
                       then
                         let uu____20871 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____20872 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____20873 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____20871 uu____20872 uu____20873
                       else ());
                      (let uu____20875 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____20875
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____20890 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____20890
                          then
                            let guard =
                              let uu____20902 =
                                let uu____20903 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____20903 = FStar_Syntax_Util.Equal  in
                              if uu____20902
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____20907 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_85  ->
                                      FStar_Pervasives_Native.Some _0_85)
                                   uu____20907)
                               in
                            let uu____20910 = solve_prob orig guard [] wl  in
                            solve env uu____20910
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____20913,FStar_Syntax_Syntax.Tm_fvar uu____20914) ->
                     let head1 =
                       let uu____20918 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____20918
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____20962 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____20962
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21004 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21004
                       then
                         let uu____21005 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21006 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21007 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21005 uu____21006 uu____21007
                       else ());
                      (let uu____21009 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21009
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21024 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21024
                          then
                            let guard =
                              let uu____21036 =
                                let uu____21037 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21037 = FStar_Syntax_Util.Equal  in
                              if uu____21036
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21041 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_86  ->
                                      FStar_Pervasives_Native.Some _0_86)
                                   uu____21041)
                               in
                            let uu____21044 = solve_prob orig guard [] wl  in
                            solve env uu____21044
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (uu____21047,FStar_Syntax_Syntax.Tm_app uu____21048) ->
                     let head1 =
                       let uu____21066 = FStar_Syntax_Util.head_and_args t1
                          in
                       FStar_All.pipe_right uu____21066
                         FStar_Pervasives_Native.fst
                        in
                     let head2 =
                       let uu____21110 = FStar_Syntax_Util.head_and_args t2
                          in
                       FStar_All.pipe_right uu____21110
                         FStar_Pervasives_Native.fst
                        in
                     ((let uu____21152 =
                         FStar_TypeChecker_Env.debug env
                           (FStar_Options.Other "RelCheck")
                          in
                       if uu____21152
                       then
                         let uu____21153 =
                           FStar_Util.string_of_int
                             problem.FStar_TypeChecker_Common.pid
                            in
                         let uu____21154 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____21155 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.print3
                           ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                           uu____21153 uu____21154 uu____21155
                       else ());
                      (let uu____21157 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21157
                       then
                         let uv1 = FStar_Syntax_Free.uvars t1  in
                         let uv2 = FStar_Syntax_Free.uvars t2  in
                         let uu____21172 =
                           (FStar_Util.set_is_empty uv1) &&
                             (FStar_Util.set_is_empty uv2)
                            in
                         (if uu____21172
                          then
                            let guard =
                              let uu____21184 =
                                let uu____21185 =
                                  FStar_Syntax_Util.eq_tm t1 t2  in
                                uu____21185 = FStar_Syntax_Util.Equal  in
                              if uu____21184
                              then FStar_Pervasives_Native.None
                              else
                                (let uu____21189 = mk_eq2 orig t1 t2  in
                                 FStar_All.pipe_left
                                   (fun _0_87  ->
                                      FStar_Pervasives_Native.Some _0_87)
                                   uu____21189)
                               in
                            let uu____21192 = solve_prob orig guard [] wl  in
                            solve env uu____21192
                          else
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2))
                 | (FStar_Syntax_Syntax.Tm_let
                    uu____21195,FStar_Syntax_Syntax.Tm_let uu____21196) ->
                     let uu____21221 = FStar_Syntax_Util.term_eq t1 t2  in
                     if uu____21221
                     then
                       let uu____21222 =
                         solve_prob orig FStar_Pervasives_Native.None [] wl
                          in
                       solve env uu____21222
                     else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
                 | (FStar_Syntax_Syntax.Tm_let uu____21224,uu____21225) ->
                     let uu____21238 =
                       let uu____21243 =
                         let uu____21244 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____21245 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____21246 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____21247 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____21244 uu____21245 uu____21246 uu____21247
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____21243)
                        in
                     FStar_Errors.raise_error uu____21238
                       t1.FStar_Syntax_Syntax.pos
                 | (uu____21248,FStar_Syntax_Syntax.Tm_let uu____21249) ->
                     let uu____21262 =
                       let uu____21267 =
                         let uu____21268 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____21269 = FStar_Syntax_Print.tag_of_term t2
                            in
                         let uu____21270 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____21271 =
                           FStar_Syntax_Print.term_to_string t2  in
                         FStar_Util.format4
                           "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                           uu____21268 uu____21269 uu____21270 uu____21271
                          in
                       (FStar_Errors.Fatal_UnificationNotWellFormed,
                         uu____21267)
                        in
                     FStar_Errors.raise_error uu____21262
                       t1.FStar_Syntax_Syntax.pos
                 | uu____21272 -> giveup env "head tag mismatch" orig)))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob t1 rel t2 reason =
          let uu____21300 = p_scope orig  in
          mk_problem uu____21300 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____21309 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____21309
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____21311 =
               let uu____21312 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____21313 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____21312 uu____21313
                in
             giveup env uu____21311 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____21333  ->
                    fun uu____21334  ->
                      match (uu____21333, uu____21334) with
                      | ((a1,uu____21352),(a2,uu____21354)) ->
                          let uu____21363 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg"
                             in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____21363)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args
                in
             let guard =
               let uu____21373 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs
                  in
               FStar_Syntax_Util.mk_conj_l uu____21373  in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
             solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____21397 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____21404)::[] -> wp1
              | uu____21421 ->
                  let uu____21430 =
                    let uu____21431 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____21431
                     in
                  failwith uu____21430
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____21439 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____21439]
              | x -> x  in
            let uu____21441 =
              let uu____21450 =
                let uu____21451 =
                  let uu____21452 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____21452 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____21451  in
              [uu____21450]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____21441;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____21453 = lift_c1 ()  in solve_eq uu____21453 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___115_21459  ->
                       match uu___115_21459 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____21460 -> false))
                in
             let uu____21461 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____21495)::uu____21496,(wp2,uu____21498)::uu____21499)
                   -> (wp1, wp2)
               | uu____21556 ->
                   let uu____21577 =
                     let uu____21582 =
                       let uu____21583 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____21584 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21583 uu____21584
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21582)
                      in
                   FStar_Errors.raise_error uu____21577
                     env.FStar_TypeChecker_Env.range
                in
             match uu____21461 with
             | (wpc1,wpc2) ->
                 let uu____21603 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____21603
                 then
                   let uu____21606 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____21606 wl
                 else
                   (let uu____21610 =
                      let uu____21617 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____21617  in
                    match uu____21610 with
                    | (c2_decl,qualifiers) ->
                        let uu____21638 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____21638
                        then
                          let c1_repr =
                            let uu____21642 =
                              let uu____21643 =
                                let uu____21644 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____21644  in
                              let uu____21645 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21643 uu____21645
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21642
                             in
                          let c2_repr =
                            let uu____21647 =
                              let uu____21648 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____21649 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21648 uu____21649
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21647
                             in
                          let prob =
                            let uu____21651 =
                              let uu____21656 =
                                let uu____21657 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____21658 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21657
                                  uu____21658
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21656
                               in
                            FStar_TypeChecker_Common.TProb uu____21651  in
                          let wl1 =
                            let uu____21660 =
                              let uu____21663 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____21663  in
                            solve_prob orig uu____21660 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21672 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21672
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____21675 =
                                     let uu____21678 =
                                       let uu____21679 =
                                         let uu____21694 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____21695 =
                                           let uu____21698 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____21699 =
                                             let uu____21702 =
                                               let uu____21703 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21703
                                                in
                                             [uu____21702]  in
                                           uu____21698 :: uu____21699  in
                                         (uu____21694, uu____21695)  in
                                       FStar_Syntax_Syntax.Tm_app uu____21679
                                        in
                                     FStar_Syntax_Syntax.mk uu____21678  in
                                   uu____21675 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____21712 =
                                    let uu____21715 =
                                      let uu____21716 =
                                        let uu____21731 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____21732 =
                                          let uu____21735 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____21736 =
                                            let uu____21739 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____21740 =
                                              let uu____21743 =
                                                let uu____21744 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21744
                                                 in
                                              [uu____21743]  in
                                            uu____21739 :: uu____21740  in
                                          uu____21735 :: uu____21736  in
                                        (uu____21731, uu____21732)  in
                                      FStar_Syntax_Syntax.Tm_app uu____21716
                                       in
                                    FStar_Syntax_Syntax.mk uu____21715  in
                                  uu____21712 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____21751 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21751
                              in
                           let wl1 =
                             let uu____21761 =
                               let uu____21764 =
                                 let uu____21767 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____21767 g  in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21764
                                in
                             solve_prob orig uu____21761 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____21780 = FStar_Util.physical_equality c1 c2  in
        if uu____21780
        then
          let uu____21781 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21781
        else
          ((let uu____21784 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21784
            then
              let uu____21785 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21786 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21785
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21786
            else ());
           (let uu____21788 =
              let uu____21793 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21794 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21793, uu____21794)  in
            match uu____21788 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21798),FStar_Syntax_Syntax.Total
                    (t2,uu____21800)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21817 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21817 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21820,FStar_Syntax_Syntax.Total uu____21821) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21839),FStar_Syntax_Syntax.Total
                    (t2,uu____21841)) ->
                     let uu____21858 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21858 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21862),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21864)) ->
                     let uu____21881 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21881 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21885),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21887)) ->
                     let uu____21904 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21904 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21907,FStar_Syntax_Syntax.Comp uu____21908) ->
                     let uu____21917 =
                       let uu___164_21922 = problem  in
                       let uu____21927 =
                         let uu____21928 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21928
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___164_21922.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21927;
                         FStar_TypeChecker_Common.relation =
                           (uu___164_21922.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___164_21922.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___164_21922.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___164_21922.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___164_21922.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___164_21922.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___164_21922.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___164_21922.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21917 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21929,FStar_Syntax_Syntax.Comp uu____21930) ->
                     let uu____21939 =
                       let uu___164_21944 = problem  in
                       let uu____21949 =
                         let uu____21950 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21950
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___164_21944.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21949;
                         FStar_TypeChecker_Common.relation =
                           (uu___164_21944.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___164_21944.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___164_21944.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___164_21944.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___164_21944.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___164_21944.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___164_21944.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___164_21944.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21939 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21951,FStar_Syntax_Syntax.GTotal uu____21952) ->
                     let uu____21961 =
                       let uu___165_21966 = problem  in
                       let uu____21971 =
                         let uu____21972 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21972
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___165_21966.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___165_21966.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___165_21966.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21971;
                         FStar_TypeChecker_Common.element =
                           (uu___165_21966.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___165_21966.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___165_21966.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___165_21966.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___165_21966.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___165_21966.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21961 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21973,FStar_Syntax_Syntax.Total uu____21974) ->
                     let uu____21983 =
                       let uu___165_21988 = problem  in
                       let uu____21993 =
                         let uu____21994 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21994
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___165_21988.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___165_21988.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___165_21988.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21993;
                         FStar_TypeChecker_Common.element =
                           (uu___165_21988.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___165_21988.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___165_21988.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___165_21988.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___165_21988.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___165_21988.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21983 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21995,FStar_Syntax_Syntax.Comp uu____21996) ->
                     let uu____21997 =
                       (((FStar_Syntax_Util.is_ml_comp c11) &&
                           (FStar_Syntax_Util.is_ml_comp c21))
                          ||
                          ((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_total_comp c21)))
                         ||
                         (((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_ml_comp c21))
                            &&
                            (problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____21997
                     then
                       let uu____21998 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21998 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____22004 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____22014 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____22015 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____22014, uu____22015))
                             in
                          match uu____22004 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____22022 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____22022
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____22024 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____22024 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____22027 =
                                  let uu____22028 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____22029 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____22028 uu____22029
                                   in
                                giveup env uu____22027 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____22034 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____22072  ->
              match uu____22072 with
              | (uu____22085,uu____22086,u,uu____22088,uu____22089,uu____22090)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____22034 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____22121 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____22121 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____22139 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____22167  ->
                match uu____22167 with
                | (u1,u2) ->
                    let uu____22174 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____22175 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____22174 uu____22175))
         in
      FStar_All.pipe_right uu____22139 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____22192,[])) -> "{}"
      | uu____22217 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____22234 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____22234
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____22237 =
              FStar_List.map
                (fun uu____22247  ->
                   match uu____22247 with
                   | (uu____22252,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____22237 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____22257 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____22257 imps
  
let new_t_problem :
  'Auu____22265 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____22265 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____22265)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____22299 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____22299
                then
                  let uu____22300 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____22301 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____22300
                    (rel_to_string rel) uu____22301
                else "TOP"  in
              let p = new_problem env lhs rel rhs elt loc reason  in p
  
let (new_t_prob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____22325 =
              let uu____22328 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____22328
               in
            FStar_Syntax_Syntax.new_bv uu____22325 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____22337 =
              let uu____22340 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____22340
               in
            let uu____22343 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____22337 uu____22343  in
          ((FStar_TypeChecker_Common.TProb p), x)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
        -> FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let probs1 =
          let uu____22373 = FStar_Options.eager_inference ()  in
          if uu____22373
          then
            let uu___166_22374 = probs  in
            {
              attempting = (uu___166_22374.attempting);
              wl_deferred = (uu___166_22374.wl_deferred);
              ctr = (uu___166_22374.ctr);
              defer_ok = false;
              smt_ok = (uu___166_22374.smt_ok);
              tcenv = (uu___166_22374.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____22385 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____22385
              then
                let uu____22386 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____22386
              else ());
             (let result = err (d, s)  in
              FStar_Syntax_Unionfind.rollback tx; result))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____22400 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____22400
            then
              let uu____22401 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____22401
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____22405 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____22405
             then
               let uu____22406 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____22406
             else ());
            (let f2 =
               let uu____22409 =
                 let uu____22410 = FStar_Syntax_Util.unmeta f1  in
                 uu____22410.FStar_Syntax_Syntax.n  in
               match uu____22409 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____22414 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___167_22415 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___167_22415.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___167_22415.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___167_22415.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____22434 =
              let uu____22435 =
                let uu____22436 =
                  let uu____22437 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____22437
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____22436;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____22435  in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____22434
  
let with_guard_no_simp :
  'Auu____22464 .
    'Auu____22464 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____22484 =
              let uu____22485 =
                let uu____22486 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____22486
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____22485;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____22484
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____22524 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____22524
           then
             let uu____22525 = FStar_Syntax_Print.term_to_string t1  in
             let uu____22526 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22525
               uu____22526
           else ());
          (let prob =
             let uu____22529 =
               let uu____22534 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22534
                in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____22529
              in
           let g =
             let uu____22542 =
               let uu____22545 = singleton' env prob smt_ok  in
               solve_and_commit env uu____22545
                 (fun uu____22547  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____22542  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22565 = try_teq true env t1 t2  in
        match uu____22565 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22569 = FStar_TypeChecker_Env.get_range env  in
              let uu____22570 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22569 uu____22570);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22577 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22577
              then
                let uu____22578 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22579 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22580 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22578
                  uu____22579 uu____22580
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____22594 = FStar_TypeChecker_Env.get_range env  in
          let uu____22595 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22594 uu____22595
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22612 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22612
         then
           let uu____22613 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22614 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22613
             uu____22614
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____22619 =
             let uu____22624 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22624 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____22619
            in
         let uu____22629 =
           let uu____22632 = singleton env prob  in
           solve_and_commit env uu____22632
             (fun uu____22634  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____22629)
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____22663  ->
        match uu____22663 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22702 =
                 let uu____22707 =
                   let uu____22708 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22709 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22708 uu____22709
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22707)  in
               let uu____22710 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22702 uu____22710)
               in
            let equiv1 v1 v' =
              let uu____22718 =
                let uu____22723 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22724 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22723, uu____22724)  in
              match uu____22718 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22743 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22773 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22773 with
                      | FStar_Syntax_Syntax.U_unif uu____22780 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22809  ->
                                    match uu____22809 with
                                    | (u,v') ->
                                        let uu____22818 = equiv1 v1 v'  in
                                        if uu____22818
                                        then
                                          let uu____22821 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22821 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22837 -> []))
               in
            let uu____22842 =
              let wl =
                let uu___168_22846 = empty_worklist env  in
                {
                  attempting = (uu___168_22846.attempting);
                  wl_deferred = (uu___168_22846.wl_deferred);
                  ctr = (uu___168_22846.ctr);
                  defer_ok = false;
                  smt_ok = (uu___168_22846.smt_ok);
                  tcenv = (uu___168_22846.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22864  ->
                      match uu____22864 with
                      | (lb,v1) ->
                          let uu____22871 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22871 with
                           | USolved wl1 -> ()
                           | uu____22873 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22881 =
              match uu____22881 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22890) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____22913,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22915,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22926) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22933,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22941 -> false)
               in
            let uu____22946 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22961  ->
                      match uu____22961 with
                      | (u,v1) ->
                          let uu____22968 = check_ineq (u, v1)  in
                          if uu____22968
                          then true
                          else
                            ((let uu____22971 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22971
                              then
                                let uu____22972 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22973 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22972
                                  uu____22973
                              else ());
                             false)))
               in
            if uu____22946
            then ()
            else
              ((let uu____22977 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22977
                then
                  ((let uu____22979 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22979);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22989 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22989))
                else ());
               (let uu____22999 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22999))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let rec (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let fail1 uu____23047 =
        match uu____23047 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____23061 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____23061
       then
         let uu____23062 = wl_to_string wl  in
         let uu____23063 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____23062 uu____23063
       else ());
      (let g1 =
         let uu____23078 = solve_and_commit env wl fail1  in
         match uu____23078 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___169_23091 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___169_23091.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___169_23091.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___169_23091.FStar_TypeChecker_Env.implicits)
             }
         | uu____23096 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___170_23100 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___170_23100.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___170_23100.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___170_23100.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____23126 = FStar_ST.op_Bang last_proof_ns  in
    match uu____23126 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals last_proof_ns
          (FStar_Pervasives_Native.Some pns)
    | FStar_Pervasives_Native.Some old ->
        if old = pns
        then ()
        else
          ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           FStar_ST.op_Colon_Equals last_proof_ns
             (FStar_Pervasives_Native.Some pns))
  
let (discharge_guard' :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___171_23229 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___171_23229.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___171_23229.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___171_23229.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____23230 =
            let uu____23231 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____23231  in
          if uu____23230
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____23239 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____23240 =
                       let uu____23241 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____23241
                        in
                     FStar_Errors.diag uu____23239 uu____23240)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____23245 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____23246 =
                        let uu____23247 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____23247
                         in
                      FStar_Errors.diag uu____23245 uu____23246)
                   else ();
                   (let uu____23250 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____23250 "discharge_guard'"
                      env vc1);
                   (let uu____23251 = check_trivial vc1  in
                    match uu____23251 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____23258 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____23259 =
                                let uu____23260 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____23260
                                 in
                              FStar_Errors.diag uu____23258 uu____23259)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____23265 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____23266 =
                                let uu____23267 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____23267
                                 in
                              FStar_Errors.diag uu____23265 uu____23266)
                           else ();
                           (let vcs =
                              let uu____23278 = FStar_Options.use_tactics ()
                                 in
                              if uu____23278
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____23297  ->
                                     (let uu____23299 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____23299);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____23301 =
                                   let uu____23308 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____23308)  in
                                 [uu____23301])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23342  ->
                                    match uu____23342 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____23353 = check_trivial goal1
                                           in
                                        (match uu____23353 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug1
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal2 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              maybe_update_proof_ns env1;
                                              if debug1
                                              then
                                                (let uu____23361 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23362 =
                                                   let uu____23363 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____23364 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23363 uu____23364
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23361 uu____23362)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23367 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23368 =
                                                   let uu____23369 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23369
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23367 uu____23368)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal2;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23379 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23379 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23385 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23385
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23392 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23392 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (resolve_implicits' :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total  ->
    fun forcelax  ->
      fun g  ->
        let unresolved u =
          let uu____23411 = FStar_Syntax_Unionfind.find u  in
          match uu____23411 with
          | FStar_Pervasives_Native.None  -> true
          | uu____23414 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____23432 = acc  in
          match uu____23432 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23518 = hd1  in
                   (match uu____23518 with
                    | (uu____23531,env,u,tm,k,r) ->
                        let uu____23537 = unresolved u  in
                        if uu____23537
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___172_23567 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___172_23567.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___172_23567.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___172_23567.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___172_23567.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___172_23567.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___172_23567.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___172_23567.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___172_23567.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___172_23567.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___172_23567.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___172_23567.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___172_23567.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___172_23567.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___172_23567.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___172_23567.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___172_23567.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___172_23567.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___172_23567.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___172_23567.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___172_23567.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___172_23567.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___172_23567.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___172_23567.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___172_23567.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___172_23567.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___172_23567.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___172_23567.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___172_23567.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___172_23567.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___172_23567.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___172_23567.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___172_23567.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___172_23567.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___172_23567.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___172_23567.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____23570 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____23570
                            then
                              let uu____23571 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____23572 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____23573 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23571 uu____23572 uu____23573
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____23584 =
                                      let uu____23593 =
                                        let uu____23600 =
                                          let uu____23601 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____23602 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23601 uu____23602
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23600, r)
                                         in
                                      [uu____23593]  in
                                    FStar_Errors.add_errors uu____23584);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___175_23616 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___175_23616.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___175_23616.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___175_23616.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____23619 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23625  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____23619 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                               in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1))))
           in
        let uu___176_23653 = g  in
        let uu____23654 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___176_23653.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___176_23653.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___176_23653.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23654
        }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g  -> resolve_implicits' true false g 
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g  -> resolve_implicits' false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____23708 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23708 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23721 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23721
      | (reason,uu____23723,uu____23724,e,t,r)::uu____23728 ->
          let uu____23755 =
            let uu____23760 =
              let uu____23761 = FStar_Syntax_Print.term_to_string t  in
              let uu____23762 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23761 uu____23762
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23760)
             in
          FStar_Errors.raise_error uu____23755 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___177_23769 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___177_23769.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___177_23769.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___177_23769.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23792 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23792 with
      | FStar_Pervasives_Native.Some uu____23797 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23807 = try_teq false env t1 t2  in
        match uu____23807 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> discharge_guard_nosmt env g
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23827 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23827
         then
           let uu____23828 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23829 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23828
             uu____23829
         else ());
        (let uu____23831 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23831 with
         | (prob,x) ->
             let g =
               let uu____23847 =
                 let uu____23850 = singleton' env prob true  in
                 solve_and_commit env uu____23850
                   (fun uu____23852  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23847  in
             ((let uu____23862 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23862
               then
                 let uu____23863 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23864 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23865 =
                   let uu____23866 = FStar_Util.must g  in
                   guard_to_string env uu____23866  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23863 uu____23864 uu____23865
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23894 = check_subtyping env t1 t2  in
        match uu____23894 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23913 =
              let uu____23914 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23914 g  in
            FStar_Pervasives_Native.Some uu____23913
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23926 = check_subtyping env t1 t2  in
        match uu____23926 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23945 =
              let uu____23946 =
                let uu____23947 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23947]  in
              close_guard env uu____23946 g  in
            FStar_Pervasives_Native.Some uu____23945
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23958 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23958
         then
           let uu____23959 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23960 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23959
             uu____23960
         else ());
        (let uu____23962 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23962 with
         | (prob,x) ->
             let g =
               let uu____23972 =
                 let uu____23975 = singleton' env prob false  in
                 solve_and_commit env uu____23975
                   (fun uu____23977  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23972  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23988 =
                      let uu____23989 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23989]  in
                    close_guard env uu____23988 g1  in
                  discharge_guard_nosmt env g2))
  