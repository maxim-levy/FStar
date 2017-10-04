open Prims
let guard_of_guard_formula:
  FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
let guard_form:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun g  -> g.FStar_TypeChecker_Env.guard_f
let is_trivial: FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = [];
        FStar_TypeChecker_Env.univ_ineqs = uu____33;
        FStar_TypeChecker_Env.implicits = uu____34;_} -> true
    | uu____61 -> false
let trivial_guard: FStar_TypeChecker_Env.guard_t =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  }
let abstract_guard:
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun x  ->
    fun g  ->
      match g with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = uu____98;
            FStar_TypeChecker_Env.univ_ineqs = uu____99;
            FStar_TypeChecker_Env.implicits = uu____100;_}
          -> g
      | FStar_Pervasives_Native.Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____126 -> failwith "impossible" in
          let uu____127 =
            let uu___141_128 = g1 in
            let uu____129 =
              let uu____130 =
                let uu____131 =
                  let uu____132 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____132] in
                FStar_Syntax_Util.abs uu____131 f
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)) in
              FStar_All.pipe_left
                (fun _0_41  -> FStar_TypeChecker_Common.NonTrivial _0_41)
                uu____130 in
            {
              FStar_TypeChecker_Env.guard_f = uu____129;
              FStar_TypeChecker_Env.deferred =
                (uu___141_128.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___141_128.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___141_128.FStar_TypeChecker_Env.implicits)
            } in
          FStar_Pervasives_Native.Some uu____127
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___142_142 = g in
          let uu____143 =
            let uu____144 =
              let uu____145 =
                let uu____148 =
                  let uu____149 =
                    let uu____164 =
                      let uu____167 = FStar_Syntax_Syntax.as_arg e in
                      [uu____167] in
                    (f, uu____164) in
                  FStar_Syntax_Syntax.Tm_app uu____149 in
                FStar_Syntax_Syntax.mk uu____148 in
              uu____145 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_42  -> FStar_TypeChecker_Common.NonTrivial _0_42)
              uu____144 in
          {
            FStar_TypeChecker_Env.guard_f = uu____143;
            FStar_TypeChecker_Env.deferred =
              (uu___142_142.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___142_142.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___142_142.FStar_TypeChecker_Env.implicits)
          }
let map_guard:
  FStar_TypeChecker_Env.guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___143_187 = g in
          let uu____188 =
            let uu____189 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____189 in
          {
            FStar_TypeChecker_Env.guard_f = uu____188;
            FStar_TypeChecker_Env.deferred =
              (uu___143_187.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___143_187.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___143_187.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____194 -> failwith "impossible"
let conj_guard_f:
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____207 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____207
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____212 =
      let uu____213 = FStar_Syntax_Util.unmeta t in
      uu____213.FStar_Syntax_Syntax.n in
    match uu____212 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____217 -> FStar_TypeChecker_Common.NonTrivial t
let imp_guard_f:
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2 in check_trivial imp
let binop_guard:
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____253 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____253;
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
let conj_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2
let imp_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2
let close_guard_univs:
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
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
                       let uu____327 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____327
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___144_329 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___144_329.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___144_329.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___144_329.FStar_TypeChecker_Env.implicits)
            }
let close_forall:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____351 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____351
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
let close_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___145_367 = g in
            let uu____368 =
              let uu____369 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____369 in
            {
              FStar_TypeChecker_Env.guard_f = uu____368;
              FStar_TypeChecker_Env.deferred =
                (uu___145_367.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___145_367.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___145_367.FStar_TypeChecker_Env.implicits)
            }
let new_uvar:
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Syntax_Unionfind.fresh () in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                FStar_Pervasives_Native.None r in
            (uv1, uv1)
        | uu____402 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____427 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____427 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____435 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____435, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____466 = FStar_Syntax_Util.type_u () in
        match uu____466 with
        | (t_type,u) ->
            let uu____473 =
              let uu____478 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____478 t_type in
            (match uu____473 with
             | (tt,uu____480) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____514 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____556 -> false
let __proj__UNIV__item___0:
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UNIV _0 -> _0
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list;
  ctr: Prims.int;
  defer_ok: Prims.bool;
  smt_ok: Prims.bool;
  tcenv: FStar_TypeChecker_Env.env;}[@@deriving show]
let __proj__Mkworklist__item__attempting:
  worklist -> FStar_TypeChecker_Common.probs =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__attempting
let __proj__Mkworklist__item__wl_deferred:
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__wl_deferred
let __proj__Mkworklist__item__ctr: worklist -> Prims.int =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__ctr
let __proj__Mkworklist__item__defer_ok: worklist -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__defer_ok
let __proj__Mkworklist__item__smt_ok: worklist -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__smt_ok
let __proj__Mkworklist__item__tcenv: worklist -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__tcenv
type solution =
  | Success of FStar_TypeChecker_Common.deferred
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Success: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____750 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____768 -> false
let __proj__Failed__item___0:
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT[@@deriving show]
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____793 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____798 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____803 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___113_827  ->
    match uu___113_827 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t in
    let detail =
      let uu____834 =
        let uu____835 = FStar_Syntax_Subst.compress t in
        uu____835.FStar_Syntax_Syntax.n in
      match uu____834 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____864 = FStar_Syntax_Print.uvar_to_string u in
          let uu____865 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.format2 "%s : %s" uu____864 uu____865
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____868;
             FStar_Syntax_Syntax.vars = uu____869;_},args)
          ->
          let uu____915 = FStar_Syntax_Print.uvar_to_string u in
          let uu____916 = FStar_Syntax_Print.term_to_string ty in
          let uu____917 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.format3 "(%s : %s) %s" uu____915 uu____916 uu____917
      | uu____918 -> "--" in
    let uu____919 = FStar_Syntax_Print.tag_of_term t in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____919 detail
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___114_927  ->
      match uu___114_927 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____933 =
            let uu____936 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____937 =
              let uu____940 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____941 =
                let uu____944 =
                  let uu____947 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____947] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____944 in
              uu____940 :: uu____941 in
            uu____936 :: uu____937 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____933
      | FStar_TypeChecker_Common.CProb p ->
          let uu____953 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____954 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\n\t%s \n\t\t%s\n\t%s" uu____953
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____954
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___115_962  ->
      match uu___115_962 with
      | UNIV (u,t) ->
          let x =
            let uu____966 = FStar_Options.hide_uvar_nums () in
            if uu____966
            then "?"
            else
              (let uu____968 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____968 FStar_Util.string_of_int) in
          let uu____969 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____969
      | TERM ((u,uu____971),t) ->
          let x =
            let uu____978 = FStar_Options.hide_uvar_nums () in
            if uu____978
            then "?"
            else
              (let uu____980 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____980 FStar_Util.string_of_int) in
          let uu____981 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____981
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____994 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____994 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____1007 =
      let uu____1010 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1010
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1007 (FStar_String.concat ", ")
let args_to_string:
  'Auu____1023 .
    (FStar_Syntax_Syntax.term,'Auu____1023) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1040 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1058  ->
              match uu____1058 with
              | (x,uu____1064) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1040 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1071 =
      let uu____1072 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1072 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1071;
      smt_ok = true;
      tcenv = env
    }
let singleton':
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.bool -> worklist
  =
  fun env  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___146_1091 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___146_1091.wl_deferred);
          ctr = (uu___146_1091.ctr);
          defer_ok = (uu___146_1091.defer_ok);
          smt_ok;
          tcenv = (uu___146_1091.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard:
  'Auu____1106 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1106,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___147_1127 = empty_worklist env in
      let uu____1128 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1128;
        wl_deferred = (uu___147_1127.wl_deferred);
        ctr = (uu___147_1127.ctr);
        defer_ok = false;
        smt_ok = (uu___147_1127.smt_ok);
        tcenv = (uu___147_1127.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___148_1145 = wl in
        {
          attempting = (uu___148_1145.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___148_1145.ctr);
          defer_ok = (uu___148_1145.defer_ok);
          smt_ok = (uu___148_1145.smt_ok);
          tcenv = (uu___148_1145.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___149_1164 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___149_1164.wl_deferred);
        ctr = (uu___149_1164.ctr);
        defer_ok = (uu___149_1164.defer_ok);
        smt_ok = (uu___149_1164.smt_ok);
        tcenv = (uu___149_1164.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1178 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1178
         then
           let uu____1179 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1179
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___116_1184  ->
    match uu___116_1184 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1191 'Auu____1192 .
    ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem ->
      ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___150_1209 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___150_1209.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___150_1209.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___150_1209.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___150_1209.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___150_1209.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___150_1209.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___150_1209.FStar_TypeChecker_Common.rank)
    }
let maybe_invert:
  'Auu____1220 'Auu____1221 .
    ('Auu____1221,'Auu____1220) FStar_TypeChecker_Common.problem ->
      ('Auu____1221,'Auu____1220) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___117_1242  ->
    match uu___117_1242 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___118_1268  ->
      match uu___118_1268 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___119_1272  ->
    match uu___119_1272 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___120_1286  ->
    match uu___120_1286 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___121_1302  ->
    match uu___121_1302 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___122_1318  ->
    match uu___122_1318 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___123_1336  ->
    match uu___123_1336 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___124_1354  ->
    match uu___124_1354 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___125_1368  ->
    match uu___125_1368 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.TProb _0_45) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_46  -> FStar_TypeChecker_Common.CProb _0_46) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1391 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1391 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1404  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem:
  'Auu____1505 'Auu____1506 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1506 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1506 ->
              'Auu____1505 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1506,'Auu____1505)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1543 = next_pid () in
                let uu____1544 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1543;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1544;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1567 'Auu____1568 .
    FStar_TypeChecker_Env.env ->
      'Auu____1568 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1568 ->
            'Auu____1567 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1568,'Auu____1567)
                    FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              fun reason  ->
                let scope = FStar_TypeChecker_Env.all_binders env in
                let uu____1606 = next_pid () in
                let uu____1607 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1606;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1607;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1628 'Auu____1629 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1629 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1629 ->
            'Auu____1628 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1629,'Auu____1628) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1662 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1662;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.scope = (p_scope orig);
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
let guard_on_element:
  'Auu____1673 .
    worklist ->
      ('Auu____1673,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
                  x.FStar_Syntax_Syntax.sort in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
let explain:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1726 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1726
        then
          let uu____1727 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1728 = prob_to_string env d in
          let uu____1729 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1727 uu____1728 uu____1729 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1735 -> failwith "impossible" in
           let uu____1736 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1750 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1751 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1750, uu____1751)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1757 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1758 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1757, uu____1758) in
           match uu____1736 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___126_1775  ->
            match uu___126_1775 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1787 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1789),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___127_1811  ->
           match uu___127_1811 with
           | UNIV uu____1814 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1820),t) ->
               let uu____1826 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1826
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___128_1848  ->
           match uu___128_1848 with
           | UNIV (u',t) ->
               let uu____1853 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1853
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1857 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1866 =
        let uu____1867 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1867 in
      FStar_Syntax_Subst.compress uu____1866
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1876 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1876
let norm_arg:
  'Auu____1883 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1883) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1883)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1904 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1904, (FStar_Pervasives_Native.snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1937  ->
              match uu____1937 with
              | (x,imp) ->
                  let uu____1948 =
                    let uu___151_1949 = x in
                    let uu____1950 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___151_1949.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___151_1949.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1950
                    } in
                  (uu____1948, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1967 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1967
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1971 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1971
        | uu____1974 -> u2 in
      let uu____1975 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1975
let normalize_refinement:
  'Auu____1986 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____1986 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement:
  'Auu____2011 .
    FStar_TypeChecker_Env.env ->
      'Auu____2011 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                                  FStar_Syntax_Syntax.term'
                                                                    FStar_Syntax_Syntax.syntax)
                                                                  FStar_Pervasives_Native.tuple2
                                                                  FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        let rec aux norm1 t11 =
          match t11.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2116 =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 match uu____2116 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2133;
                     FStar_Syntax_Syntax.vars = uu____2134;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2160 =
                       let uu____2161 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2162 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2161 uu____2162 in
                     failwith uu____2160)
          | FStar_Syntax_Syntax.Tm_uinst uu____2177 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2216 =
                   let uu____2217 = FStar_Syntax_Subst.compress t1' in
                   uu____2217.FStar_Syntax_Syntax.n in
                 match uu____2216 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2234 -> aux true t1'
                 | uu____2241 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2258 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2291 =
                   let uu____2292 = FStar_Syntax_Subst.compress t1' in
                   uu____2292.FStar_Syntax_Syntax.n in
                 match uu____2291 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2309 -> aux true t1'
                 | uu____2316 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2333 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2380 =
                   let uu____2381 = FStar_Syntax_Subst.compress t1' in
                   uu____2381.FStar_Syntax_Syntax.n in
                 match uu____2380 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2398 -> aux true t1'
                 | uu____2405 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2422 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2439 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2456 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2473 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2490 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2519 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2552 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2585 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2614 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2653 ->
              let uu____2660 =
                let uu____2661 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2662 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2661 uu____2662 in
              failwith uu____2660
          | FStar_Syntax_Syntax.Tm_ascribed uu____2677 ->
              let uu____2704 =
                let uu____2705 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2706 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2705 uu____2706 in
              failwith uu____2704
          | FStar_Syntax_Syntax.Tm_delayed uu____2721 ->
              let uu____2746 =
                let uu____2747 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2748 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2747 uu____2748 in
              failwith uu____2746
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2763 =
                let uu____2764 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2765 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2764 uu____2765 in
              failwith uu____2763 in
        let uu____2780 = whnf env t1 in aux false uu____2780
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____2791 =
        let uu____2806 = empty_worklist env in
        base_and_refinement env uu____2806 t in
      FStar_All.pipe_right uu____2791 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2841 = FStar_Syntax_Syntax.null_bv t in
    (uu____2841, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2850 .
    FStar_TypeChecker_Env.env ->
      'Auu____2850 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2867 = base_and_refinement env wl t in
        match uu____2867 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
let force_refinement:
  (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                              FStar_Pervasives_Native.tuple2
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun uu____2947  ->
    match uu____2947 with
    | (t_base,refopt) ->
        let uu____2974 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2974 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____3009 =
      let uu____3012 =
        let uu____3015 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3038  ->
                  match uu____3038 with | (uu____3045,uu____3046,x) -> x)) in
        FStar_List.append wl.attempting uu____3015 in
      FStar_List.map (wl_prob_to_string wl) uu____3012 in
    FStar_All.pipe_right uu____3009 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3074 =
          let uu____3093 =
            let uu____3094 = FStar_Syntax_Subst.compress k in
            uu____3094.FStar_Syntax_Syntax.n in
          match uu____3093 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3159 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3159)
              else
                (let uu____3185 = FStar_Syntax_Util.abs_formals t in
                 match uu____3185 with
                 | (ys',t1,uu____3214) ->
                     let uu____3219 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3219))
          | uu____3260 ->
              let uu____3261 =
                let uu____3272 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3272) in
              ((ys, t), uu____3261) in
        match uu____3074 with
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
                 let uu____3351 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3351 c in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
let solve_prob':
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            let phi =
              match logical_guard with
              | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
              | FStar_Pervasives_Native.Some phi -> phi in
            let uu____3384 = p_guard prob in
            match uu____3384 with
            | (uu____3389,uv) ->
                ((let uu____3392 =
                    let uu____3393 = FStar_Syntax_Subst.compress uv in
                    uu____3393.FStar_Syntax_Syntax.n in
                  match uu____3392 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3425 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3425
                        then
                          let uu____3426 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3427 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3428 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3426
                            uu____3427 uu____3428
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3430 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___152_3433 = wl in
                  {
                    attempting = (uu___152_3433.attempting);
                    wl_deferred = (uu___152_3433.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___152_3433.defer_ok);
                    smt_ok = (uu___152_3433.smt_ok);
                    tcenv = (uu___152_3433.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3451 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3451
         then
           let uu____3452 = FStar_Util.string_of_int pid in
           let uu____3453 =
             let uu____3454 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3454 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3452 uu____3453
         else ());
        commit sol;
        (let uu___153_3461 = wl in
         {
           attempting = (uu___153_3461.attempting);
           wl_deferred = (uu___153_3461.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___153_3461.defer_ok);
           smt_ok = (uu___153_3461.smt_ok);
           tcenv = (uu___153_3461.tcenv)
         })
let solve_prob:
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____3503,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3515 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3515 in
          (let uu____3521 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3521
           then
             let uu____3522 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3523 =
               let uu____3524 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3524 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3522 uu____3523
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs:
  'b .
    worklist ->
      (FStar_Syntax_Syntax.uvar,'b) FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun wl  ->
    fun uk  ->
      fun t  ->
        let uu____3559 =
          let uu____3566 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3566 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3559
          (FStar_Util.for_some
             (fun uu____3602  ->
                match uu____3602 with
                | (uv,uu____3608) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3621 'Auu____3622 .
    'Auu____3622 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3621)
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
            let uu____3654 = occurs wl uk t in Prims.op_Negation uu____3654 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3661 =
                 let uu____3662 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3663 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3662 uu____3663 in
               FStar_Pervasives_Native.Some uu____3661) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3680 'Auu____3681 .
    'Auu____3681 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3680)
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
            let fvs_t = FStar_Syntax_Free.names t in
            let uu____3735 = occurs_check env wl uk t in
            match uu____3735 with
            | (occurs_ok,msg) ->
                let uu____3766 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3766, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3793 'Auu____3794 .
    (FStar_Syntax_Syntax.bv,'Auu____3794) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3793) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3793) FStar_Pervasives_Native.tuple2
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
             FStar_Syntax_Syntax.no_names) in
      let v1_set = as_set1 v1 in
      let uu____3878 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3932  ->
                fun uu____3933  ->
                  match (uu____3932, uu____3933) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4014 =
                        let uu____4015 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____4015 in
                      if uu____4014
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____4040 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____4040
                         then
                           let uu____4053 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____4053)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3878 with | (isect,uu____4094) -> FStar_List.rev isect
let binders_eq:
  'Auu____4123 'Auu____4124 .
    (FStar_Syntax_Syntax.bv,'Auu____4124) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4123) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4179  ->
              fun uu____4180  ->
                match (uu____4179, uu____4180) with
                | ((a,uu____4198),(b,uu____4200)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____4219 'Auu____4220 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4220) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4219)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4219)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4271 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4285  ->
                      match uu____4285 with
                      | (b,uu____4291) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4271
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4307 -> FStar_Pervasives_Native.None
let rec pat_vars:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____4382 = pat_var_opt env seen hd1 in
            (match uu____4382 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4396 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4396
                   then
                     let uu____4397 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4397
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4416 =
      let uu____4417 = FStar_Syntax_Subst.compress t in
      uu____4417.FStar_Syntax_Syntax.n in
    match uu____4416 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4420 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4437;
           FStar_Syntax_Syntax.pos = uu____4438;
           FStar_Syntax_Syntax.vars = uu____4439;_},uu____4440)
        -> true
    | uu____4477 -> false
let destruct_flex_t:
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
      FStar_Pervasives_Native.tuple4
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
           FStar_Syntax_Syntax.pos = uu____4602;
           FStar_Syntax_Syntax.vars = uu____4603;_},args)
        -> (t, uv, k, args)
    | uu____4671 -> failwith "Not a flex-uvar"
let destruct_flex_pattern:
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
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____4750 = destruct_flex_t t in
      match uu____4750 with
      | (t1,uv,k,args) ->
          let uu____4865 = pat_vars env [] args in
          (match uu____4865 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4963 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5045 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5082 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5087 -> false
let head_match: match_result -> match_result =
  fun uu___129_5091  ->
    match uu___129_5091 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5106 -> HeadMatch
let fv_delta_depth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth
  =
  fun env  ->
    fun fv  ->
      match fv.FStar_Syntax_Syntax.fv_delta with
      | FStar_Syntax_Syntax.Delta_abstract d ->
          if
            (env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
          then d
          else FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5117 ->
          let uu____5118 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5118 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5129 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____5150 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5159 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5186 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5187 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5188 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5205 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5218 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5242) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5248,uu____5249) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5291) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5312;
             FStar_Syntax_Syntax.index = uu____5313;
             FStar_Syntax_Syntax.sort = t2;_},uu____5315)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5322 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5323 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5324 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5337 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5355 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5355
let rec head_matches:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1 in
        let t21 = FStar_Syntax_Util.unmeta t2 in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____5379 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5379
            then FullMatch
            else
              (let uu____5381 =
                 let uu____5390 =
                   let uu____5393 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5393 in
                 let uu____5394 =
                   let uu____5397 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5397 in
                 (uu____5390, uu____5394) in
               MisMatch uu____5381)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5403),FStar_Syntax_Syntax.Tm_uinst (g,uu____5405)) ->
            let uu____5414 = head_matches env f g in
            FStar_All.pipe_right uu____5414 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5423),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5425)) ->
            let uu____5474 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5474
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5481),FStar_Syntax_Syntax.Tm_refine (y,uu____5483)) ->
            let uu____5492 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5492 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5494),uu____5495) ->
            let uu____5500 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5500 head_match
        | (uu____5501,FStar_Syntax_Syntax.Tm_refine (x,uu____5503)) ->
            let uu____5508 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5508 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5509,FStar_Syntax_Syntax.Tm_type
           uu____5510) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5511,FStar_Syntax_Syntax.Tm_arrow uu____5512) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5538),FStar_Syntax_Syntax.Tm_app (head',uu____5540))
            ->
            let uu____5581 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5581 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5583),uu____5584) ->
            let uu____5605 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5605 head_match
        | (uu____5606,FStar_Syntax_Syntax.Tm_app (head1,uu____5608)) ->
            let uu____5629 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5629 head_match
        | uu____5630 ->
            let uu____5635 =
              let uu____5644 = delta_depth_of_term env t11 in
              let uu____5647 = delta_depth_of_term env t21 in
              (uu____5644, uu____5647) in
            MisMatch uu____5635
let head_matches_delta:
  'Auu____5664 .
    FStar_TypeChecker_Env.env ->
      'Auu____5664 ->
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
            let uu____5697 = FStar_Syntax_Util.head_and_args t in
            match uu____5697 with
            | (head1,uu____5715) ->
                let uu____5736 =
                  let uu____5737 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5737.FStar_Syntax_Syntax.n in
                (match uu____5736 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5743 =
                       let uu____5744 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5744 FStar_Option.isSome in
                     if uu____5743
                     then
                       let uu____5763 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5763
                         (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                     else FStar_Pervasives_Native.None
                 | uu____5767 -> FStar_Pervasives_Native.None) in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None)) in
          let fail r = (r, FStar_Pervasives_Native.None) in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21 in
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5870)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5888 =
                     let uu____5897 = maybe_inline t11 in
                     let uu____5900 = maybe_inline t21 in
                     (uu____5897, uu____5900) in
                   match uu____5888 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail r
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
                (uu____5937,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5955 =
                     let uu____5964 = maybe_inline t11 in
                     let uu____5967 = maybe_inline t21 in
                     (uu____5964, uu____5967) in
                   match uu____5955 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail r
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
                let uu____6010 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____6010 with
                 | FStar_Pervasives_Native.None  -> fail r
                 | FStar_Pervasives_Native.Some d ->
                     let t12 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.WHNF] env wl t11 in
                     let t22 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.WHNF] env wl t21 in
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
                let uu____6033 =
                  if d1_greater_than_d2
                  then
                    let t1' =
                      normalize_refinement
                        [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                        FStar_TypeChecker_Normalize.WHNF] env wl t11 in
                    (t1', t21)
                  else
                    (let t2' =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                         FStar_TypeChecker_Normalize.WHNF] env wl t21 in
                     (t11, t2')) in
                (match uu____6033 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6057 -> fail r
            | uu____6066 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6100 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6138 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___130_6152  ->
    match uu___130_6152 with
    | T (t,uu____6154) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6172 = FStar_Syntax_Util.type_u () in
      match uu____6172 with
      | (t,uu____6178) ->
          let uu____6179 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6179
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6192 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6192 FStar_Pervasives_Native.fst
let rec decompose:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (tc Prims.list -> FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term ->
                                                   Prims.bool,(FStar_Syntax_Syntax.binder
                                                                 FStar_Pervasives_Native.option,
                                                                variance,
                                                                tc)
                                                                FStar_Pervasives_Native.tuple3
                                                                Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let matches t' =
        let uu____6258 = head_matches env t1 t' in
        match uu____6258 with
        | MisMatch uu____6259 -> false
        | uu____6268 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6364,imp),T (t2,uu____6367)) -> (t2, imp)
                     | uu____6386 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6453  ->
                    match uu____6453 with
                    | (t2,uu____6467) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6510 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6510 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6585))::tcs2) ->
                       aux
                         (((let uu___154_6620 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___154_6620.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___154_6620.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6638 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___131_6691 =
                 match uu___131_6691 with
                 | [] ->
                     FStar_List.rev
                       ((FStar_Pervasives_Native.None, COVARIANT, (C c1)) ::
                       out)
                 | hd1::rest ->
                     decompose1
                       (((FStar_Pervasives_Native.Some hd1), CONTRAVARIANT,
                          (T
                             (((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____6808 = decompose1 [] bs1 in
               (rebuild, matches, uu____6808))
      | uu____6857 ->
          let rebuild uu___132_6863 =
            match uu___132_6863 with
            | [] -> t1
            | uu____6866 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___133_6898  ->
    match uu___133_6898 with
    | T (t,uu____6900) -> t
    | uu____6909 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___134_6913  ->
    match uu___134_6913 with
    | T (t,uu____6915) -> FStar_Syntax_Syntax.as_arg t
    | uu____6924 -> failwith "Impossible"
let imitation_sub_probs:
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,
            variance,tc) FStar_Pervasives_Native.tuple3 Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list,tc Prims.list,FStar_Syntax_Syntax.formula)
              FStar_Pervasives_Native.tuple3
  =
  fun orig  ->
    fun env  ->
      fun scope  ->
        fun ps  ->
          fun qs  ->
            let r = p_loc orig in
            let rel = p_rel orig in
            let sub_prob scope1 args q =
              match q with
              | (uu____7035,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7060 = new_uvar r scope1 k in
                  (match uu____7060 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7078 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7095 =
                         let uu____7096 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_48  ->
                              FStar_TypeChecker_Common.TProb _0_48)
                           uu____7096 in
                       ((T (gi_xs, mk_kind)), uu____7095))
              | (uu____7109,uu____7110,C uu____7111) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7258 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7275;
                         FStar_Syntax_Syntax.vars = uu____7276;_})
                        ->
                        let uu____7299 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7299 with
                         | (T (gi_xs,uu____7323),prob) ->
                             let uu____7333 =
                               let uu____7334 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_49  -> C _0_49)
                                 uu____7334 in
                             (uu____7333, [prob])
                         | uu____7337 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7352;
                         FStar_Syntax_Syntax.vars = uu____7353;_})
                        ->
                        let uu____7376 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7376 with
                         | (T (gi_xs,uu____7400),prob) ->
                             let uu____7410 =
                               let uu____7411 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____7411 in
                             (uu____7410, [prob])
                         | uu____7414 -> failwith "impossible")
                    | (uu____7425,uu____7426,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7428;
                         FStar_Syntax_Syntax.vars = uu____7429;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (FStar_Pervasives_Native.None, INVARIANT,
                                    (T
                                       ((FStar_Pervasives_Native.fst t),
                                         generic_kind))))) in
                        let components1 =
                          (FStar_Pervasives_Native.None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components in
                        let uu____7560 =
                          let uu____7569 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7569 FStar_List.unzip in
                        (match uu____7560 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7623 =
                                 let uu____7624 =
                                   let uu____7627 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7627 un_T in
                                 let uu____7628 =
                                   let uu____7637 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7637
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7624;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7628;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7623 in
                             ((C gi_xs), sub_probs))
                    | uu____7646 ->
                        let uu____7659 = sub_prob scope1 args q in
                        (match uu____7659 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7258 with
                   | (tc,probs) ->
                       let uu____7690 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7753,uu____7754),T
                            (t,uu____7756)) ->
                             let b1 =
                               ((let uu___155_7793 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___155_7793.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___155_7793.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7794 =
                               let uu____7801 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7801 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7794)
                         | uu____7836 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7690 with
                        | (bopt,scope2,args1) ->
                            let uu____7920 = aux scope2 args1 qs2 in
                            (match uu____7920 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7957 =
                                         let uu____7960 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7960 in
                                       FStar_Syntax_Util.mk_conj_l uu____7957
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7983 =
                                         let uu____7986 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7987 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7986 :: uu____7987 in
                                       FStar_Syntax_Util.mk_conj_l uu____7983 in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1)))) in
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
let rigid_rigid: Prims.int = Prims.parse_int "0"
let flex_rigid_eq: Prims.int = Prims.parse_int "1"
let flex_refine_inner: Prims.int = Prims.parse_int "2"
let flex_refine: Prims.int = Prims.parse_int "3"
let flex_rigid: Prims.int = Prims.parse_int "4"
let rigid_flex: Prims.int = Prims.parse_int "5"
let refine_flex: Prims.int = Prims.parse_int "6"
let flex_flex: Prims.int = Prims.parse_int "7"
let compress_tprob:
  'Auu____8058 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8058)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8058)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___156_8079 = p in
      let uu____8084 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8085 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___156_8079.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8084;
        FStar_TypeChecker_Common.relation =
          (uu___156_8079.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8085;
        FStar_TypeChecker_Common.element =
          (uu___156_8079.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___156_8079.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___156_8079.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___156_8079.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___156_8079.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___156_8079.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8099 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8099
            (fun _0_51  -> FStar_TypeChecker_Common.TProb _0_51)
      | FStar_TypeChecker_Common.CProb uu____8108 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8130 = compress_prob wl pr in
        FStar_All.pipe_right uu____8130 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8140 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8140 with
           | (lh,uu____8160) ->
               let uu____8181 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8181 with
                | (rh,uu____8201) ->
                    let uu____8222 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8239,FStar_Syntax_Syntax.Tm_uvar uu____8240)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8277,uu____8278)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8299,FStar_Syntax_Syntax.Tm_uvar uu____8300)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8321,uu____8322)
                          ->
                          let uu____8339 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8339 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8402 ->
                                    let rank =
                                      let uu____8412 = is_top_level_prob prob in
                                      if uu____8412
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8414 =
                                      let uu___157_8419 = tp in
                                      let uu____8424 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___157_8419.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___157_8419.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___157_8419.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8424;
                                        FStar_TypeChecker_Common.element =
                                          (uu___157_8419.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___157_8419.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___157_8419.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___157_8419.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___157_8419.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___157_8419.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8414)))
                      | (uu____8439,FStar_Syntax_Syntax.Tm_uvar uu____8440)
                          ->
                          let uu____8457 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8457 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8520 ->
                                    let uu____8529 =
                                      let uu___158_8536 = tp in
                                      let uu____8541 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___158_8536.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8541;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___158_8536.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___158_8536.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___158_8536.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___158_8536.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___158_8536.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___158_8536.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___158_8536.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___158_8536.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8529)))
                      | (uu____8562,uu____8563) -> (rigid_rigid, tp) in
                    (match uu____8222 with
                     | (rank,tp1) ->
                         let uu____8582 =
                           FStar_All.pipe_right
                             (let uu___159_8588 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___159_8588.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___159_8588.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___159_8588.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___159_8588.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___159_8588.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___159_8588.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___159_8588.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___159_8588.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___159_8588.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_52  ->
                                FStar_TypeChecker_Common.TProb _0_52) in
                         (rank, uu____8582))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8598 =
            FStar_All.pipe_right
              (let uu___160_8604 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___160_8604.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___160_8604.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___160_8604.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___160_8604.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___160_8604.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___160_8604.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___160_8604.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___160_8604.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___160_8604.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_53  -> FStar_TypeChecker_Common.CProb _0_53) in
          (rigid_rigid, uu____8598)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8660 probs =
      match uu____8660 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8713 = rank wl hd1 in
               (match uu____8713 with
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
                      else aux (min_rank, min1, (hd2 :: out)) tl1)) in
    aux
      ((flex_flex + (Prims.parse_int "1")), FStar_Pervasives_Native.None, [])
      wl.attempting
let is_flex_rigid: Prims.int -> Prims.bool =
  fun rank1  -> (flex_refine_inner <= rank1) && (rank1 <= flex_rigid)
let is_rigid_flex: Prims.int -> Prims.bool =
  fun rank1  -> (rigid_flex <= rank1) && (rank1 <= refine_flex)
type univ_eq_sol =
  | UDeferred of worklist
  | USolved of worklist
  | UFailed of Prims.string[@@deriving show]
let uu___is_UDeferred: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____8823 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8837 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8851 -> false
let __proj__UFailed__item___0: univ_eq_sol -> Prims.string =
  fun projectee  -> match projectee with | UFailed _0 -> _0
let rec really_solve_universe_eq:
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1 in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2 in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____8896 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8896 with
                        | (k,uu____8902) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8912 -> false)))
            | uu____8913 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8964 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8964 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8967 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8977 =
                     let uu____8978 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8979 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8978
                       uu____8979 in
                   UFailed uu____8977)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8999 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8999 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9021 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9021 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____9024 ->
                let uu____9029 =
                  let uu____9030 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____9031 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9030
                    uu____9031 msg in
                UFailed uu____9029 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9032,uu____9033) ->
              let uu____9034 =
                let uu____9035 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9036 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9035 uu____9036 in
              failwith uu____9034
          | (FStar_Syntax_Syntax.U_unknown ,uu____9037) ->
              let uu____9038 =
                let uu____9039 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9040 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9039 uu____9040 in
              failwith uu____9038
          | (uu____9041,FStar_Syntax_Syntax.U_bvar uu____9042) ->
              let uu____9043 =
                let uu____9044 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9045 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9044 uu____9045 in
              failwith uu____9043
          | (uu____9046,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9047 =
                let uu____9048 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9049 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9048 uu____9049 in
              failwith uu____9047
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9073 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9073
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9095 = occurs_univ v1 u3 in
              if uu____9095
              then
                let uu____9096 =
                  let uu____9097 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9098 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9097 uu____9098 in
                try_umax_components u11 u21 uu____9096
              else
                (let uu____9100 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9100)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9120 = occurs_univ v1 u3 in
              if uu____9120
              then
                let uu____9121 =
                  let uu____9122 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9123 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9122 uu____9123 in
                try_umax_components u11 u21 uu____9121
              else
                (let uu____9125 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9125)
          | (FStar_Syntax_Syntax.U_max uu____9134,uu____9135) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9141 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9141
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9143,FStar_Syntax_Syntax.U_max uu____9144) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9150 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9150
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9152,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9153,FStar_Syntax_Syntax.U_name
             uu____9154) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9155) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9156) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9157,FStar_Syntax_Syntax.U_succ
             uu____9158) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9159,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
let solve_universe_eq:
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
let match_num_binders:
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
      let uu____9253 = bc1 in
      match uu____9253 with
      | (bs1,mk_cod1) ->
          let uu____9294 = bc2 in
          (match uu____9294 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9364 = FStar_Util.first_N n1 bs in
                 match uu____9364 with
                 | (bs3,rest) ->
                     let uu____9389 = mk_cod rest in (bs3, uu____9389) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9418 =
                   let uu____9425 = mk_cod1 [] in (bs1, uu____9425) in
                 let uu____9428 =
                   let uu____9435 = mk_cod2 [] in (bs2, uu____9435) in
                 (uu____9418, uu____9428)
               else
                 if l1 > l2
                 then
                   (let uu____9477 = curry l2 bs1 mk_cod1 in
                    let uu____9490 =
                      let uu____9497 = mk_cod2 [] in (bs2, uu____9497) in
                    (uu____9477, uu____9490))
                 else
                   (let uu____9513 =
                      let uu____9520 = mk_cod1 [] in (bs1, uu____9520) in
                    let uu____9523 = curry l1 bs2 mk_cod2 in
                    (uu____9513, uu____9523)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9644 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9644
       then
         let uu____9645 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9645
       else ());
      (let uu____9647 = next_prob probs in
       match uu____9647 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___161_9668 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___161_9668.wl_deferred);
               ctr = (uu___161_9668.ctr);
               defer_ok = (uu___161_9668.defer_ok);
               smt_ok = (uu___161_9668.smt_ok);
               tcenv = (uu___161_9668.tcenv)
             } in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                if
                  ((Prims.op_Negation probs1.defer_ok) &&
                     (flex_refine_inner <= rank1))
                    && (rank1 <= flex_rigid)
                then
                  let uu____9679 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9679 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9684 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9684 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9689,uu____9690) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9707 ->
                let uu____9716 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9775  ->
                          match uu____9775 with
                          | (c,uu____9783,uu____9784) -> c < probs.ctr)) in
                (match uu____9716 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9825 =
                            FStar_List.map
                              (fun uu____9840  ->
                                 match uu____9840 with
                                 | (uu____9851,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9825
                      | uu____9854 ->
                          let uu____9863 =
                            let uu___162_9864 = probs in
                            let uu____9865 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9886  ->
                                      match uu____9886 with
                                      | (uu____9893,uu____9894,y) -> y)) in
                            {
                              attempting = uu____9865;
                              wl_deferred = rest;
                              ctr = (uu___162_9864.ctr);
                              defer_ok = (uu___162_9864.defer_ok);
                              smt_ok = (uu___162_9864.smt_ok);
                              tcenv = (uu___162_9864.tcenv)
                            } in
                          solve env uu____9863))))
and solve_one_universe_eq:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____9901 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9901 with
            | USolved wl1 ->
                let uu____9903 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9903
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)
and solve_maybe_uinsts:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol
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
                  let uu____9949 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9949 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9952 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9964;
                  FStar_Syntax_Syntax.vars = uu____9965;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9968;
                  FStar_Syntax_Syntax.vars = uu____9969;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9983,uu____9984) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9991,FStar_Syntax_Syntax.Tm_uinst uu____9992) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9999 -> USolved wl
and giveup_or_defer:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____10009 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____10009
              then
                let uu____10010 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10010 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10019 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10019
         then
           let uu____10020 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10020
         else ());
        (let uu____10022 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____10022 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10084 = head_matches_delta env () t1 t2 in
               match uu____10084 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10125 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10174 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10189 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10190 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10189, uu____10190)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10195 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10196 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10195, uu____10196) in
                        (match uu____10174 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10222 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_54  ->
                                    FStar_TypeChecker_Common.TProb _0_54)
                                 uu____10222 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10253 =
                                    let uu____10262 =
                                      let uu____10265 =
                                        let uu____10268 =
                                          let uu____10269 =
                                            let uu____10276 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10276) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10269 in
                                        FStar_Syntax_Syntax.mk uu____10268 in
                                      uu____10265
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10284 =
                                      let uu____10287 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10287] in
                                    (uu____10262, uu____10284) in
                                  FStar_Pervasives_Native.Some uu____10253
                              | (uu____10300,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10302)) ->
                                  let uu____10307 =
                                    let uu____10314 =
                                      let uu____10317 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10317] in
                                    (t11, uu____10314) in
                                  FStar_Pervasives_Native.Some uu____10307
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10327),uu____10328) ->
                                  let uu____10333 =
                                    let uu____10340 =
                                      let uu____10343 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10343] in
                                    (t21, uu____10340) in
                                  FStar_Pervasives_Native.Some uu____10333
                              | uu____10352 ->
                                  let uu____10357 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10357 with
                                   | (head1,uu____10381) ->
                                       let uu____10402 =
                                         let uu____10403 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10403.FStar_Syntax_Syntax.n in
                                       (match uu____10402 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10414;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10416;_}
                                            ->
                                            let prev =
                                              if i > (Prims.parse_int "1")
                                              then
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                  (i - (Prims.parse_int "1"))
                                              else
                                                FStar_Syntax_Syntax.Delta_constant in
                                            let t12 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11 in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t21 in
                                            disjoin t12 t22
                                        | uu____10423 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10436) ->
                  let uu____10461 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___135_10487  ->
                            match uu___135_10487 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10494 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10494 with
                                      | (u',uu____10510) ->
                                          let uu____10531 =
                                            let uu____10532 = whnf env u' in
                                            uu____10532.FStar_Syntax_Syntax.n in
                                          (match uu____10531 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10536) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10561 -> false))
                                 | uu____10562 -> false)
                            | uu____10565 -> false)) in
                  (match uu____10461 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10599 tps =
                         match uu____10599 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10647 =
                                    let uu____10656 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10656 in
                                  (match uu____10647 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10691 -> FStar_Pervasives_Native.None) in
                       let uu____10700 =
                         let uu____10709 =
                           let uu____10716 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10716, []) in
                         make_lower_bound uu____10709 lower_bounds in
                       (match uu____10700 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10728 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10728
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
                                "meeting refinements" in
                            ((let uu____10748 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10748
                              then
                                let wl' =
                                  let uu___163_10750 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___163_10750.wl_deferred);
                                    ctr = (uu___163_10750.ctr);
                                    defer_ok = (uu___163_10750.defer_ok);
                                    smt_ok = (uu___163_10750.smt_ok);
                                    tcenv = (uu___163_10750.tcenv)
                                  } in
                                let uu____10751 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10751
                              else ());
                             (let uu____10753 =
                                solve_t env eq_prob
                                  (let uu___164_10755 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___164_10755.wl_deferred);
                                     ctr = (uu___164_10755.ctr);
                                     defer_ok = (uu___164_10755.defer_ok);
                                     smt_ok = (uu___164_10755.smt_ok);
                                     tcenv = (uu___164_10755.tcenv)
                                   }) in
                              match uu____10753 with
                              | Success uu____10758 ->
                                  let wl1 =
                                    let uu___165_10760 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___165_10760.wl_deferred);
                                      ctr = (uu___165_10760.ctr);
                                      defer_ok = (uu___165_10760.defer_ok);
                                      smt_ok = (uu___165_10760.smt_ok);
                                      tcenv = (uu___165_10760.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10762 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10767 -> FStar_Pervasives_Native.None))))
              | uu____10768 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10777 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10777
         then
           let uu____10778 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10778
         else ());
        (let uu____10780 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10780 with
         | (u,args) ->
             let uu____10819 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10819 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10860 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10860 with
                    | (h1,args1) ->
                        let uu____10901 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10901 with
                         | (h2,uu____10921) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10948 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10948
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10966 =
                                          let uu____10969 =
                                            let uu____10970 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_55  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_55) uu____10970 in
                                          [uu____10969] in
                                        FStar_Pervasives_Native.Some
                                          uu____10966))
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
                                       (let uu____11003 =
                                          let uu____11006 =
                                            let uu____11007 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____11007 in
                                          [uu____11006] in
                                        FStar_Pervasives_Native.Some
                                          uu____11003))
                                  else FStar_Pervasives_Native.None
                              | uu____11021 -> FStar_Pervasives_Native.None)) in
                  let conjoin t1 t2 =
                    match ((t1.FStar_Syntax_Syntax.n),
                            (t2.FStar_Syntax_Syntax.n))
                    with
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,phi1),FStar_Syntax_Syntax.Tm_refine (y,phi2)) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort
                            y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let uu____11111 =
                               let uu____11120 =
                                 let uu____11123 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11123 in
                               (uu____11120, m1) in
                             FStar_Pervasives_Native.Some uu____11111)
                    | (uu____11136,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11138)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11186),uu____11187) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11234 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11287) ->
                       let uu____11312 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___136_11338  ->
                                 match uu___136_11338 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11345 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11345 with
                                           | (u',uu____11361) ->
                                               let uu____11382 =
                                                 let uu____11383 =
                                                   whnf env u' in
                                                 uu____11383.FStar_Syntax_Syntax.n in
                                               (match uu____11382 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11387) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11412 -> false))
                                      | uu____11413 -> false)
                                 | uu____11416 -> false)) in
                       (match uu____11312 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11454 tps =
                              match uu____11454 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11516 =
                                         let uu____11527 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11527 in
                                       (match uu____11516 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11578 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11589 =
                              let uu____11600 =
                                let uu____11609 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11609, []) in
                              make_upper_bound uu____11600 upper_bounds in
                            (match uu____11589 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11623 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11623
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
                                     "joining refinements" in
                                 ((let uu____11649 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11649
                                   then
                                     let wl' =
                                       let uu___166_11651 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___166_11651.wl_deferred);
                                         ctr = (uu___166_11651.ctr);
                                         defer_ok = (uu___166_11651.defer_ok);
                                         smt_ok = (uu___166_11651.smt_ok);
                                         tcenv = (uu___166_11651.tcenv)
                                       } in
                                     let uu____11652 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11652
                                   else ());
                                  (let uu____11654 =
                                     solve_t env eq_prob
                                       (let uu___167_11656 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___167_11656.wl_deferred);
                                          ctr = (uu___167_11656.ctr);
                                          defer_ok =
                                            (uu___167_11656.defer_ok);
                                          smt_ok = (uu___167_11656.smt_ok);
                                          tcenv = (uu___167_11656.tcenv)
                                        }) in
                                   match uu____11654 with
                                   | Success uu____11659 ->
                                       let wl1 =
                                         let uu___168_11661 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___168_11661.wl_deferred);
                                           ctr = (uu___168_11661.ctr);
                                           defer_ok =
                                             (uu___168_11661.defer_ok);
                                           smt_ok = (uu___168_11661.smt_ok);
                                           tcenv = (uu___168_11661.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11663 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11668 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11669 -> failwith "Impossible: Not a flex-rigid")))
and solve_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (FStar_Syntax_Syntax.binders ->
               FStar_TypeChecker_Env.env ->
                 FStar_Syntax_Syntax.subst_elt Prims.list ->
                   FStar_TypeChecker_Common.prob)
              -> solution
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
                    let rhs_prob = rhs (FStar_List.rev scope) env1 subst1 in
                    ((let uu____11760 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11760
                      then
                        let uu____11761 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11761
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___169_11815 = hd1 in
                      let uu____11816 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___169_11815.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___169_11815.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11816
                      } in
                    let hd21 =
                      let uu___170_11820 = hd2 in
                      let uu____11821 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___170_11820.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___170_11820.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11821
                      } in
                    let prob =
                      let uu____11825 =
                        let uu____11830 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11830 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_57  -> FStar_TypeChecker_Common.TProb _0_57)
                        uu____11825 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11841 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11841 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11845 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____11845 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11875 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11880 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11875 uu____11880 in
                         ((let uu____11890 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11890
                           then
                             let uu____11891 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11892 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11891 uu____11892
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11915 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11925 = aux scope env [] bs1 bs2 in
              match uu____11925 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11949 = compress_tprob wl problem in
        solve_t' env uu____11949 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11982 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11982 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____12013,uu____12014) ->
                   let rec may_relate head3 =
                     let uu____12039 =
                       let uu____12040 = FStar_Syntax_Subst.compress head3 in
                       uu____12040.FStar_Syntax_Syntax.n in
                     match uu____12039 with
                     | FStar_Syntax_Syntax.Tm_name uu____12043 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12044 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12067;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____12068;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12071;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12072;
                           FStar_Syntax_Syntax.fv_qual = uu____12073;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12077,uu____12078) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12120) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12126) ->
                         may_relate t
                     | uu____12131 -> false in
                   let uu____12132 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12132
                   then
                     let guard =
                       if
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                       then mk_eq2 env1 t1 t2
                       else
                         (let has_type_guard t11 t21 =
                            match problem.FStar_TypeChecker_Common.element
                            with
                            | FStar_Pervasives_Native.Some t ->
                                FStar_Syntax_Util.mk_has_type t11 t t21
                            | FStar_Pervasives_Native.None  ->
                                let x =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None t11 in
                                let u_x =
                                  env1.FStar_TypeChecker_Env.universe_of env1
                                    t11 in
                                let uu____12149 =
                                  let uu____12150 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12150 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12149 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12152 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12152
                   else
                     (let uu____12154 =
                        let uu____12155 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12156 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12155 uu____12156 in
                      giveup env1 uu____12154 orig)
               | (uu____12157,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___171_12171 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___171_12171.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___171_12171.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___171_12171.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___171_12171.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___171_12171.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___171_12171.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___171_12171.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___171_12171.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12172,FStar_Pervasives_Native.None ) ->
                   ((let uu____12184 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12184
                     then
                       let uu____12185 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12186 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12187 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12188 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12185
                         uu____12186 uu____12187 uu____12188
                     else ());
                    (let uu____12190 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12190 with
                     | (head11,args1) ->
                         let uu____12227 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12227 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12281 =
                                  let uu____12282 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12283 = args_to_string args1 in
                                  let uu____12284 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12285 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12282 uu____12283 uu____12284
                                    uu____12285 in
                                giveup env1 uu____12281 orig
                              else
                                (let uu____12287 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12293 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12293 = FStar_Syntax_Util.Equal) in
                                 if uu____12287
                                 then
                                   let uu____12294 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12294 with
                                   | USolved wl2 ->
                                       let uu____12296 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12296
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12300 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12300 with
                                    | (base1,refinement1) ->
                                        let uu____12337 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12337 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12418 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12418 with
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
                                                           (fun uu____12440 
                                                              ->
                                                              fun uu____12441
                                                                 ->
                                                                match 
                                                                  (uu____12440,
                                                                    uu____12441)
                                                                with
                                                                | ((a,uu____12459),
                                                                   (a',uu____12461))
                                                                    ->
                                                                    let uu____12470
                                                                    =
                                                                    mk_problem
                                                                    (p_scope
                                                                    orig)
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index" in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_58  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_58)
                                                                    uu____12470)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12480 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12480 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12486 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___172_12534 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___172_12534.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___172_12534.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___172_12534.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___172_12534.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___172_12534.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___172_12534.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___172_12534.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___172_12534.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12573 =
          match uu____12573 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12789  ->
                              match uu____12789 with
                              | (x,imp) ->
                                  let uu____12800 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12800, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12813 = FStar_Syntax_Util.type_u () in
                      match uu____12813 with
                      | (t1,uu____12819) ->
                          let uu____12820 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12820 in
                    let uu____12825 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12825 with
                     | (t',tm_u1) ->
                         let uu____12838 = destruct_flex_t t' in
                         (match uu____12838 with
                          | (uu____12875,u1,k1,uu____12878) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12937 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12937 in
                              let sol =
                                let uu____12941 =
                                  let uu____12950 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12950) in
                                TERM uu____12941 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____13086 = pat_var_opt env pat_args hd1 in
                    (match uu____13086 with
                     | FStar_Pervasives_Native.None  ->
                         aux pat_args pattern_vars pattern_var_set (formal ::
                           seen_formals) formals1 res_t tl1
                     | FStar_Pervasives_Native.Some y ->
                         let maybe_pat =
                           match xs_opt with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some xs ->
                               FStar_All.pipe_right xs
                                 (FStar_Util.for_some
                                    (fun uu____13149  ->
                                       match uu____13149 with
                                       | (x,uu____13155) ->
                                           FStar_Syntax_Syntax.bv_eq x
                                             (FStar_Pervasives_Native.fst y))) in
                         if Prims.op_Negation maybe_pat
                         then
                           aux pat_args pattern_vars pattern_var_set (formal
                             :: seen_formals) formals1 res_t tl1
                         else
                           (let fvs =
                              FStar_Syntax_Free.names
                                (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                            let uu____13170 =
                              let uu____13171 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____13171 in
                            if uu____13170
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____13183 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____13183 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____13198::uu____13199) ->
                    let uu____13230 =
                      let uu____13243 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____13243 in
                    (match uu____13230 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____13282 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____13289::uu____13290,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____13325 =
                let uu____13338 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13338 in
              (match uu____13325 with
               | (all_formals,res_t) ->
                   let uu____13363 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____13363 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13397 = lhs in
          match uu____13397 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13407 ->
                    let uu____13408 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13408 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13437 = p in
          match uu____13437 with
          | (((u,k),xs,c),ps,(h,uu____13448,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13530 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13530 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13553 = h gs_xs in
                     let uu____13554 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59) in
                     FStar_Syntax_Util.abs xs1 uu____13553 uu____13554 in
                   ((let uu____13560 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13560
                     then
                       let uu____13561 =
                         let uu____13564 =
                           let uu____13565 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13565
                             (FStar_String.concat "\n\t") in
                         let uu____13570 =
                           let uu____13573 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13574 =
                             let uu____13577 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13578 =
                               let uu____13581 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13582 =
                                 let uu____13585 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13586 =
                                   let uu____13589 =
                                     let uu____13590 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13590
                                       (FStar_String.concat ", ") in
                                   let uu____13595 =
                                     let uu____13598 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13598] in
                                   uu____13589 :: uu____13595 in
                                 uu____13585 :: uu____13586 in
                               uu____13581 :: uu____13582 in
                             uu____13577 :: uu____13578 in
                           uu____13573 :: uu____13574 in
                         uu____13564 :: uu____13570 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13561
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___137_13619 =
          match uu___137_13619 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13651 = p in
          match uu____13651 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13742 = FStar_List.nth ps i in
              (match uu____13742 with
               | (pi,uu____13746) ->
                   let uu____13751 = FStar_List.nth xs i in
                   (match uu____13751 with
                    | (xi,uu____13763) ->
                        let rec gs k =
                          let uu____13776 =
                            let uu____13789 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13789 in
                          match uu____13776 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13864)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13877 = new_uvar r xs k_a in
                                    (match uu____13877 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs in
                                         let gi_ps =
                                           FStar_Syntax_Syntax.mk_Tm_app gi
                                             ps FStar_Pervasives_Native.None
                                             r in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1 in
                                         let uu____13899 = aux subst2 tl1 in
                                         (match uu____13899 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13926 =
                                                let uu____13929 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13929 :: gi_xs' in
                                              let uu____13930 =
                                                let uu____13933 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13933 :: gi_ps' in
                                              (uu____13926, uu____13930))) in
                              aux [] bs in
                        let uu____13938 =
                          let uu____13939 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13939 in
                        if uu____13938
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13943 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13943 with
                           | (g_xs,uu____13955) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13966 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13967 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_60  ->
                                        FStar_Pervasives_Native.Some _0_60) in
                                 FStar_Syntax_Util.abs xs uu____13966
                                   uu____13967 in
                               let sub1 =
                                 let uu____13973 =
                                   let uu____13978 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13981 =
                                     let uu____13984 =
                                       FStar_List.map
                                         (fun uu____13999  ->
                                            match uu____13999 with
                                            | (uu____14008,uu____14009,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13984 in
                                   mk_problem (p_scope orig) orig uu____13978
                                     (p_rel orig) uu____13981
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____13973 in
                               ((let uu____14024 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14024
                                 then
                                   let uu____14025 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____14026 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14025 uu____14026
                                 else ());
                                (let wl2 =
                                   let uu____14029 =
                                     let uu____14032 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____14032 in
                                   solve_prob orig uu____14029
                                     [TERM (u, proj)] wl1 in
                                 let uu____14041 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____14041))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14072 = lhs in
          match uu____14072 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14108 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14108 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14141 =
                        let uu____14188 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14188) in
                      FStar_Pervasives_Native.Some uu____14141
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____14332 =
                           let uu____14339 =
                             let uu____14340 = FStar_Syntax_Subst.compress k1 in
                             uu____14340.FStar_Syntax_Syntax.n in
                           (uu____14339, args) in
                         match uu____14332 with
                         | (uu____14351,[]) ->
                             let uu____14354 =
                               let uu____14365 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14365) in
                             FStar_Pervasives_Native.Some uu____14354
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14386,uu____14387) ->
                             let uu____14408 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14408 with
                              | (uv1,uv_args) ->
                                  let uu____14451 =
                                    let uu____14452 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14452.FStar_Syntax_Syntax.n in
                                  (match uu____14451 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14462) ->
                                       let uu____14487 =
                                         pat_vars env [] uv_args in
                                       (match uu____14487 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14514  ->
                                                      let uu____14515 =
                                                        let uu____14516 =
                                                          let uu____14517 =
                                                            let uu____14522 =
                                                              let uu____14523
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14523
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14522 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14517 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14516 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14515)) in
                                            let c1 =
                                              let uu____14533 =
                                                let uu____14534 =
                                                  let uu____14539 =
                                                    let uu____14540 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14540
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14539 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14534 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14533 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14553 =
                                                let uu____14556 =
                                                  let uu____14557 =
                                                    let uu____14560 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14560
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14557 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14556 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14553 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14578 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14583,uu____14584) ->
                             let uu____14603 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14603 with
                              | (uv1,uv_args) ->
                                  let uu____14646 =
                                    let uu____14647 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14647.FStar_Syntax_Syntax.n in
                                  (match uu____14646 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14657) ->
                                       let uu____14682 =
                                         pat_vars env [] uv_args in
                                       (match uu____14682 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14709  ->
                                                      let uu____14710 =
                                                        let uu____14711 =
                                                          let uu____14712 =
                                                            let uu____14717 =
                                                              let uu____14718
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14718
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14717 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14712 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14711 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14710)) in
                                            let c1 =
                                              let uu____14728 =
                                                let uu____14729 =
                                                  let uu____14734 =
                                                    let uu____14735 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14735
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14734 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14729 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14728 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14748 =
                                                let uu____14751 =
                                                  let uu____14752 =
                                                    let uu____14755 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14755
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14752 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14751 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14748 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14773 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14780) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14821 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14821
                                 (fun _0_63  ->
                                    FStar_Pervasives_Native.Some _0_63)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14857 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14857 with
                                  | (args1,rest) ->
                                      let uu____14886 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14886 with
                                       | (xs2,c2) ->
                                           let uu____14899 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14899
                                             (fun uu____14923  ->
                                                match uu____14923 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14963 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14963 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____15031 =
                                        let uu____15036 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15036 in
                                      FStar_All.pipe_right uu____15031
                                        (fun _0_64  ->
                                           FStar_Pervasives_Native.Some _0_64))
                         | uu____15051 ->
                             let uu____15058 =
                               let uu____15059 =
                                 let uu____15064 =
                                   let uu____15065 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____15066 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____15067 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____15065 uu____15066 uu____15067 in
                                 (uu____15064, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____15059 in
                             FStar_Exn.raise uu____15058 in
                       let uu____15074 = elim k_uv ps in
                       FStar_Util.bind_opt uu____15074
                         (fun uu____15129  ->
                            match uu____15129 with
                            | (xs1,c1) ->
                                let uu____15178 =
                                  let uu____15219 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15219) in
                                FStar_Pervasives_Native.Some uu____15178)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15340 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15356 = project orig env wl1 i st in
                     match uu____15356 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15370) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15385 = imitate orig env wl1 st in
                  match uu____15385 with
                  | Failed uu____15390 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15421 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15421 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15446 =
                      let uu____15447 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15447 wl2 in
                    (match uu____15446 with
                     | Failed uu____15448 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15466 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15466 with
                | (hd1,uu____15482) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15503 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15516 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15517 -> true
                     | uu____15534 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15538 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15538
                         then true
                         else
                           ((let uu____15541 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15541
                             then
                               let uu____15542 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____15542
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15562 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15562 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15575 =
                            let uu____15576 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15576 in
                          giveup_or_defer1 orig uu____15575
                        else
                          (let uu____15578 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15578
                           then
                             let uu____15579 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15579
                              then
                                let uu____15580 = subterms args_lhs in
                                imitate' orig env wl1 uu____15580
                              else
                                ((let uu____15585 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15585
                                  then
                                    let uu____15586 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15587 = names_to_string fvs1 in
                                    let uu____15588 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15586 uu____15587 uu____15588
                                  else ());
                                 use_pattern_equality orig env wl1 lhs1 vars
                                   t21))
                           else
                             if
                               ((Prims.op_Negation patterns_only) &&
                                  wl1.defer_ok)
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                             then
                               solve env
                                 (defer
                                    "flex pattern/rigid: occurs or freevar check"
                                    orig wl1)
                             else
                               (let uu____15592 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15592
                                then
                                  ((let uu____15594 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15594
                                    then
                                      let uu____15595 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15596 = names_to_string fvs1 in
                                      let uu____15597 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15595 uu____15596 uu____15597
                                    else ());
                                   (let uu____15599 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15599))
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
                     (let uu____15610 =
                        let uu____15611 = FStar_Syntax_Free.names t1 in
                        check_head uu____15611 t2 in
                      if uu____15610
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15622 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15622
                          then
                            let uu____15623 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15624 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15623 uu____15624
                          else ());
                         (let uu____15632 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15632))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15709 uu____15710 r =
               match (uu____15709, uu____15710) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15908 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15908
                   then
                     let uu____15909 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15909
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15933 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15933
                       then
                         let uu____15934 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15935 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15936 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15937 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15938 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15934 uu____15935 uu____15936 uu____15937
                           uu____15938
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15998 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15998 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____16012 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____16012 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16066 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16066 in
                                  let uu____16069 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____16069 k3)
                           else
                             (let uu____16073 =
                                let uu____16074 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____16075 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____16076 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16074 uu____16075 uu____16076 in
                              failwith uu____16073) in
                       let uu____16077 =
                         let uu____16084 =
                           let uu____16097 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____16097 in
                         match uu____16084 with
                         | (bs,k1') ->
                             let uu____16122 =
                               let uu____16135 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____16135 in
                             (match uu____16122 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____16163 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      uu____16163 in
                                  let uu____16172 =
                                    let uu____16177 =
                                      let uu____16178 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____16178.FStar_Syntax_Syntax.n in
                                    let uu____16181 =
                                      let uu____16182 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____16182.FStar_Syntax_Syntax.n in
                                    (uu____16177, uu____16181) in
                                  (match uu____16172 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16191,uu____16192) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16195,FStar_Syntax_Syntax.Tm_type
                                      uu____16196) -> (k2'_ys, [sub_prob])
                                   | uu____16199 ->
                                       let uu____16204 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____16204 with
                                        | (t,uu____16216) ->
                                            let uu____16217 = new_uvar r zs t in
                                            (match uu____16217 with
                                             | (k_zs,uu____16229) ->
                                                 let kprob =
                                                   let uu____16231 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_66  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_66) uu____16231 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____16077 with
                       | (k_u',sub_probs) ->
                           let uu____16248 =
                             let uu____16259 =
                               let uu____16260 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16260 in
                             let uu____16269 =
                               let uu____16272 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16272 in
                             let uu____16275 =
                               let uu____16278 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16278 in
                             (uu____16259, uu____16269, uu____16275) in
                           (match uu____16248 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16297 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16297 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16316 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16316
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16320 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16320 with
                                           | (occurs_ok1,msg1) ->
                                               if
                                                 Prims.op_Negation occurs_ok1
                                               then
                                                 giveup_or_defer1 orig
                                                   "flex-flex: failed occurs check"
                                               else
                                                 (let sol2 =
                                                    TERM ((u2, k2), sub2) in
                                                  let wl2 =
                                                    solve_prob orig
                                                      FStar_Pervasives_Native.None
                                                      [sol1; sol2] wl1 in
                                                  solve env
                                                    (attempt sub_probs wl2)))))))) in
             let solve_one_pat uu____16373 uu____16374 =
               match (uu____16373, uu____16374) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16492 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16492
                     then
                       let uu____16493 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16494 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16493 uu____16494
                     else ());
                    (let uu____16496 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16496
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16515  ->
                              fun uu____16516  ->
                                match (uu____16515, uu____16516) with
                                | ((a,uu____16534),(t21,uu____16536)) ->
                                    let uu____16545 =
                                      let uu____16550 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16550
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16545
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67))
                           xs args2 in
                       let guard =
                         let uu____16556 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16556 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16571 = occurs_check env wl (u1, k1) t21 in
                        match uu____16571 with
                        | (occurs_ok,uu____16579) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16587 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16587
                            then
                              let sol =
                                let uu____16589 =
                                  let uu____16598 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16598) in
                                TERM uu____16589 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16605 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16605
                               then
                                 let uu____16606 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16606 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16630,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16656 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16656
                                       then
                                         let uu____16657 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16657
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16664 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16666 = lhs in
             match uu____16666 with
             | (t1,u1,k1,args1) ->
                 let uu____16671 = rhs in
                 (match uu____16671 with
                  | (t2,u2,k2,args2) ->
                      let maybe_pat_vars1 = pat_vars env [] args1 in
                      let maybe_pat_vars2 = pat_vars env [] args2 in
                      let r = t2.FStar_Syntax_Syntax.pos in
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
                       | uu____16711 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16721 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16721 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16739) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16746 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16746
                                    then
                                      let uu____16747 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16747
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16754 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16756 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16756
        then
          let uu____16757 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16757
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16761 = FStar_Util.physical_equality t1 t2 in
           if uu____16761
           then
             let uu____16762 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16762
           else
             ((let uu____16765 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16765
               then
                 let uu____16766 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16766
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16769,uu____16770) ->
                   let uu____16797 =
                     let uu___173_16798 = problem in
                     let uu____16799 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___173_16798.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16799;
                       FStar_TypeChecker_Common.relation =
                         (uu___173_16798.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___173_16798.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___173_16798.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___173_16798.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___173_16798.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___173_16798.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___173_16798.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___173_16798.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16797 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16800,uu____16801) ->
                   let uu____16808 =
                     let uu___173_16809 = problem in
                     let uu____16810 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___173_16809.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16810;
                       FStar_TypeChecker_Common.relation =
                         (uu___173_16809.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___173_16809.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___173_16809.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___173_16809.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___173_16809.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___173_16809.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___173_16809.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___173_16809.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16808 wl
               | (uu____16811,FStar_Syntax_Syntax.Tm_ascribed uu____16812) ->
                   let uu____16839 =
                     let uu___174_16840 = problem in
                     let uu____16841 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___174_16840.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___174_16840.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___174_16840.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16841;
                       FStar_TypeChecker_Common.element =
                         (uu___174_16840.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___174_16840.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___174_16840.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___174_16840.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___174_16840.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___174_16840.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16839 wl
               | (uu____16842,FStar_Syntax_Syntax.Tm_meta uu____16843) ->
                   let uu____16850 =
                     let uu___174_16851 = problem in
                     let uu____16852 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___174_16851.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___174_16851.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___174_16851.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16852;
                       FStar_TypeChecker_Common.element =
                         (uu___174_16851.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___174_16851.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___174_16851.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___174_16851.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___174_16851.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___174_16851.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16850 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16853,uu____16854) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16855,FStar_Syntax_Syntax.Tm_bvar uu____16856) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___138_16911 =
                     match uu___138_16911 with
                     | [] -> c
                     | bs ->
                         let uu____16933 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16933 in
                   let uu____16942 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16942 with
                    | ((bs11,c11),(bs21,c21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let c12 =
                                   FStar_Syntax_Subst.subst_comp subst1 c11 in
                                 let c22 =
                                   FStar_Syntax_Subst.subst_comp subst1 c21 in
                                 let rel =
                                   let uu____17084 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____17084
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____17086 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.CProb _0_68)
                                   uu____17086))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___139_17162 =
                     match uu___139_17162 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____17196 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____17196 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17332 =
                                   let uu____17337 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17338 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17337
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17338 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17332))
               | (FStar_Syntax_Syntax.Tm_abs uu____17343,uu____17344) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17369 -> true
                     | uu____17386 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17420 =
                     let uu____17437 = maybe_eta t1 in
                     let uu____17444 = maybe_eta t2 in
                     (uu____17437, uu____17444) in
                   (match uu____17420 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___175_17486 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___175_17486.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___175_17486.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___175_17486.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___175_17486.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___175_17486.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___175_17486.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___175_17486.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___175_17486.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17509 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17509
                        then
                          let uu____17510 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17510 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17538 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17538
                        then
                          let uu____17539 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17539 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17547 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17564,FStar_Syntax_Syntax.Tm_abs uu____17565) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17590 -> true
                     | uu____17607 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17641 =
                     let uu____17658 = maybe_eta t1 in
                     let uu____17665 = maybe_eta t2 in
                     (uu____17658, uu____17665) in
                   (match uu____17641 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___175_17707 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___175_17707.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___175_17707.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___175_17707.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___175_17707.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___175_17707.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___175_17707.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___175_17707.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___175_17707.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17730 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17730
                        then
                          let uu____17731 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17731 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17759 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17759
                        then
                          let uu____17760 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17760 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17768 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17785,FStar_Syntax_Syntax.Tm_refine uu____17786) ->
                   let uu____17799 = as_refinement env wl t1 in
                   (match uu____17799 with
                    | (x1,phi1) ->
                        let uu____17806 = as_refinement env wl t2 in
                        (match uu____17806 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17814 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_70  ->
                                    FStar_TypeChecker_Common.TProb _0_70)
                                 uu____17814 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17852 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17852
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17856 =
                               let impl =
                                 if
                                   problem.FStar_TypeChecker_Common.relation
                                     = FStar_TypeChecker_Common.EQ
                                 then
                                   mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                     phi21
                                 else
                                   mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                     phi21 in
                               let guard =
                                 let uu____17862 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17862 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17871 =
                                   let uu____17876 =
                                     let uu____17877 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____17877 :: (p_scope orig) in
                                   mk_problem uu____17876 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.TProb _0_71)
                                   uu____17871 in
                               let uu____17882 =
                                 solve env1
                                   (let uu___176_17884 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___176_17884.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___176_17884.smt_ok);
                                      tcenv = (uu___176_17884.tcenv)
                                    }) in
                               (match uu____17882 with
                                | Failed uu____17891 -> fallback ()
                                | Success uu____17896 ->
                                    let guard =
                                      let uu____17900 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17905 =
                                        let uu____17906 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17906
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17900
                                        uu____17905 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___177_17915 = wl1 in
                                      {
                                        attempting =
                                          (uu___177_17915.attempting);
                                        wl_deferred =
                                          (uu___177_17915.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___177_17915.defer_ok);
                                        smt_ok = (uu___177_17915.smt_ok);
                                        tcenv = (uu___177_17915.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17917,FStar_Syntax_Syntax.Tm_uvar uu____17918) ->
                   let uu____17951 = destruct_flex_t t1 in
                   let uu____17952 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17951 uu____17952
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17953;
                     FStar_Syntax_Syntax.pos = uu____17954;
                     FStar_Syntax_Syntax.vars = uu____17955;_},uu____17956),FStar_Syntax_Syntax.Tm_uvar
                  uu____17957) ->
                   let uu____18010 = destruct_flex_t t1 in
                   let uu____18011 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18010 uu____18011
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18012,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18013;
                     FStar_Syntax_Syntax.pos = uu____18014;
                     FStar_Syntax_Syntax.vars = uu____18015;_},uu____18016))
                   ->
                   let uu____18069 = destruct_flex_t t1 in
                   let uu____18070 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18069 uu____18070
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18071;
                     FStar_Syntax_Syntax.pos = uu____18072;
                     FStar_Syntax_Syntax.vars = uu____18073;_},uu____18074),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18075;
                     FStar_Syntax_Syntax.pos = uu____18076;
                     FStar_Syntax_Syntax.vars = uu____18077;_},uu____18078))
                   ->
                   let uu____18151 = destruct_flex_t t1 in
                   let uu____18152 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18151 uu____18152
               | (FStar_Syntax_Syntax.Tm_uvar uu____18153,uu____18154) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18171 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18171 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18178;
                     FStar_Syntax_Syntax.pos = uu____18179;
                     FStar_Syntax_Syntax.vars = uu____18180;_},uu____18181),uu____18182)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18219 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18219 t2 wl
               | (uu____18226,FStar_Syntax_Syntax.Tm_uvar uu____18227) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18244,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18245;
                     FStar_Syntax_Syntax.pos = uu____18246;
                     FStar_Syntax_Syntax.vars = uu____18247;_},uu____18248))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18285,FStar_Syntax_Syntax.Tm_type uu____18286) ->
                   solve_t' env
                     (let uu___178_18304 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___178_18304.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___178_18304.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___178_18304.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___178_18304.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___178_18304.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___178_18304.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___178_18304.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___178_18304.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___178_18304.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18305;
                     FStar_Syntax_Syntax.pos = uu____18306;
                     FStar_Syntax_Syntax.vars = uu____18307;_},uu____18308),FStar_Syntax_Syntax.Tm_type
                  uu____18309) ->
                   solve_t' env
                     (let uu___178_18347 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___178_18347.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___178_18347.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___178_18347.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___178_18347.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___178_18347.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___178_18347.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___178_18347.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___178_18347.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___178_18347.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18348,FStar_Syntax_Syntax.Tm_arrow uu____18349) ->
                   solve_t' env
                     (let uu___178_18379 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___178_18379.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___178_18379.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___178_18379.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___178_18379.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___178_18379.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___178_18379.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___178_18379.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___178_18379.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___178_18379.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18380;
                     FStar_Syntax_Syntax.pos = uu____18381;
                     FStar_Syntax_Syntax.vars = uu____18382;_},uu____18383),FStar_Syntax_Syntax.Tm_arrow
                  uu____18384) ->
                   solve_t' env
                     (let uu___178_18434 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___178_18434.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___178_18434.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___178_18434.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___178_18434.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___178_18434.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___178_18434.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___178_18434.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___178_18434.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___178_18434.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18435,uu____18436) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18455 =
                        let uu____18456 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18456 in
                      if uu____18455
                      then
                        let uu____18457 =
                          FStar_All.pipe_left
                            (fun _0_72  ->
                               FStar_TypeChecker_Common.TProb _0_72)
                            (let uu___179_18463 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___179_18463.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___179_18463.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___179_18463.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___179_18463.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___179_18463.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___179_18463.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___179_18463.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___179_18463.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___179_18463.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18464 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18457 uu____18464 t2
                          wl
                      else
                        (let uu____18472 = base_and_refinement env wl t2 in
                         match uu____18472 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18515 =
                                    FStar_All.pipe_left
                                      (fun _0_73  ->
                                         FStar_TypeChecker_Common.TProb _0_73)
                                      (let uu___180_18521 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___180_18521.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___180_18521.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___180_18521.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___180_18521.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___180_18521.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___180_18521.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___180_18521.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___180_18521.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___180_18521.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18522 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18515
                                    uu____18522 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___181_18542 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___181_18542.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___181_18542.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18545 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      uu____18545 in
                                  let guard =
                                    let uu____18557 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18557
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18565;
                     FStar_Syntax_Syntax.pos = uu____18566;
                     FStar_Syntax_Syntax.vars = uu____18567;_},uu____18568),uu____18569)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18608 =
                        let uu____18609 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18609 in
                      if uu____18608
                      then
                        let uu____18610 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___179_18616 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___179_18616.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___179_18616.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___179_18616.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___179_18616.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___179_18616.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___179_18616.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___179_18616.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___179_18616.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___179_18616.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18617 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18610 uu____18617 t2
                          wl
                      else
                        (let uu____18625 = base_and_refinement env wl t2 in
                         match uu____18625 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18668 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___180_18674 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___180_18674.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___180_18674.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___180_18674.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___180_18674.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___180_18674.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___180_18674.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___180_18674.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___180_18674.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___180_18674.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18675 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18668
                                    uu____18675 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___181_18695 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___181_18695.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___181_18695.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18698 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____18698 in
                                  let guard =
                                    let uu____18710 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18710
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18718,FStar_Syntax_Syntax.Tm_uvar uu____18719) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18737 = base_and_refinement env wl t1 in
                      match uu____18737 with
                      | (t_base,uu____18753) ->
                          solve_t env
                            (let uu___182_18775 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___182_18775.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___182_18775.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___182_18775.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___182_18775.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___182_18775.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___182_18775.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___182_18775.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___182_18775.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18778,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18779;
                     FStar_Syntax_Syntax.pos = uu____18780;
                     FStar_Syntax_Syntax.vars = uu____18781;_},uu____18782))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18820 = base_and_refinement env wl t1 in
                      match uu____18820 with
                      | (t_base,uu____18836) ->
                          solve_t env
                            (let uu___182_18858 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___182_18858.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___182_18858.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___182_18858.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___182_18858.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___182_18858.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___182_18858.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___182_18858.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___182_18858.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18861,uu____18862) ->
                   let t21 =
                     let uu____18872 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____18872 in
                   solve_t env
                     (let uu___183_18896 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___183_18896.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___183_18896.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___183_18896.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___183_18896.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___183_18896.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___183_18896.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___183_18896.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___183_18896.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___183_18896.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18897,FStar_Syntax_Syntax.Tm_refine uu____18898) ->
                   let t11 =
                     let uu____18908 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____18908 in
                   solve_t env
                     (let uu___184_18932 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___184_18932.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___184_18932.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___184_18932.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___184_18932.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___184_18932.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___184_18932.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___184_18932.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___184_18932.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___184_18932.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18935,uu____18936) ->
                   let head1 =
                     let uu____18962 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18962
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19006 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19006
                       FStar_Pervasives_Native.fst in
                   let uu____19047 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19047
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19062 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19062
                      then
                        let guard =
                          let uu____19074 =
                            let uu____19075 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19075 = FStar_Syntax_Util.Equal in
                          if uu____19074
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19079 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19079) in
                        let uu____19082 = solve_prob orig guard [] wl in
                        solve env uu____19082
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19085,uu____19086) ->
                   let head1 =
                     let uu____19096 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19096
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19140 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19140
                       FStar_Pervasives_Native.fst in
                   let uu____19181 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19181
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19196 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19196
                      then
                        let guard =
                          let uu____19208 =
                            let uu____19209 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19209 = FStar_Syntax_Util.Equal in
                          if uu____19208
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19213 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19213) in
                        let uu____19216 = solve_prob orig guard [] wl in
                        solve env uu____19216
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19219,uu____19220) ->
                   let head1 =
                     let uu____19224 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19224
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19268 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19268
                       FStar_Pervasives_Native.fst in
                   let uu____19309 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19309
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19324 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19324
                      then
                        let guard =
                          let uu____19336 =
                            let uu____19337 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19337 = FStar_Syntax_Util.Equal in
                          if uu____19336
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19341 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19341) in
                        let uu____19344 = solve_prob orig guard [] wl in
                        solve env uu____19344
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19347,uu____19348) ->
                   let head1 =
                     let uu____19352 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19352
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19396 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19396
                       FStar_Pervasives_Native.fst in
                   let uu____19437 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19437
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19452 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19452
                      then
                        let guard =
                          let uu____19464 =
                            let uu____19465 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19465 = FStar_Syntax_Util.Equal in
                          if uu____19464
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19469 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19469) in
                        let uu____19472 = solve_prob orig guard [] wl in
                        solve env uu____19472
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19475,uu____19476) ->
                   let head1 =
                     let uu____19480 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19480
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19524 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19524
                       FStar_Pervasives_Native.fst in
                   let uu____19565 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19565
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19580 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19580
                      then
                        let guard =
                          let uu____19592 =
                            let uu____19593 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19593 = FStar_Syntax_Util.Equal in
                          if uu____19592
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19597 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19597) in
                        let uu____19600 = solve_prob orig guard [] wl in
                        solve env uu____19600
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19603,uu____19604) ->
                   let head1 =
                     let uu____19622 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19622
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19666 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19666
                       FStar_Pervasives_Native.fst in
                   let uu____19707 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19707
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19722 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19722
                      then
                        let guard =
                          let uu____19734 =
                            let uu____19735 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19735 = FStar_Syntax_Util.Equal in
                          if uu____19734
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19739 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19739) in
                        let uu____19742 = solve_prob orig guard [] wl in
                        solve env uu____19742
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19745,FStar_Syntax_Syntax.Tm_match uu____19746) ->
                   let head1 =
                     let uu____19772 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19772
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19816 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19816
                       FStar_Pervasives_Native.fst in
                   let uu____19857 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19857
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19872 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19872
                      then
                        let guard =
                          let uu____19884 =
                            let uu____19885 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19885 = FStar_Syntax_Util.Equal in
                          if uu____19884
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19889 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19889) in
                        let uu____19892 = solve_prob orig guard [] wl in
                        solve env uu____19892
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19895,FStar_Syntax_Syntax.Tm_uinst uu____19896) ->
                   let head1 =
                     let uu____19906 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19906
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19950 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19950
                       FStar_Pervasives_Native.fst in
                   let uu____19991 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19991
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20006 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20006
                      then
                        let guard =
                          let uu____20018 =
                            let uu____20019 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20019 = FStar_Syntax_Util.Equal in
                          if uu____20018
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20023 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20023) in
                        let uu____20026 = solve_prob orig guard [] wl in
                        solve env uu____20026
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20029,FStar_Syntax_Syntax.Tm_name uu____20030) ->
                   let head1 =
                     let uu____20034 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20034
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20078 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20078
                       FStar_Pervasives_Native.fst in
                   let uu____20119 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20119
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20134 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20134
                      then
                        let guard =
                          let uu____20146 =
                            let uu____20147 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20147 = FStar_Syntax_Util.Equal in
                          if uu____20146
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20151 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20151) in
                        let uu____20154 = solve_prob orig guard [] wl in
                        solve env uu____20154
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20157,FStar_Syntax_Syntax.Tm_constant uu____20158) ->
                   let head1 =
                     let uu____20162 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20162
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20206 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20206
                       FStar_Pervasives_Native.fst in
                   let uu____20247 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20247
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20262 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20262
                      then
                        let guard =
                          let uu____20274 =
                            let uu____20275 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20275 = FStar_Syntax_Util.Equal in
                          if uu____20274
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20279 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20279) in
                        let uu____20282 = solve_prob orig guard [] wl in
                        solve env uu____20282
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20285,FStar_Syntax_Syntax.Tm_fvar uu____20286) ->
                   let head1 =
                     let uu____20290 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20290
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20334 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20334
                       FStar_Pervasives_Native.fst in
                   let uu____20375 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20375
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20390 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20390
                      then
                        let guard =
                          let uu____20402 =
                            let uu____20403 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20403 = FStar_Syntax_Util.Equal in
                          if uu____20402
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20407 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_88  ->
                                  FStar_Pervasives_Native.Some _0_88)
                               uu____20407) in
                        let uu____20410 = solve_prob orig guard [] wl in
                        solve env uu____20410
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20413,FStar_Syntax_Syntax.Tm_app uu____20414) ->
                   let head1 =
                     let uu____20432 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20432
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20476 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20476
                       FStar_Pervasives_Native.fst in
                   let uu____20517 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20517
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20532 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20532
                      then
                        let guard =
                          let uu____20544 =
                            let uu____20545 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20545 = FStar_Syntax_Util.Equal in
                          if uu____20544
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20549 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_Pervasives_Native.Some _0_89)
                               uu____20549) in
                        let uu____20552 = solve_prob orig guard [] wl in
                        solve env uu____20552
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20555,uu____20556) ->
                   let uu____20569 =
                     let uu____20570 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20571 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20570
                       uu____20571 in
                   failwith uu____20569
               | (FStar_Syntax_Syntax.Tm_delayed uu____20572,uu____20573) ->
                   let uu____20598 =
                     let uu____20599 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20600 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20599
                       uu____20600 in
                   failwith uu____20598
               | (uu____20601,FStar_Syntax_Syntax.Tm_delayed uu____20602) ->
                   let uu____20627 =
                     let uu____20628 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20629 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20628
                       uu____20629 in
                   failwith uu____20627
               | (uu____20630,FStar_Syntax_Syntax.Tm_let uu____20631) ->
                   let uu____20644 =
                     let uu____20645 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20646 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20645
                       uu____20646 in
                   failwith uu____20644
               | uu____20647 -> giveup env "head tag mismatch" orig)))
and solve_c:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem ->
      worklist -> solution
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs in
        let c2 = problem.FStar_TypeChecker_Common.rhs in
        let orig = FStar_TypeChecker_Common.CProb problem in
        let sub_prob t1 rel t2 reason =
          mk_problem (p_scope orig) orig t1 rel t2
            FStar_Pervasives_Native.None reason in
        let solve_eq c1_comp c2_comp =
          (let uu____20683 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20683
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20685 =
               let uu____20686 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20687 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20686 uu____20687 in
             giveup env uu____20685 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20707  ->
                    fun uu____20708  ->
                      match (uu____20707, uu____20708) with
                      | ((a1,uu____20726),(a2,uu____20728)) ->
                          let uu____20737 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_90  ->
                               FStar_TypeChecker_Common.TProb _0_90)
                            uu____20737)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20747 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20747 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20771 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20778)::[] -> wp1
              | uu____20795 ->
                  let uu____20804 =
                    let uu____20805 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20805 in
                  failwith uu____20804 in
            let uu____20808 =
              let uu____20817 =
                let uu____20818 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20818 in
              [uu____20817] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20808;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20819 = lift_c1 () in solve_eq uu____20819 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___140_20825  ->
                       match uu___140_20825 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20826 -> false)) in
             let uu____20827 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20861)::uu____20862,(wp2,uu____20864)::uu____20865)
                   -> (wp1, wp2)
               | uu____20922 ->
                   let uu____20943 =
                     let uu____20944 =
                       let uu____20949 =
                         let uu____20950 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20951 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20950 uu____20951 in
                       (uu____20949, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20944 in
                   FStar_Exn.raise uu____20943 in
             match uu____20827 with
             | (wpc1,wpc2) ->
                 let uu____20970 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20970
                 then
                   let uu____20973 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20973 wl
                 else
                   (let uu____20977 =
                      let uu____20984 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20984 in
                    match uu____20977 with
                    | (c2_decl,qualifiers) ->
                        let uu____21005 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____21005
                        then
                          let c1_repr =
                            let uu____21009 =
                              let uu____21010 =
                                let uu____21011 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____21011 in
                              let uu____21012 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21010 uu____21012 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____21009 in
                          let c2_repr =
                            let uu____21014 =
                              let uu____21015 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____21016 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21015 uu____21016 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____21014 in
                          let prob =
                            let uu____21018 =
                              let uu____21023 =
                                let uu____21024 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____21025 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21024
                                  uu____21025 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21023 in
                            FStar_TypeChecker_Common.TProb uu____21018 in
                          let wl1 =
                            let uu____21027 =
                              let uu____21030 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____21030 in
                            solve_prob orig uu____21027 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21039 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____21039
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____21041 =
                                     let uu____21044 =
                                       let uu____21045 =
                                         let uu____21060 =
                                           let uu____21061 =
                                             let uu____21062 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____21062] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____21061 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21063 =
                                           let uu____21066 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21067 =
                                             let uu____21070 =
                                               let uu____21071 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21071 in
                                             [uu____21070] in
                                           uu____21066 :: uu____21067 in
                                         (uu____21060, uu____21063) in
                                       FStar_Syntax_Syntax.Tm_app uu____21045 in
                                     FStar_Syntax_Syntax.mk uu____21044 in
                                   uu____21041 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____21078 =
                                    let uu____21081 =
                                      let uu____21082 =
                                        let uu____21097 =
                                          let uu____21098 =
                                            let uu____21099 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____21099] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____21098 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21100 =
                                          let uu____21103 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21104 =
                                            let uu____21107 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21108 =
                                              let uu____21111 =
                                                let uu____21112 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21112 in
                                              [uu____21111] in
                                            uu____21107 :: uu____21108 in
                                          uu____21103 :: uu____21104 in
                                        (uu____21097, uu____21100) in
                                      FStar_Syntax_Syntax.Tm_app uu____21082 in
                                    FStar_Syntax_Syntax.mk uu____21081 in
                                  uu____21078 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21119 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_91  ->
                                  FStar_TypeChecker_Common.TProb _0_91)
                               uu____21119 in
                           let wl1 =
                             let uu____21129 =
                               let uu____21132 =
                                 let uu____21135 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21135 g in
                               FStar_All.pipe_left
                                 (fun _0_92  ->
                                    FStar_Pervasives_Native.Some _0_92)
                                 uu____21132 in
                             solve_prob orig uu____21129 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21148 = FStar_Util.physical_equality c1 c2 in
        if uu____21148
        then
          let uu____21149 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21149
        else
          ((let uu____21152 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21152
            then
              let uu____21153 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21154 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21153
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21154
            else ());
           (let uu____21156 =
              let uu____21161 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21162 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21161, uu____21162) in
            match uu____21156 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21166),FStar_Syntax_Syntax.Total
                    (t2,uu____21168)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21185 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21185 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21188,FStar_Syntax_Syntax.Total uu____21189) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21207),FStar_Syntax_Syntax.Total
                    (t2,uu____21209)) ->
                     let uu____21226 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21226 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21230),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21232)) ->
                     let uu____21249 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21249 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21253),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21255)) ->
                     let uu____21272 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21272 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21275,FStar_Syntax_Syntax.Comp uu____21276) ->
                     let uu____21285 =
                       let uu___185_21290 = problem in
                       let uu____21295 =
                         let uu____21296 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21296 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___185_21290.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21295;
                         FStar_TypeChecker_Common.relation =
                           (uu___185_21290.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___185_21290.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___185_21290.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___185_21290.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___185_21290.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___185_21290.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___185_21290.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___185_21290.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21285 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21297,FStar_Syntax_Syntax.Comp uu____21298) ->
                     let uu____21307 =
                       let uu___185_21312 = problem in
                       let uu____21317 =
                         let uu____21318 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21318 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___185_21312.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21317;
                         FStar_TypeChecker_Common.relation =
                           (uu___185_21312.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___185_21312.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___185_21312.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___185_21312.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___185_21312.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___185_21312.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___185_21312.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___185_21312.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21307 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21319,FStar_Syntax_Syntax.GTotal uu____21320) ->
                     let uu____21329 =
                       let uu___186_21334 = problem in
                       let uu____21339 =
                         let uu____21340 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21340 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___186_21334.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___186_21334.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___186_21334.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21339;
                         FStar_TypeChecker_Common.element =
                           (uu___186_21334.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___186_21334.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___186_21334.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___186_21334.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___186_21334.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___186_21334.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21329 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21341,FStar_Syntax_Syntax.Total uu____21342) ->
                     let uu____21351 =
                       let uu___186_21356 = problem in
                       let uu____21361 =
                         let uu____21362 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21362 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___186_21356.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___186_21356.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___186_21356.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21361;
                         FStar_TypeChecker_Common.element =
                           (uu___186_21356.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___186_21356.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___186_21356.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___186_21356.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___186_21356.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___186_21356.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21351 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21363,FStar_Syntax_Syntax.Comp uu____21364) ->
                     let uu____21365 =
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
                               FStar_TypeChecker_Common.SUB)) in
                     if uu____21365
                     then
                       let uu____21366 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21366 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21372 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21382 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21383 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21382, uu____21383)) in
                          match uu____21372 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21390 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21390
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21392 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21392 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21395 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21397 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21397) in
                                if uu____21395
                                then
                                  let edge =
                                    {
                                      FStar_TypeChecker_Env.msource =
                                        (c12.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mtarget =
                                        (c22.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mlift =
                                        FStar_TypeChecker_Env.identity_mlift
                                    } in
                                  solve_sub c12 edge c22
                                else
                                  (let uu____21400 =
                                     let uu____21401 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21402 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21401 uu____21402 in
                                   giveup env uu____21400 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21408 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21446  ->
              match uu____21446 with
              | (uu____21459,uu____21460,u,uu____21462,uu____21463,uu____21464)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21408 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21496 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21496 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21514 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21542  ->
                match uu____21542 with
                | (u1,u2) ->
                    let uu____21549 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21550 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21549 uu____21550)) in
      FStar_All.pipe_right uu____21514 (FStar_String.concat ", ") in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
let guard_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21569,[])) -> "{}"
      | uu____21594 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21611 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21611
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21614 =
              FStar_List.map
                (fun uu____21624  ->
                   match uu____21624 with
                   | (uu____21629,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21614 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21634 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21634 imps
let new_t_problem:
  'Auu____21649 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21649 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21649)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21683 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21683
                then
                  let uu____21684 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21685 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21684
                    (rel_to_string rel) uu____21685
                else "TOP" in
              let p = new_problem env lhs rel rhs elt loc reason in p
let new_t_prob:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____21713 =
              let uu____21716 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_93  -> FStar_Pervasives_Native.Some _0_93)
                uu____21716 in
            FStar_Syntax_Syntax.new_bv uu____21713 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21725 =
              let uu____21728 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_94  -> FStar_Pervasives_Native.Some _0_94)
                uu____21728 in
            let uu____21731 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21725 uu____21731 in
          ((FStar_TypeChecker_Common.TProb p), x)
let solve_and_commit:
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
        -> FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option
  =
  fun env  ->
    fun probs  ->
      fun err1  ->
        let probs1 =
          let uu____21764 = FStar_Options.eager_inference () in
          if uu____21764
          then
            let uu___187_21765 = probs in
            {
              attempting = (uu___187_21765.attempting);
              wl_deferred = (uu___187_21765.wl_deferred);
              ctr = (uu___187_21765.ctr);
              defer_ok = false;
              smt_ok = (uu___187_21765.smt_ok);
              tcenv = (uu___187_21765.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____21777 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21777
              then
                let uu____21778 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21778
              else ());
             err1 (d, s))
let simplify_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____21790 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21790
            then
              let uu____21791 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21791
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21795 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21795
             then
               let uu____21796 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21796
             else ());
            (let f2 =
               let uu____21799 =
                 let uu____21800 = FStar_Syntax_Util.unmeta f1 in
                 uu____21800.FStar_Syntax_Syntax.n in
               match uu____21799 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21804 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___188_21805 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___188_21805.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___188_21805.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___188_21805.FStar_TypeChecker_Env.implicits)
             })))
let with_guard:
  FStar_TypeChecker_Env.env ->
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
            let uu____21827 =
              let uu____21828 =
                let uu____21829 =
                  let uu____21830 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21830
                    (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21829;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21828 in
            FStar_All.pipe_left
              (fun _0_96  -> FStar_Pervasives_Native.Some _0_96) uu____21827
let with_guard_no_simp:
  'Auu____21861 .
    'Auu____21861 ->
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
            let uu____21881 =
              let uu____21882 =
                let uu____21883 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21883
                  (fun _0_97  -> FStar_TypeChecker_Common.NonTrivial _0_97) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21882;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21881
let try_teq:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____21925 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21925
           then
             let uu____21926 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21927 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21926
               uu____21927
           else ());
          (let prob =
             let uu____21930 =
               let uu____21935 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21935 in
             FStar_All.pipe_left
               (fun _0_98  -> FStar_TypeChecker_Common.TProb _0_98)
               uu____21930 in
           let g =
             let uu____21943 =
               let uu____21946 = singleton' env prob smt_ok in
               solve_and_commit env uu____21946
                 (fun uu____21948  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21943 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21969 = try_teq true env t1 t2 in
        match uu____21969 with
        | FStar_Pervasives_Native.None  ->
            let uu____21972 =
              let uu____21973 =
                let uu____21978 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21979 = FStar_TypeChecker_Env.get_range env in
                (uu____21978, uu____21979) in
              FStar_Errors.Error uu____21973 in
            FStar_Exn.raise uu____21972
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21982 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21982
              then
                let uu____21983 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21984 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21985 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21983
                  uu____21984 uu____21985
              else ());
             g)
let try_subtype':
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____22006 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____22006
           then
             let uu____22007 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____22008 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____22007
               uu____22008
           else ());
          (let uu____22010 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____22010 with
           | (prob,x) ->
               let g =
                 let uu____22022 =
                   let uu____22025 = singleton' env prob smt_ok in
                   solve_and_commit env uu____22025
                     (fun uu____22027  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____22022 in
               ((let uu____22037 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____22037
                 then
                   let uu____22038 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____22039 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____22040 =
                     let uu____22041 = FStar_Util.must g in
                     guard_to_string env uu____22041 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____22038 uu____22039 uu____22040
                 else ());
                abstract_guard x g))
let try_subtype:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  = fun env  -> fun t1  -> fun t2  -> try_subtype' env t1 t2 true
let subtype_fail:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____22073 = FStar_TypeChecker_Env.get_range env in
          let uu____22074 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____22073 uu____22074
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22090 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22090
         then
           let uu____22091 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22092 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22091
             uu____22092
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22097 =
             let uu____22102 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22102 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_99  -> FStar_TypeChecker_Common.CProb _0_99) uu____22097 in
         let uu____22107 =
           let uu____22110 = singleton env prob in
           solve_and_commit env uu____22110
             (fun uu____22112  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22107)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____22144  ->
        match uu____22144 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22183 =
                 let uu____22184 =
                   let uu____22189 =
                     let uu____22190 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____22191 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____22190 uu____22191 in
                   let uu____22192 = FStar_TypeChecker_Env.get_range env in
                   (uu____22189, uu____22192) in
                 FStar_Errors.Error uu____22184 in
               FStar_Exn.raise uu____22183) in
            let equiv1 v1 v' =
              let uu____22200 =
                let uu____22205 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22206 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22205, uu____22206) in
              match uu____22200 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22225 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22255 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22255 with
                      | FStar_Syntax_Syntax.U_unif uu____22262 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22291  ->
                                    match uu____22291 with
                                    | (u,v') ->
                                        let uu____22300 = equiv1 v1 v' in
                                        if uu____22300
                                        then
                                          let uu____22303 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22303 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22319 -> [])) in
            let uu____22324 =
              let wl =
                let uu___189_22328 = empty_worklist env in
                {
                  attempting = (uu___189_22328.attempting);
                  wl_deferred = (uu___189_22328.wl_deferred);
                  ctr = (uu___189_22328.ctr);
                  defer_ok = false;
                  smt_ok = (uu___189_22328.smt_ok);
                  tcenv = (uu___189_22328.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22346  ->
                      match uu____22346 with
                      | (lb,v1) ->
                          let uu____22353 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22353 with
                           | USolved wl1 -> ()
                           | uu____22355 -> fail lb v1))) in
            let rec check_ineq uu____22363 =
              match uu____22363 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22372) -> true
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
                      uu____22395,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22397,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22408) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22415,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22423 -> false) in
            let uu____22428 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22443  ->
                      match uu____22443 with
                      | (u,v1) ->
                          let uu____22450 = check_ineq (u, v1) in
                          if uu____22450
                          then true
                          else
                            ((let uu____22453 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22453
                              then
                                let uu____22454 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22455 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22454
                                  uu____22455
                              else ());
                             false))) in
            if uu____22428
            then ()
            else
              ((let uu____22459 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22459
                then
                  ((let uu____22461 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22461);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22471 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22471))
                else ());
               (let uu____22481 =
                  let uu____22482 =
                    let uu____22487 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22487) in
                  FStar_Errors.Error uu____22482 in
                FStar_Exn.raise uu____22481))
let solve_universe_inequalities:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
let rec solve_deferred_constraints:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let fail uu____22539 =
        match uu____22539 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22553 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22553
       then
         let uu____22554 = wl_to_string wl in
         let uu____22555 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22554 uu____22555
       else ());
      (let g1 =
         let uu____22570 = solve_and_commit env wl fail in
         match uu____22570 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___190_22583 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___190_22583.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___190_22583.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___190_22583.FStar_TypeChecker_Env.implicits)
             }
         | uu____22588 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___191_22592 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___191_22592.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___191_22592.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___191_22592.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22615 = FStar_ST.op_Bang last_proof_ns in
    match uu____22615 with
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
let discharge_guard':
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g in
          let ret_g =
            let uu___192_22802 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___192_22802.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___192_22802.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___192_22802.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22803 =
            let uu____22804 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22804 in
          if uu____22803
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22812 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22812
                   then
                     let uu____22813 = FStar_TypeChecker_Env.get_range env in
                     let uu____22814 =
                       let uu____22815 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22815 in
                     FStar_Errors.diag uu____22813 uu____22814
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____22818 = check_trivial vc1 in
                   match uu____22818 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____22825 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22825
                           then
                             let uu____22826 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22827 =
                               let uu____22828 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____22828 in
                             FStar_Errors.diag uu____22826 uu____22827
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____22833 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22833
                           then
                             let uu____22834 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22835 =
                               let uu____22836 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____22836 in
                             FStar_Errors.diag uu____22834 uu____22835
                           else ());
                          (let vcs =
                             let uu____22847 = FStar_Options.use_tactics () in
                             if uu____22847
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____22857 =
                                  let uu____22864 = FStar_Options.peek () in
                                  (env, vc2, uu____22864) in
                                [uu____22857]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____22898  ->
                                   match uu____22898 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____22909 = check_trivial goal1 in
                                       (match uu____22909 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____22911 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____22911
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____22918 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____22918
                                              then
                                                let uu____22919 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____22920 =
                                                  let uu____22921 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____22922 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____22921 uu____22922 in
                                                FStar_Errors.diag uu____22919
                                                  uu____22920
                                              else ());
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                               use_env_range_msg env1 goal2;
                                             FStar_Options.pop ())))));
                          FStar_Pervasives_Native.Some ret_g))))
let discharge_guard_no_smt:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22934 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22934 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22940 =
            let uu____22941 =
              let uu____22946 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22946) in
            FStar_Errors.Error uu____22941 in
          FStar_Exn.raise uu____22940
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22955 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22955 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits':
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun must_total  ->
    fun forcelax  ->
      fun g  ->
        let unresolved u =
          let uu____22977 = FStar_Syntax_Unionfind.find u in
          match uu____22977 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22980 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22998 = acc in
          match uu____22998 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23084 = hd1 in
                   (match uu____23084 with
                    | (uu____23097,env,u,tm,k,r) ->
                        let uu____23103 = unresolved u in
                        if uu____23103
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____23134 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____23134
                            then
                              let uu____23135 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____23136 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____23137 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23135 uu____23136 uu____23137
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___193_23140 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___193_23140.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___193_23140.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___193_23140.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___193_23140.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___193_23140.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___193_23140.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___193_23140.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___193_23140.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___193_23140.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___193_23140.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___193_23140.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___193_23140.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___193_23140.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___193_23140.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___193_23140.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___193_23140.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___193_23140.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___193_23140.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___193_23140.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___193_23140.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___193_23140.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___193_23140.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___193_23140.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___193_23140.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___193_23140.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___193_23140.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___193_23140.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___193_23140.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___193_23140.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___193_23140.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___193_23140.FStar_TypeChecker_Env.tc_hooks)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____23143 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___194_23151 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___194_23151.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___194_23151.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___194_23151.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___194_23151.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___194_23151.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___194_23151.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___194_23151.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___194_23151.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___194_23151.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___194_23151.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___194_23151.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___194_23151.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___194_23151.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___194_23151.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___194_23151.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___194_23151.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___194_23151.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___194_23151.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___194_23151.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___194_23151.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___194_23151.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___194_23151.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___194_23151.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___194_23151.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___194_23151.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___194_23151.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___194_23151.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___194_23151.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___194_23151.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___194_23151.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___194_23151.FStar_TypeChecker_Env.tc_hooks)
                                     }) tm1 in
                                match uu____23143 with
                                | (uu____23152,uu____23153,g1) -> g1
                              else
                                (let uu____23156 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___195_23164 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___195_23164.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___195_23164.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___195_23164.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___195_23164.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___195_23164.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___195_23164.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___195_23164.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___195_23164.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___195_23164.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___195_23164.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___195_23164.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___195_23164.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___195_23164.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___195_23164.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___195_23164.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___195_23164.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___195_23164.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___195_23164.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___195_23164.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___195_23164.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___195_23164.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___195_23164.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___195_23164.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___195_23164.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___195_23164.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___195_23164.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___195_23164.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___195_23164.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___195_23164.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___195_23164.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___195_23164.FStar_TypeChecker_Env.tc_hooks)
                                      }) tm1 in
                                 match uu____23156 with
                                 | (uu____23165,uu____23166,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___196_23169 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___196_23169.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___196_23169.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___196_23169.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23172 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23178  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____23172 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___197_23206 = g in
        let uu____23207 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___197_23206.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___197_23206.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___197_23206.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23207
        }
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' true false g
let resolve_implicits_tac:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' false true g
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____23265 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23265 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23278 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23278
      | (reason,uu____23280,uu____23281,e,t,r)::uu____23285 ->
          let uu____23312 =
            let uu____23313 =
              let uu____23318 =
                let uu____23319 = FStar_Syntax_Print.term_to_string t in
                let uu____23320 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____23319 uu____23320 in
              (uu____23318, r) in
            FStar_Errors.Error uu____23313 in
          FStar_Exn.raise uu____23312
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___198_23329 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___198_23329.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___198_23329.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___198_23329.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23358 = try_teq false env t1 t2 in
        match uu____23358 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____23362 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____23362 with
             | FStar_Pervasives_Native.Some uu____23367 -> true
             | FStar_Pervasives_Native.None  -> false)