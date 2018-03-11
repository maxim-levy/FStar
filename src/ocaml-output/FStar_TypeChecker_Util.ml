open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let (report :
  FStar_TypeChecker_Env.env -> Prims.string Prims.list -> Prims.unit) =
  fun env  ->
    fun errs  ->
      let uu____17 = FStar_TypeChecker_Env.get_range env  in
      let uu____18 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____17 uu____18
  
let (is_type : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26 =
      let uu____27 = FStar_Syntax_Subst.compress t  in
      uu____27.FStar_Syntax_Syntax.n  in
    match uu____26 with
    | FStar_Syntax_Syntax.Tm_type uu____30 -> true
    | uu____31 -> false
  
let (t_binders :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    let uu____41 = FStar_TypeChecker_Env.all_binders env  in
    FStar_All.pipe_right uu____41
      (FStar_List.filter
         (fun uu____55  ->
            match uu____55 with
            | (x,uu____61) -> is_type x.FStar_Syntax_Syntax.sort))
  
let (new_uvar_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____73 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____75 = FStar_TypeChecker_Env.current_module env  in
             FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____75)
           in
        if uu____73
        then FStar_TypeChecker_Env.all_binders env
        else t_binders env  in
      let uu____77 = FStar_TypeChecker_Env.get_range env  in
      FStar_TypeChecker_Rel.new_uvar uu____77 bs k
  
let (new_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun k  ->
      let uu____84 = new_uvar_aux env k  in
      FStar_Pervasives_Native.fst uu____84
  
let (as_uvar : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.uvar) =
  fun uu___80_93  ->
    match uu___80_93 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,uu____95);
        FStar_Syntax_Syntax.pos = uu____96;
        FStar_Syntax_Syntax.vars = uu____97;_} -> uv
    | uu____128 -> failwith "Impossible"
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.uvar,FStar_Range.range)
                                      FStar_Pervasives_Native.tuple2
                                      Prims.list,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____153 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid  in
          match uu____153 with
          | FStar_Pervasives_Native.Some (uu____176::(tm,uu____178)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____230 ->
              let uu____241 = new_uvar_aux env k  in
              (match uu____241 with
               | (t,u) ->
                   let g =
                     let uu___104_261 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     let uu____262 =
                       let uu____277 =
                         let uu____290 = as_uvar u  in
                         (reason, env, uu____290, t, k, r)  in
                       [uu____277]  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___104_261.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___104_261.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___104_261.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits = uu____262
                     }  in
                   let uu____315 =
                     let uu____322 =
                       let uu____327 = as_uvar u  in (uu____327, r)  in
                     [uu____322]  in
                   (t, uu____315, g))
  
let (check_uvars :
  FStar_Range.range -> FStar_Syntax_Syntax.typ -> Prims.unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____355 =
        let uu____356 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____356  in
      if uu____355
      then
        let us =
          let uu____362 =
            let uu____365 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun uu____383  ->
                 match uu____383 with
                 | (x,uu____389) -> FStar_Syntax_Print.uvar_to_string x)
              uu____365
             in
          FStar_All.pipe_right uu____362 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____396 =
            let uu____401 =
              let uu____402 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____402
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____401)  in
          FStar_Errors.log_issue r uu____396);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____415  ->
      match uu____415 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____425;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____427;
          FStar_Syntax_Syntax.lbpos = uu____428;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (if univ_vars1 <> []
                then
                  failwith
                    "Impossible: non-empty universe variables but the type is unknown"
                else ();
                (let r = FStar_TypeChecker_Env.get_range env  in
                 let mk_binder1 scope a =
                   let uu____477 =
                     let uu____478 =
                       FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort
                        in
                     uu____478.FStar_Syntax_Syntax.n  in
                   match uu____477 with
                   | FStar_Syntax_Syntax.Tm_unknown  ->
                       let uu____485 = FStar_Syntax_Util.type_u ()  in
                       (match uu____485 with
                        | (k,uu____495) ->
                            let t2 =
                              let uu____497 =
                                FStar_TypeChecker_Rel.new_uvar
                                  e.FStar_Syntax_Syntax.pos scope k
                                 in
                              FStar_All.pipe_right uu____497
                                FStar_Pervasives_Native.fst
                               in
                            ((let uu___105_507 = a  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___105_507.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___105_507.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t2
                              }), false))
                   | uu____508 -> (a, true)  in
                 let rec aux must_check_ty vars e1 =
                   let e2 = FStar_Syntax_Subst.compress e1  in
                   match e2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_meta (e3,uu____545) ->
                       aux must_check_ty vars e3
                   | FStar_Syntax_Syntax.Tm_ascribed (e3,t2,uu____552) ->
                       ((FStar_Pervasives_Native.fst t2), true)
                   | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____615) ->
                       let uu____636 =
                         FStar_All.pipe_right bs
                           (FStar_List.fold_left
                              (fun uu____696  ->
                                 fun uu____697  ->
                                   match (uu____696, uu____697) with
                                   | ((scope,bs1,must_check_ty1),(a,imp)) ->
                                       let uu____775 =
                                         if must_check_ty1
                                         then (a, true)
                                         else mk_binder1 scope a  in
                                       (match uu____775 with
                                        | (tb,must_check_ty2) ->
                                            let b = (tb, imp)  in
                                            let bs2 =
                                              FStar_List.append bs1 [b]  in
                                            let scope1 =
                                              FStar_List.append scope [b]  in
                                            (scope1, bs2, must_check_ty2)))
                              (vars, [], must_check_ty))
                          in
                       (match uu____636 with
                        | (scope,bs1,must_check_ty1) ->
                            let uu____887 = aux must_check_ty1 scope body  in
                            (match uu____887 with
                             | (res,must_check_ty2) ->
                                 let c =
                                   match res with
                                   | FStar_Util.Inl t2 ->
                                       let uu____916 =
                                         FStar_Options.ml_ish ()  in
                                       if uu____916
                                       then FStar_Syntax_Util.ml_comp t2 r
                                       else FStar_Syntax_Syntax.mk_Total t2
                                   | FStar_Util.Inr c -> c  in
                                 let t2 = FStar_Syntax_Util.arrow bs1 c  in
                                 ((let uu____923 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High
                                      in
                                   if uu____923
                                   then
                                     let uu____924 =
                                       FStar_Range.string_of_range r  in
                                     let uu____925 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____926 =
                                       FStar_Util.string_of_bool
                                         must_check_ty2
                                        in
                                     FStar_Util.print3
                                       "(%s) Using type %s .... must check = %s\n"
                                       uu____924 uu____925 uu____926
                                   else ());
                                  ((FStar_Util.Inl t2), must_check_ty2))))
                   | uu____936 ->
                       if must_check_ty
                       then ((FStar_Util.Inl FStar_Syntax_Syntax.tun), true)
                       else
                         (let uu____950 =
                            let uu____955 =
                              let uu____956 =
                                FStar_TypeChecker_Rel.new_uvar r vars
                                  FStar_Syntax_Util.ktype0
                                 in
                              FStar_All.pipe_right uu____956
                                FStar_Pervasives_Native.fst
                               in
                            FStar_Util.Inl uu____955  in
                          (uu____950, false))
                    in
                 let uu____969 =
                   let uu____978 = t_binders env  in aux false uu____978 e
                    in
                 match uu____969 with
                 | (t2,b) ->
                     let t3 =
                       match t2 with
                       | FStar_Util.Inr c ->
                           let uu____1003 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                           if uu____1003
                           then FStar_Syntax_Util.comp_result c
                           else
                             (let uu____1007 =
                                let uu____1012 =
                                  let uu____1013 =
                                    FStar_Syntax_Print.comp_to_string c  in
                                  FStar_Util.format1
                                    "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                    uu____1013
                                   in
                                (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                  uu____1012)
                                 in
                              FStar_Errors.raise_error uu____1007 rng)
                       | FStar_Util.Inl t3 -> t3  in
                     ([], t3, b)))
           | uu____1021 ->
               let uu____1022 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____1022 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_TypeChecker_Env.env ->
           FStar_Syntax_Syntax.term ->
             (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
               FStar_Pervasives_Native.tuple2)
          ->
          (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,
            FStar_TypeChecker_Env.guard_t,FStar_Syntax_Syntax.pat)
            FStar_Pervasives_Native.tuple4)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        fun tc_annot  ->
          let check_bv env1 x =
            let uu____1102 =
              let uu____1107 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____1107 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____1112;
                  FStar_Syntax_Syntax.vars = uu____1113;_} ->
                  let uu____1120 = FStar_Syntax_Util.type_u ()  in
                  (match uu____1120 with
                   | (t,uu____1130) ->
                       let uu____1131 = new_uvar env1 t  in
                       (uu____1131, FStar_TypeChecker_Rel.trivial_guard))
              | t -> tc_annot env1 t  in
            match uu____1102 with
            | (t_x,guard) ->
                ((let uu___106_1140 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___106_1140.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___106_1140.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = t_x
                  }), guard)
             in
          let rec pat_as_arg_with_env allow_wc_dependence env1 p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let e =
                  match c with
                  | FStar_Const.Const_int
                      (repr,FStar_Pervasives_Native.Some sw) ->
                      FStar_ToSyntax_ToSyntax.desugar_machine_integer
                        env1.FStar_TypeChecker_Env.dsenv repr sw
                        p1.FStar_Syntax_Syntax.p
                  | uu____1209 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1217) ->
                let uu____1222 = FStar_Syntax_Util.type_u ()  in
                (match uu____1222 with
                 | (k,uu____1248) ->
                     let t = new_uvar env1 k  in
                     let x1 =
                       let uu___107_1251 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___107_1251.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___107_1251.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t
                       }  in
                     let uu____1252 =
                       let uu____1257 =
                         FStar_TypeChecker_Env.all_binders env1  in
                       FStar_TypeChecker_Rel.new_uvar
                         p1.FStar_Syntax_Syntax.p uu____1257 t
                        in
                     (match uu____1252 with
                      | (e,u) ->
                          let p2 =
                            let uu___108_1283 = p1  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                              FStar_Syntax_Syntax.p =
                                (uu___108_1283.FStar_Syntax_Syntax.p)
                            }  in
                          ([], [], [], env1, e,
                            FStar_TypeChecker_Rel.trivial_guard, p2)))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1293 = check_bv env1 x  in
                (match uu____1293 with
                 | (x1,g) ->
                     let env2 =
                       if allow_wc_dependence
                       then FStar_TypeChecker_Env.push_bv env1 x1
                       else env1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [], [x1], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_var x ->
                let uu____1334 = check_bv env1 x  in
                (match uu____1334 with
                 | (x1,g) ->
                     let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [x1], [], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let uu____1391 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1527  ->
                          fun uu____1528  ->
                            match (uu____1527, uu____1528) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1726 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1726 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1802 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1802, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1391 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1933 =
                         let uu____1934 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____1935 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1934 uu____1935
                          in
                       uu____1933 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1942 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____1953 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____1964 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1942, uu____1953, uu____1964, env2, e, guard,
                       (let uu___109_1986 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___109_1986.FStar_Syntax_Syntax.p)
                        })))
             in
          let rec elaborate_pat env1 p1 =
            let maybe_dot inaccessible a r =
              if allow_implicits && inaccessible
              then
                FStar_Syntax_Syntax.withinfo
                  (FStar_Syntax_Syntax.Pat_dot_term
                     (a, FStar_Syntax_Syntax.tun)) r
              else
                FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                  r
               in
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let pats1 =
                  FStar_List.map
                    (fun uu____2070  ->
                       match uu____2070 with
                       | (p2,imp) ->
                           let uu____2089 = elaborate_pat env1 p2  in
                           (uu____2089, imp)) pats
                   in
                let uu____2094 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____2094 with
                 | (uu____2101,t) ->
                     let uu____2103 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____2103 with
                      | (f,uu____2119) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2241::uu____2242) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments")
                                  (FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | (uu____2293::uu____2294,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2372  ->
                                        match uu____2372 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2399 =
                                                     let uu____2402 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2402
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2399
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2404 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2404, true)
                                             | uu____2409 ->
                                                 let uu____2412 =
                                                   let uu____2417 =
                                                     let uu____2418 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2418
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2417)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2412
                                                   (FStar_Ident.range_of_lid
                                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2492,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2493)) when p_imp ->
                                     let uu____2496 = aux formals' pats'  in
                                     (p2, true) :: uu____2496
                                 | (uu____2513,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       maybe_dot inaccessible a
                                         (FStar_Ident.range_of_lid
                                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                        in
                                     let uu____2521 = aux formals' pats2  in
                                     (p3, true) :: uu____2521
                                 | (uu____2538,imp) ->
                                     let uu____2544 =
                                       let uu____2551 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2551)  in
                                     let uu____2554 = aux formals' pats'  in
                                     uu____2544 :: uu____2554)
                             in
                          let uu___110_2569 = p1  in
                          let uu____2572 =
                            let uu____2573 =
                              let uu____2586 = aux f pats1  in
                              (fv, uu____2586)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2573  in
                          {
                            FStar_Syntax_Syntax.v = uu____2572;
                            FStar_Syntax_Syntax.p =
                              (uu___110_2569.FStar_Syntax_Syntax.p)
                          }))
            | uu____2603 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2639 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2639 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2697 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2697 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2723 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2723
                       p3.FStar_Syntax_Syntax.p
                 | uu____2746 -> (b, a, w, arg, guard, p3))
             in
          let uu____2755 = one_pat true env p  in
          match uu____2755 with
          | (b,uu____2785,uu____2786,tm,guard,p1) -> (b, tm, guard, p1)
  
let (decorate_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      fun exp  ->
        let qq = p  in
        let rec aux p1 e =
          let pkg q = FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p
             in
          let e1 = FStar_Syntax_Util.unmeta e  in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____2832,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2834)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2839,uu____2840) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2844 =
                    let uu____2845 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2846 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2845 uu____2846
                     in
                  failwith uu____2844)
               else ();
               (let uu____2849 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2849
                then
                  let uu____2850 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2851 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2850
                    uu____2851
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___111_2855 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___111_2855.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___111_2855.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2859 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2859
                then
                  let uu____2860 =
                    let uu____2861 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2862 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2861 uu____2862
                     in
                  failwith uu____2860
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___112_2866 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___112_2866.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___112_2866.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2868),uu____2869) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2891 =
                  let uu____2892 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2892  in
                if uu____2891
                then
                  let uu____2893 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2893
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2912;
                FStar_Syntax_Syntax.vars = uu____2913;_},args))
              ->
              ((let uu____2956 =
                  let uu____2957 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____2957 Prims.op_Negation  in
                if uu____2956
                then
                  let uu____2958 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2958
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3094)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3169) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3206) ->
                           let pat =
                             let uu____3228 = aux argpat e2  in
                             let uu____3229 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3228, uu____3229)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3234 ->
                      let uu____3257 =
                        let uu____3258 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3259 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3258 uu____3259
                         in
                      failwith uu____3257
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3271;
                     FStar_Syntax_Syntax.vars = uu____3272;_},uu____3273);
                FStar_Syntax_Syntax.pos = uu____3274;
                FStar_Syntax_Syntax.vars = uu____3275;_},args))
              ->
              ((let uu____3326 =
                  let uu____3327 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3327 Prims.op_Negation  in
                if uu____3326
                then
                  let uu____3328 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3328
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3464)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3539) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3576) ->
                           let pat =
                             let uu____3598 = aux argpat e2  in
                             let uu____3599 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3598, uu____3599)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3604 ->
                      let uu____3627 =
                        let uu____3628 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3629 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3628 uu____3629
                         in
                      failwith uu____3627
                   in
                match_args [] args argpats))
          | uu____3638 ->
              let uu____3643 =
                let uu____3644 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3645 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3646 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3644 uu____3645 uu____3646
                 in
              failwith uu____3643
           in
        aux p exp
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____3683 =
      match uu____3683 with
      | (p,i) ->
          let uu____3700 = decorated_pattern_as_term p  in
          (match uu____3700 with
           | (vars,te) ->
               let uu____3723 =
                 let uu____3728 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3728)  in
               (vars, uu____3723))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3742 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____3742)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3746 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3746)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3750 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3750)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3771 =
          let uu____3786 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____3786 FStar_List.unzip  in
        (match uu____3771 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____3896 =
               let uu____3897 =
                 let uu____3898 =
                   let uu____3913 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____3913, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____3898  in
               mk1 uu____3897  in
             (vars1, uu____3896))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____3943,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____3953,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____3967 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3991)::[] -> wp
      | uu____4008 ->
          let uu____4017 =
            let uu____4018 =
              let uu____4019 =
                FStar_List.map
                  (fun uu____4029  ->
                     match uu____4029 with
                     | (x,uu____4035) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____4019 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____4018
             in
          failwith uu____4017
       in
    let uu____4040 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____4040, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____4054 = destruct_comp c  in
        match uu____4054 with
        | (u,uu____4062,wp) ->
            let uu____4064 =
              let uu____4073 =
                let uu____4074 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____4074  in
              [uu____4073]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____4064;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____4084 =
          let uu____4091 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____4092 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____4091 uu____4092  in
        match uu____4084 with | (m,uu____4094,uu____4095) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4105 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4105
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
  
let (lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,(FStar_Syntax_Syntax.universe,
                                            FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                                            FStar_Pervasives_Native.tuple3,
          (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.tuple3)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
        let uu____4142 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4142 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4179 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4179 with
             | (a,kwp) ->
                 let uu____4210 = destruct_comp m1  in
                 let uu____4217 = destruct_comp m2  in
                 ((md, a, kwp), uu____4210, uu____4217))
  
let (is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
  
let (is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
  
let (mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags1  ->
            let uu____4279 =
              let uu____4280 =
                let uu____4289 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4289]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4280;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4279
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags1  ->
          if FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1
  
let (subst_lcomp :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun subst1  ->
    fun lc  ->
      let uu____4328 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4328
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4331  ->
           let uu____4332 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4332)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4336 =
      let uu____4337 = FStar_Syntax_Subst.compress t  in
      uu____4337.FStar_Syntax_Syntax.n  in
    match uu____4336 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4340 -> true
    | uu____4353 -> false
  
let (label :
  Prims.string ->
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false))))
          FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos
  
let (label_opt :
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | FStar_Pervasives_Native.None  -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____4391 =
                let uu____4392 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4392  in
              if uu____4391
              then f
              else (let uu____4394 = reason1 ()  in label uu____4394 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___113_4405 = g  in
            let uu____4406 =
              let uu____4407 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4407  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4406;
              FStar_TypeChecker_Env.deferred =
                (uu___113_4405.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___113_4405.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___113_4405.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4421 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4421
        then c
        else
          (let uu____4423 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4423
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4462 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4462]  in
                       let us =
                         let uu____4466 =
                           let uu____4469 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4469]  in
                         u_res :: uu____4466  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4473 =
                         let uu____4474 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4475 =
                           let uu____4476 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4477 =
                             let uu____4480 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4481 =
                               let uu____4484 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4484]  in
                             uu____4480 :: uu____4481  in
                           uu____4476 :: uu____4477  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4474 uu____4475
                          in
                       uu____4473 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4488 = destruct_comp c1  in
              match uu____4488 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
          (fun uu____4515  ->
             let uu____4516 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____4516)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___81_4523  ->
            match uu___81_4523 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4524 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (let uu____4540 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____4540))
               &&
               (let uu____4547 = FStar_Syntax_Util.head_and_args' e  in
                match uu____4547 with
                | (head1,uu____4561) ->
                    let uu____4578 =
                      let uu____4579 = FStar_Syntax_Util.un_uinst head1  in
                      uu____4579.FStar_Syntax_Syntax.n  in
                    (match uu____4578 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4583 =
                           let uu____4584 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4584
                            in
                         Prims.op_Negation uu____4583
                     | uu____4585 -> true)))
              &&
              (let uu____4587 = should_not_inline_lc lc  in
               Prims.op_Negation uu____4587)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____4605 =
              let uu____4606 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____4606  in
            if uu____4605
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4608 = FStar_Syntax_Util.is_unit t  in
               if uu____4608
               then
                 FStar_Syntax_Syntax.mk_Total' t
                   (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
               else
                 (let m =
                    FStar_TypeChecker_Env.get_effect_decl env
                      FStar_Parser_Const.effect_PURE_lid
                     in
                  let u_t =
                    match u_t_opt with
                    | FStar_Pervasives_Native.None  ->
                        env.FStar_TypeChecker_Env.universe_of env t
                    | FStar_Pervasives_Native.Some u_t -> u_t  in
                  let wp =
                    let uu____4614 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____4614
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4616 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____4616 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____4624 =
                             let uu____4625 =
                               let uu____4626 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____4627 =
                                 let uu____4628 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____4629 =
                                   let uu____4632 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____4632]  in
                                 uu____4628 :: uu____4629  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4626
                                 uu____4627
                                in
                             uu____4625 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4624)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____4636 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____4636
           then
             let uu____4637 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____4638 = FStar_Syntax_Print.term_to_string v1  in
             let uu____4639 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4637 uu____4638 uu____4639
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____4650 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___82_4654  ->
              match uu___82_4654 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4655 -> false))
       in
    if uu____4650
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___83_4664  ->
              match uu___83_4664 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____4677 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4677
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____4680 = destruct_comp c1  in
           match uu____4680 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____4694 =
                   let uu____4695 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____4696 =
                     let uu____4697 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____4698 =
                       let uu____4701 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____4702 =
                         let uu____4705 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____4705]  in
                       uu____4701 :: uu____4702  in
                     uu____4697 :: uu____4698  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4695 uu____4696  in
                 uu____4694 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____4708 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____4708)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4723 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____4725 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____4725
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____4728 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____4728 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags1  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
               let uu____4761 = destruct_comp c1  in
               match uu____4761 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____4775 =
                       let uu____4776 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____4777 =
                         let uu____4778 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____4779 =
                           let uu____4782 =
                             let uu____4783 =
                               let uu____4784 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____4784 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____4783
                              in
                           let uu____4785 =
                             let uu____4788 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____4788]  in
                           uu____4782 :: uu____4785  in
                         uu____4778 :: uu____4779  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____4776 uu____4777
                        in
                     uu____4775 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos
                      in
                   mk_comp md u_res_t res_t wp1 flags1)
  
let (strengthen_precondition :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun reason  ->
    fun env  ->
      fun e_for_debug_only  ->
        fun lc  ->
          fun g0  ->
            let uu____4823 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____4823
            then (lc, g0)
            else
              (let flags1 =
                 let uu____4832 =
                   let uu____4839 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____4839
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____4832 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____4859 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___84_4867  ->
                               match uu___84_4867 with
                               | FStar_Syntax_Syntax.RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.SOMETRIVIAL  when
                                   Prims.op_Negation maybe_trivial_post ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION 
                                   when Prims.op_Negation maybe_trivial_post
                                   ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                   [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                               | uu____4870 -> []))
                        in
                     FStar_List.append flags1 uu____4859
                  in
               let strengthen uu____4874 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____4878 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____4878 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____4881 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____4881
                          then
                            let uu____4882 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____4883 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____4882 uu____4883
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____4885 =
                 let uu____4886 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____4886
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____4885,
                 (let uu___114_4888 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___114_4888.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___114_4888.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___114_4888.FStar_TypeChecker_Env.implicits)
                  })))
  
let (stable_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Syntax_Util.is_tac_lcomp lc)
  
let (stable_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Syntax_Util.is_tot_or_gtot_comp c) ||
      (FStar_Syntax_Util.is_tac_comp c)
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (stable_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___85_4903  ->
            match uu___85_4903 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____4904 -> false) lc.FStar_Syntax_Syntax.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____4921 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____4921
          then e
          else
            (let uu____4923 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____4925 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____4925)
                in
             if uu____4923
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_Syntax_Syntax.res_typ
                  in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_Syntax_Syntax.res_typ e
             else e)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____4963  ->
            match uu____4963 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____4981 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____4981 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____4989 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____4989
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____4996 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____4996
                       then
                         let uu____4999 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____4999
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5003 = stable_lcomp lc21  in
                             if uu____5003
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5008 =
                            (stable_lcomp lc11) && (stable_lcomp lc21)  in
                          if uu____5008
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5012 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5012
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5019 =
                  let uu____5020 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5020
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_Syntax_Syntax.res_typ
                       in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11  in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21  in
                     debug1
                       (fun uu____5034  ->
                          let uu____5035 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5036 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5038 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5035 uu____5036 uu____5038);
                     (let aux uu____5050 =
                        let uu____5051 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5051
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5072 ->
                              let uu____5073 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5073
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5092 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5092
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5159 =
                              let uu____5164 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5164, reason)  in
                            FStar_Util.Inl uu____5159
                        | uu____5171 -> aux ()  in
                      let try_simplify uu____5193 =
                        let rec maybe_close t x c =
                          let uu____5204 =
                            let uu____5205 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5205.FStar_Syntax_Syntax.n  in
                          match uu____5204 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5209) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5215 -> c  in
                        let uu____5216 =
                          let uu____5217 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5217  in
                        if uu____5216
                        then
                          let uu____5228 =
                            (stable_comp c1) && (stable_comp c2)  in
                          (if uu____5228
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____5242 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____5242))
                        else
                          (let uu____5252 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____5252
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____5262 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____5262
                              then
                                let uu____5271 =
                                  let uu____5276 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____5276, "both gtot")  in
                                FStar_Util.Inl uu____5271
                              else
                                (let uu____5282 =
                                   (stable_comp c1) && (stable_comp c2)  in
                                 if uu____5282
                                 then
                                   let ty = FStar_Syntax_Util.comp_result c2
                                      in
                                   let uu____5294 =
                                     let uu____5299 =
                                       let uu____5300 =
                                         let uu____5301 =
                                           let uu____5302 =
                                             env.FStar_TypeChecker_Env.universe_of
                                               env ty
                                              in
                                           [uu____5302]  in
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             uu____5301;
                                           FStar_Syntax_Syntax.effect_name =
                                             FStar_Parser_Const.effect_Tac_lid;
                                           FStar_Syntax_Syntax.result_typ =
                                             ty;
                                           FStar_Syntax_Syntax.effect_args =
                                             [];
                                           FStar_Syntax_Syntax.flags =
                                             [FStar_Syntax_Syntax.SOMETRIVIAL;
                                             FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____5300
                                        in
                                     (uu____5299, "both Tac")  in
                                   FStar_Util.Inl uu____5294
                                 else
                                   (match (e1opt, b) with
                                    | (FStar_Pervasives_Native.Some
                                       e,FStar_Pervasives_Native.Some x) ->
                                        let uu____5332 =
                                          (FStar_Syntax_Util.is_total_comp c1)
                                            &&
                                            (let uu____5334 =
                                               FStar_Syntax_Syntax.is_null_bv
                                                 x
                                                in
                                             Prims.op_Negation uu____5334)
                                           in
                                        if uu____5332
                                        then
                                          let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e)]
                                              c2
                                             in
                                          let x1 =
                                            let uu___115_5345 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___115_5345.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___115_5345.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                            }  in
                                          let uu____5346 =
                                            let uu____5351 =
                                              maybe_close
                                                x1.FStar_Syntax_Syntax.sort
                                                x1 c21
                                               in
                                            (uu____5351, "c1 Tot")  in
                                          FStar_Util.Inl uu____5346
                                        else aux ()
                                    | uu____5357 -> aux ()))))
                         in
                      let uu____5366 = try_simplify ()  in
                      match uu____5366 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____5386  ->
                                let uu____5387 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5387);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____5396  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____5411 = lift_and_destruct env c11 c21
                                 in
                              match uu____5411 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5468 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____5468]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____5470 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____5470]
                                     in
                                  let mk_lam wp =
                                    FStar_Syntax_Util.abs bs wp
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.mk_residual_comp
                                            FStar_Parser_Const.effect_Tot_lid
                                            FStar_Pervasives_Native.None
                                            [FStar_Syntax_Syntax.TOTAL]))
                                     in
                                  let r11 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_range r1))
                                      FStar_Pervasives_Native.None r1
                                     in
                                  let wp_args =
                                    let uu____5483 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____5484 =
                                      let uu____5487 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____5488 =
                                        let uu____5491 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____5492 =
                                          let uu____5495 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____5496 =
                                            let uu____5499 =
                                              let uu____5500 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____5500
                                               in
                                            [uu____5499]  in
                                          uu____5495 :: uu____5496  in
                                        uu____5491 :: uu____5492  in
                                      uu____5487 :: uu____5488  in
                                    uu____5483 :: uu____5484  in
                                  let wp =
                                    let uu____5504 =
                                      let uu____5505 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____5505 wp_args
                                       in
                                    uu____5504 FStar_Pervasives_Native.None
                                      t2.FStar_Syntax_Syntax.pos
                                     in
                                  mk_comp md u_t2 t2 wp bind_flags
                               in
                            let mk_seq c11 b1 c21 =
                              let c12 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c11
                                 in
                              let c22 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c21
                                 in
                              let uu____5524 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____5524 with
                              | (m,uu____5532,lift2) ->
                                  let c23 =
                                    let uu____5535 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____5535
                                     in
                                  let uu____5536 = destruct_comp c12  in
                                  (match uu____5536 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____5550 =
                                           let uu____5551 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____5552 =
                                             let uu____5553 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____5554 =
                                               let uu____5557 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____5557]  in
                                             uu____5553 :: uu____5554  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____5551 uu____5552
                                            in
                                         uu____5550
                                           FStar_Pervasives_Native.None r1
                                          in
                                       strengthen_comp env
                                         FStar_Pervasives_Native.None c23 vc1
                                         bind_flags)
                               in
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1
                               in
                            let uu____5563 = destruct_comp c1_typ  in
                            match uu____5563 with
                            | (u_res_t1,res_t1,uu____5572) ->
                                let uu____5573 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____5573
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____5576 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____5576
                                   then
                                     (debug1
                                        (fun uu____5584  ->
                                           let uu____5585 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____5586 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____5585 uu____5586);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____5589 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____5591 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____5591)
                                         in
                                      if uu____5589
                                      then
                                        let e1' =
                                          let uu____5613 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____5613
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____5624  ->
                                              let uu____5625 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____5626 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____5625 uu____5626);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____5638  ->
                                              let uu____5639 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____5640 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____5639 uu____5640);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____5643 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____5643
                                             in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e  in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2))))
                   in
                FStar_Syntax_Syntax.mk_lcomp joined_eff
                  lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it
  
let (weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2  in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____5655 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let should_return1 =
          (((Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
              (FStar_TypeChecker_Env.lid_exists env
                 FStar_Parser_Const.effect_GTot_lid))
             && (should_return env (FStar_Pervasives_Native.Some e) lc))
            &&
            (let uu____5671 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____5671)
           in
        let flags1 =
          if should_return1
          then
            let uu____5677 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____5677
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____5685 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____5689 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____5689
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____5691 =
              let uu____5692 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____5692  in
            (if uu____5691
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___116_5695 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___116_5695.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___116_5695.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___116_5695.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags1
                 }  in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags1)
          else
            (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
             let t = c1.FStar_Syntax_Syntax.result_typ  in
             let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
             let x =
               FStar_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t
                in
             let xexp = FStar_Syntax_Syntax.bv_to_name x  in
             let ret1 =
               let uu____5706 =
                 let uu____5709 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____5709
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5706
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____5714 =
               let uu____5715 =
                 let uu____5716 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____5716
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____5715  in
             FStar_Syntax_Util.comp_set_flags uu____5714 flags1)
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags1 refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____5739  ->
              match uu____5739 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name
                       in
                    let uu____5751 =
                      ((let uu____5754 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____5754) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____5751
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____5764 =
        let uu____5765 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____5765  in
      FStar_Syntax_Syntax.fvar uu____5764 FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                    Prims.list,Prims.bool ->
                                                                 FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple4 Prims.list ->
        FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____5824  ->
                 match uu____5824 with
                 | (uu____5837,eff_label,uu____5839,uu____5840) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____5849 =
          let uu____5856 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____5888  ->
                    match uu____5888 with
                    | (uu____5901,uu____5902,flags1,uu____5904) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___86_5916  ->
                                match uu___86_5916 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____5917 -> false))))
             in
          if uu____5856
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____5849 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____5938 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____5940 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5940
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____5960 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____5961 =
                     let uu____5962 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____5963 =
                       let uu____5964 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____5965 =
                         let uu____5968 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____5969 =
                           let uu____5972 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____5973 =
                             let uu____5976 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____5976]  in
                           uu____5972 :: uu____5973  in
                         uu____5968 :: uu____5969  in
                       uu____5964 :: uu____5965  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____5962 uu____5963  in
                   uu____5961 FStar_Pervasives_Native.None uu____5960  in
                 let default_case =
                   let post_k =
                     let uu____5983 =
                       let uu____5990 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____5990]  in
                     let uu____5991 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____5983 uu____5991  in
                   let kwp =
                     let uu____5997 =
                       let uu____6004 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6004]  in
                     let uu____6005 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____5997 uu____6005  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6010 =
                       let uu____6011 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6011]  in
                     let uu____6012 =
                       let uu____6013 =
                         let uu____6016 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6016
                          in
                       let uu____6017 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6013 uu____6017  in
                     FStar_Syntax_Util.abs uu____6010 uu____6012
                       (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Util.mk_residual_comp
                             FStar_Parser_Const.effect_Tot_lid
                             FStar_Pervasives_Native.None
                             [FStar_Syntax_Syntax.TOTAL]))
                      in
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       FStar_Parser_Const.effect_PURE_lid
                      in
                   mk_comp md u_res_t res_t wp []  in
                 let maybe_return eff_label_then cthen =
                   let uu____6033 =
                     should_not_inline_whole_match ||
                       (let uu____6035 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6035)
                      in
                   if uu____6033 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6067  ->
                        fun celse  ->
                          match uu____6067 with
                          | (g,eff_label,uu____6083,cthen) ->
                              let uu____6093 =
                                let uu____6118 =
                                  let uu____6119 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6119
                                   in
                                lift_and_destruct env uu____6118 celse  in
                              (match uu____6093 with
                               | ((md,uu____6121,uu____6122),(uu____6123,uu____6124,wp_then),
                                  (uu____6126,uu____6127,wp_else)) ->
                                   let uu____6147 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____6147 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____6160::[] -> comp
                 | uu____6197 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____6214 = destruct_comp comp1  in
                     (match uu____6214 with
                      | (uu____6221,uu____6222,wp) ->
                          let wp1 =
                            let uu____6227 =
                              let uu____6228 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____6229 =
                                let uu____6230 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____6231 =
                                  let uu____6234 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____6234]  in
                                uu____6230 :: uu____6231  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6228
                                uu____6229
                               in
                            uu____6227 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos
                             in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags))
               in
            FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags
              bind_cases
  
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____6261 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6261 with
          | FStar_Pervasives_Native.None  ->
              let uu____6270 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____6275 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____6270 uu____6275
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let is_type1 t1 =
            let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
            let uu____6308 =
              let uu____6309 = FStar_Syntax_Subst.compress t2  in
              uu____6309.FStar_Syntax_Syntax.n  in
            match uu____6308 with
            | FStar_Syntax_Syntax.Tm_type uu____6312 -> true
            | uu____6313 -> false  in
          let uu____6314 =
            let uu____6315 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____6315.FStar_Syntax_Syntax.n  in
          match uu____6314 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____6323 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                FStar_Syntax_Syntax.fvar
                  (FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                     e.FStar_Syntax_Syntax.pos)
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____6334 =
                  let uu____6335 =
                    let uu____6336 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____6336
                     in
                  (FStar_Pervasives_Native.None, uu____6335)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____6334
                 in
              let e1 =
                let uu____6346 =
                  let uu____6347 =
                    let uu____6348 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____6348]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____6347  in
                uu____6346 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____6353 -> (e, lc)
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let use_eq =
            env.FStar_TypeChecker_Env.use_eq ||
              (let uu____6382 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____6382 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____6405 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____6427 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____6427, false)
            else
              (let uu____6433 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____6433, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____6444) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____6453 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____6453 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___117_6467 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___117_6467.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___117_6467.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___117_6467.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____6472 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____6472 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___118_6480 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___118_6480.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___118_6480.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___118_6480.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___119_6483 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___119_6483.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___119_6483.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___119_6483.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____6487 =
                     let uu____6488 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____6488
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____6491 =
                          let uu____6492 = FStar_Syntax_Subst.compress f1  in
                          uu____6492.FStar_Syntax_Syntax.n  in
                        match uu____6491 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____6495,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____6497;
                                          FStar_Syntax_Syntax.vars =
                                            uu____6498;_},uu____6499)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___120_6525 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___120_6525.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___120_6525.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___120_6525.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____6526 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____6529 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6529
                              then
                                let uu____6530 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____6531 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____6532 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____6533 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____6530 uu____6531 uu____6532 uu____6533
                              else ());
                             (let u_t_opt = comp_univ_opt c  in
                              let x =
                                FStar_Syntax_Syntax.new_bv
                                  (FStar_Pervasives_Native.Some
                                     (t.FStar_Syntax_Syntax.pos)) t
                                 in
                              let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                              let cret = return_value env u_t_opt t xexp  in
                              let guard =
                                if apply_guard1
                                then
                                  let uu____6546 =
                                    let uu____6547 =
                                      let uu____6548 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____6548]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____6547
                                     in
                                  uu____6546 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____6552 =
                                let uu____6557 =
                                  FStar_All.pipe_left
                                    (fun _0_40  ->
                                       FStar_Pervasives_Native.Some _0_40)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____6570 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____6571 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____6572 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____6557 uu____6570
                                  e uu____6571 uu____6572
                                 in
                              match uu____6552 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___121_6576 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___121_6576.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___121_6576.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____6578 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____6578
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____6583 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____6583
                                    then
                                      let uu____6584 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____6584
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___87_6594  ->
                             match uu___87_6594 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____6597 -> []))
                      in
                   let lc1 =
                     let uu____6599 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____6599 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___122_6601 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___122_6601.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___122_6601.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___122_6601.FStar_TypeChecker_Env.implicits)
                     }  in
                   (e, lc1, g2))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____6624 =
          let uu____6625 =
            let uu____6626 =
              let uu____6627 =
                let uu____6628 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____6628  in
              [uu____6627]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____6626  in
          uu____6625 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____6624  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____6635 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____6635
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____6653 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____6668 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             if
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____6697)::(ens,uu____6699)::uu____6700 ->
                    let uu____6729 =
                      let uu____6732 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____6732  in
                    let uu____6733 =
                      let uu____6734 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____6734  in
                    (uu____6729, uu____6733)
                | uu____6737 ->
                    let uu____6746 =
                      let uu____6751 =
                        let uu____6752 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____6752
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____6751)
                       in
                    FStar_Errors.raise_error uu____6746
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____6768)::uu____6769 ->
                    let uu____6788 =
                      let uu____6793 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____6793
                       in
                    (match uu____6788 with
                     | (us_r,uu____6825) ->
                         let uu____6826 =
                           let uu____6831 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____6831
                            in
                         (match uu____6826 with
                          | (us_e,uu____6863) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____6866 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_requires r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6866
                                  us_r
                                 in
                              let as_ens =
                                let uu____6868 =
                                  FStar_Syntax_Syntax.fvar
                                    (FStar_Ident.set_lid_range
                                       FStar_Parser_Const.as_ensures r)
                                    FStar_Syntax_Syntax.Delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____6868
                                  us_e
                                 in
                              let req =
                                let uu____6872 =
                                  let uu____6873 =
                                    let uu____6874 =
                                      let uu____6885 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6885]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6874
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____6873
                                   in
                                uu____6872 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____6903 =
                                  let uu____6904 =
                                    let uu____6905 =
                                      let uu____6916 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6916]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6905
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6904
                                   in
                                uu____6903 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____6931 =
                                let uu____6934 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____6934  in
                              let uu____6935 =
                                let uu____6936 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____6936  in
                              (uu____6931, uu____6935)))
                | uu____6939 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
         in
      (let uu____6965 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____6965
       then
         let uu____6966 = FStar_Syntax_Print.term_to_string tm  in
         let uu____6967 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6966 uu____6967
       else ());
      tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun head1  ->
      fun arg  ->
        let tm =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
            FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
           in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Reify;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
           in
        (let uu____6985 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____6985
         then
           let uu____6986 = FStar_Syntax_Print.term_to_string tm  in
           let uu____6987 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6986
             uu____6987
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____6992 =
      let uu____6993 =
        let uu____6994 = FStar_Syntax_Subst.compress t  in
        uu____6994.FStar_Syntax_Syntax.n  in
      match uu____6993 with
      | FStar_Syntax_Syntax.Tm_app uu____6997 -> false
      | uu____7012 -> true  in
    if uu____6992
    then t
    else
      (let uu____7014 = FStar_Syntax_Util.head_and_args t  in
       match uu____7014 with
       | (head1,args) ->
           let uu____7051 =
             let uu____7052 =
               let uu____7053 = FStar_Syntax_Subst.compress head1  in
               uu____7053.FStar_Syntax_Syntax.n  in
             match uu____7052 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7056 -> false  in
           if uu____7051
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7078 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard)
        else
          (let number_of_implicits t1 =
             let uu____7115 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____7115 with
             | (formals,uu____7129) ->
                 let n_implicits =
                   let uu____7147 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____7223  ->
                             match uu____7223 with
                             | (uu____7230,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____7147 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____7361 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____7361 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____7385 =
                     let uu____7390 =
                       let uu____7391 = FStar_Util.string_of_int n_expected
                          in
                       let uu____7398 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____7399 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____7391 uu____7398 uu____7399
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____7390)
                      in
                   let uu____7406 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____7385 uu____7406
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___88_7427 =
             match uu___88_7427 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____7457 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____7457 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_41,uu____7566) when
                          _0_41 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____7609,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____7642 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____7642 with
                           | (v1,uu____7682,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____7699 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____7699 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7792 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7792)))
                      | (uu____7819,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____7865 =
                      let uu____7892 = inst_n_binders t  in
                      aux [] uu____7892 bs1  in
                    (match uu____7865 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7963) -> (e, torig, guard)
                          | (uu____7994,[]) when
                              let uu____8025 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____8025 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8026 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8058 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____8073 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____8081 =
      let uu____8084 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____8084
        (FStar_List.map
           (fun u  ->
              let uu____8094 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____8094 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____8081 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____8111 = FStar_Util.set_is_empty x  in
      if uu____8111
      then []
      else
        (let s =
           let uu____8118 =
             let uu____8121 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____8121  in
           FStar_All.pipe_right uu____8118 FStar_Util.set_elements  in
         (let uu____8129 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____8129
          then
            let uu____8130 =
              let uu____8131 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____8131  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____8130
          else ());
         (let r =
            let uu____8138 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____8138  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____8153 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____8153
                     then
                       let uu____8154 =
                         let uu____8155 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____8155
                          in
                       let uu____8156 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____8157 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____8154 uu____8156 uu____8157
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name))
             in
          u_names))
  
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames1 =
        let uu____8179 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____8179 FStar_Util.set_elements  in
      univnames1
  
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____8211) -> generalized_univ_names
        | (uu____8218,[]) -> explicit_univ_names
        | uu____8225 ->
            let uu____8234 =
              let uu____8239 =
                let uu____8240 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____8240
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____8239)
               in
            FStar_Errors.raise_error uu____8234 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____8254 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____8254
       then
         let uu____8255 = FStar_Syntax_Print.term_to_string t  in
         let uu____8256 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____8255 uu____8256
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____8262 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____8262
        then
          let uu____8263 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____8263
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____8269 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____8269
         then
           let uu____8270 = FStar_Syntax_Print.term_to_string t  in
           let uu____8271 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____8270 uu____8271
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
         (univs2, ts))))
  
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_name Prims.list,
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder
                                                              Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____8341 =
          let uu____8342 =
            FStar_Util.for_all
              (fun uu____8355  ->
                 match uu____8355 with
                 | (uu____8364,uu____8365,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____8342  in
        if uu____8341
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____8411 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____8411
              then
                let uu____8412 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____8412
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.NoDeltaSteps] env c
                 in
              (let uu____8416 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____8416
               then
                 let uu____8417 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____8417
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____8478 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____8478 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____8608 =
             match uu____8608 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____8674 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____8674
                   then
                     let uu____8675 =
                       let uu____8676 =
                         let uu____8679 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____8679
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____8676
                         (FStar_String.concat ", ")
                        in
                     let uu____8706 =
                       let uu____8707 =
                         let uu____8710 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____8710
                           (FStar_List.map
                              (fun uu____8738  ->
                                 match uu____8738 with
                                 | (u,t2) ->
                                     let uu____8745 =
                                       FStar_Syntax_Print.uvar_to_string u
                                        in
                                     let uu____8746 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     FStar_Util.format2 "(%s : %s)"
                                       uu____8745 uu____8746))
                          in
                       FStar_All.pipe_right uu____8707
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8675
                       uu____8706
                   else ());
                  (let univs2 =
                     let uu____8753 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uu____8776  ->
                            match uu____8776 with
                            | (uu____8785,t2) ->
                                let uu____8787 = FStar_Syntax_Free.univs t2
                                   in
                                FStar_Util.set_union univs2 uu____8787)
                       univs1 uu____8753
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____8810 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____8810
                    then
                      let uu____8811 =
                        let uu____8812 =
                          let uu____8815 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____8815
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____8812
                          (FStar_String.concat ", ")
                         in
                      let uu____8842 =
                        let uu____8843 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun uu____8875  ->
                                  match uu____8875 with
                                  | (u,t2) ->
                                      let uu____8882 =
                                        FStar_Syntax_Print.uvar_to_string u
                                         in
                                      let uu____8883 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t2
                                         in
                                      FStar_Util.format2 "(%s : %s)"
                                        uu____8882 uu____8883))
                           in
                        FStar_All.pipe_right uu____8843
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8811
                        uu____8842
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____8913 =
             let uu____8946 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____8946  in
           match uu____8913 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9064 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____9064
                 then ()
                 else
                   (let uu____9066 = lec_hd  in
                    match uu____9066 with
                    | (lb1,uu____9074,uu____9075) ->
                        let uu____9076 = lec2  in
                        (match uu____9076 with
                         | (lb2,uu____9084,uu____9085) ->
                             let msg =
                               let uu____9087 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9088 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9087 uu____9088
                                in
                             let uu____9089 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9089))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun uu____9200  ->
                           match uu____9200 with
                           | (u,uu____9208) ->
                               FStar_All.pipe_right u21
                                 (FStar_Util.for_some
                                    (fun uu____9230  ->
                                       match uu____9230 with
                                       | (u',uu____9238) ->
                                           FStar_Syntax_Unionfind.equiv u u'))))
                    in
                 let uu____9243 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____9243
                 then ()
                 else
                   (let uu____9245 = lec_hd  in
                    match uu____9245 with
                    | (lb1,uu____9253,uu____9254) ->
                        let uu____9255 = lec2  in
                        (match uu____9255 with
                         | (lb2,uu____9263,uu____9264) ->
                             let msg =
                               let uu____9266 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9267 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9266 uu____9267
                                in
                             let uu____9268 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9268))
                  in
               let lecs1 =
                 let uu____9278 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9337 = univs_and_uvars_of_lec this_lec  in
                        match uu____9337 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9278 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____9490 = lec_hd  in
                   match uu____9490 with
                   | (lbname,e,c) ->
                       let uu____9500 =
                         let uu____9505 =
                           let uu____9506 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____9507 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____9508 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____9506 uu____9507 uu____9508
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____9505)
                          in
                       let uu____9509 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____9500 uu____9509
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun uu____9539  ->
                         match uu____9539 with
                         | (u,k) ->
                             let uu____9552 = FStar_Syntax_Unionfind.find u
                                in
                             (match uu____9552 with
                              | FStar_Pervasives_Native.Some uu____9561 ->
                                  failwith
                                    "Unexpected instantiation of mutually recursive uvar"
                              | uu____9568 ->
                                  let k1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta;
                                      FStar_TypeChecker_Normalize.Exclude
                                        FStar_TypeChecker_Normalize.Zeta] env
                                      k
                                     in
                                  let uu____9572 =
                                    FStar_Syntax_Util.arrow_formals k1  in
                                  (match uu____9572 with
                                   | (bs,kres) ->
                                       ((let uu____9610 =
                                           let uu____9611 =
                                             let uu____9614 =
                                               FStar_TypeChecker_Normalize.unfold_whnf
                                                 env kres
                                                in
                                             FStar_Syntax_Util.unrefine
                                               uu____9614
                                              in
                                           uu____9611.FStar_Syntax_Syntax.n
                                            in
                                         match uu____9610 with
                                         | FStar_Syntax_Syntax.Tm_type
                                             uu____9615 ->
                                             let free =
                                               FStar_Syntax_Free.names kres
                                                in
                                             let uu____9619 =
                                               let uu____9620 =
                                                 FStar_Util.set_is_empty free
                                                  in
                                               Prims.op_Negation uu____9620
                                                in
                                             if uu____9619
                                             then fail1 kres
                                             else ()
                                         | uu____9622 -> fail1 kres);
                                        (let a =
                                           let uu____9624 =
                                             let uu____9627 =
                                               FStar_TypeChecker_Env.get_range
                                                 env
                                                in
                                             FStar_All.pipe_left
                                               (fun _0_42  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_42) uu____9627
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____9624 kres
                                            in
                                         let t =
                                           let uu____9631 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Util.abs bs
                                             uu____9631
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.residual_tot
                                                   kres))
                                            in
                                         FStar_Syntax_Util.set_uvar u t;
                                         (a,
                                           (FStar_Pervasives_Native.Some
                                              FStar_Syntax_Syntax.imp_tag))))))))
                  in
               let gen_univs1 = gen_univs env univs1  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____9750  ->
                         match uu____9750 with
                         | (lbname,e,c) ->
                             let uu____9796 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____9865 ->
                                   let uu____9880 = (e, c)  in
                                   (match uu____9880 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.NoDeltaSteps;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta]
                                            env c
                                           in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e
                                           in
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____9917  ->
                                                   match uu____9917 with
                                                   | (x,uu____9925) ->
                                                       let uu____9930 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9930)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9940 =
                                                let uu____9941 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9941
                                                 in
                                              if uu____9940
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  FStar_Pervasives_Native.None
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____9949 =
                                            let uu____9950 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____9950.FStar_Syntax_Syntax.n
                                             in
                                          match uu____9949 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9973 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____9973 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9988 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____9990 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____9990, gen_tvars))
                                in
                             (match uu____9796 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____10136 = Obj.magic ()  in ());
        (let uu____10138 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____10138
         then
           let uu____10139 =
             let uu____10140 =
               FStar_List.map
                 (fun uu____10153  ->
                    match uu____10153 with
                    | (lb,uu____10161,uu____10162) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____10140 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____10139
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10183  ->
                match uu____10183 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____10212 = gen env is_rec lecs  in
           match uu____10212 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10311  ->
                       match uu____10311 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10373 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____10373
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10417  ->
                           match uu____10417 with
                           | (l,us,e,c,gvs) ->
                               let uu____10451 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____10452 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____10453 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____10454 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____10455 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____10451 uu____10452 uu____10453
                                 uu____10454 uu____10455))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____10496  ->
                match uu____10496 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____10540 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____10540, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____10583 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____10583 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____10589 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____10589)
             in
          let is_var e1 =
            let uu____10596 =
              let uu____10597 = FStar_Syntax_Subst.compress e1  in
              uu____10597.FStar_Syntax_Syntax.n  in
            match uu____10596 with
            | FStar_Syntax_Syntax.Tm_name uu____10600 -> true
            | uu____10601 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___123_10617 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___123_10617.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___123_10617.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____10618 -> e2  in
          let env2 =
            let uu___124_10620 = env1  in
            let uu____10621 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___124_10620.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___124_10620.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___124_10620.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___124_10620.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___124_10620.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___124_10620.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___124_10620.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___124_10620.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___124_10620.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___124_10620.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___124_10620.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___124_10620.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___124_10620.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___124_10620.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___124_10620.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____10621;
              FStar_TypeChecker_Env.is_iface =
                (uu___124_10620.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___124_10620.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___124_10620.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___124_10620.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___124_10620.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___124_10620.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___124_10620.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___124_10620.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___124_10620.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___124_10620.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___124_10620.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___124_10620.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___124_10620.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___124_10620.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.splice =
                (uu___124_10620.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___124_10620.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___124_10620.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___124_10620.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___124_10620.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___124_10620.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____10622 = check1 env2 t1 t2  in
          match uu____10622 with
          | FStar_Pervasives_Native.None  ->
              let uu____10629 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____10634 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____10629 uu____10634
          | FStar_Pervasives_Native.Some g ->
              ((let uu____10641 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10641
                then
                  let uu____10642 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____10642
                else ());
               (let uu____10644 = decorate e t2  in (uu____10644, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g1 =
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          FStar_Syntax_Util.is_pure_lcomp lc  in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
        let uu____10672 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____10672
        then
          let uu____10677 = discharge g1  in
          let uu____10678 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____10677, uu____10678)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm]  in
           let c1 =
             let uu____10685 =
               let uu____10686 =
                 let uu____10687 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____10687 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____10686
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____10685
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____10689 = destruct_comp c1  in
           match uu____10689 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____10706 = FStar_TypeChecker_Env.get_range env  in
                 let uu____10707 =
                   let uu____10708 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____10709 =
                     let uu____10710 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____10711 =
                       let uu____10714 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____10714]  in
                     uu____10710 :: uu____10711  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____10708 uu____10709  in
                 uu____10707 FStar_Pervasives_Native.None uu____10706  in
               ((let uu____10718 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____10718
                 then
                   let uu____10719 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____10719
                 else ());
                (let g2 =
                   let uu____10722 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____10722  in
                 let uu____10723 = discharge g2  in
                 let uu____10724 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____10723, uu____10724))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___89_10748 =
        match uu___89_10748 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____10756)::[] -> f fst1
        | uu____10773 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____10778 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____10778
          (fun _0_44  -> FStar_TypeChecker_Common.NonTrivial _0_44)
         in
      let op_or_e e =
        let uu____10787 =
          let uu____10790 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____10790  in
        FStar_All.pipe_right uu____10787
          (fun _0_45  -> FStar_TypeChecker_Common.NonTrivial _0_45)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_46  -> FStar_TypeChecker_Common.NonTrivial _0_46)
         in
      let op_or_t t =
        let uu____10801 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____10801
          (fun _0_47  -> FStar_TypeChecker_Common.NonTrivial _0_47)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_48  -> FStar_TypeChecker_Common.NonTrivial _0_48)
         in
      let short_op_ite uu___90_10815 =
        match uu___90_10815 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10823)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10842)::[] ->
            let uu____10871 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____10871
              (fun _0_49  -> FStar_TypeChecker_Common.NonTrivial _0_49)
        | uu____10876 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____10886 =
          let uu____10893 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____10893)  in
        let uu____10898 =
          let uu____10907 =
            let uu____10914 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____10914)  in
          let uu____10919 =
            let uu____10928 =
              let uu____10935 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____10935)  in
            let uu____10940 =
              let uu____10949 =
                let uu____10956 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____10956)  in
              let uu____10961 =
                let uu____10970 =
                  let uu____10977 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____10977)  in
                [uu____10970; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____10949 :: uu____10961  in
            uu____10928 :: uu____10940  in
          uu____10907 :: uu____10919  in
        uu____10886 :: uu____10898  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____11028 =
            FStar_Util.find_map table
              (fun uu____11041  ->
                 match uu____11041 with
                 | (x,mk1) ->
                     if FStar_Ident.lid_equals x lid
                     then
                       let uu____11058 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____11058
                     else FStar_Pervasives_Native.None)
             in
          (match uu____11028 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11061 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____11065 =
      let uu____11066 = FStar_Syntax_Util.un_uinst l  in
      uu____11066.FStar_Syntax_Syntax.n  in
    match uu____11065 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11070 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11094)::uu____11095 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11106 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____11113,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11114))::uu____11115 -> bs
      | uu____11132 ->
          let uu____11133 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____11133 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11137 =
                 let uu____11138 = FStar_Syntax_Subst.compress t  in
                 uu____11138.FStar_Syntax_Syntax.n  in
               (match uu____11137 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11142) ->
                    let uu____11159 =
                      FStar_Util.prefix_until
                        (fun uu___91_11199  ->
                           match uu___91_11199 with
                           | (uu____11206,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11207)) ->
                               false
                           | uu____11210 -> true) bs'
                       in
                    (match uu____11159 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11245,uu____11246) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____11318,uu____11319) ->
                         let uu____11392 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____11410  ->
                                   match uu____11410 with
                                   | (x,uu____11418) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____11392
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____11465  ->
                                     match uu____11465 with
                                     | (x,i) ->
                                         let uu____11484 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____11484, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____11494 -> bs))
  
let (maybe_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1  in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2  in
            if
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
            then e
            else
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____11526 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____11526
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (d : Prims.string -> Prims.unit) =
  fun s  -> FStar_Util.print1 "\027[01;36m%s\027[00m\n" s 
let (mk_toplevel_definition :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____11549 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____11549
         then
           (d (FStar_Ident.text_of_lid lident);
            (let uu____11551 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               (FStar_Ident.text_of_lid lident) uu____11551))
         else ());
        (let fv =
           let uu____11554 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____11554
             FStar_Pervasives_Native.None
            in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [FStar_Syntax_Util.mk_letbinding lbname []
                FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def
                [] FStar_Range.dummyRange])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident]))
            in
         let uu____11564 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___125_11570 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___125_11570.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___125_11570.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___125_11570.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___125_11570.FStar_Syntax_Syntax.sigattrs)
           }), uu____11564))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun env  ->
    fun se  ->
      let visibility uu___92_11580 =
        match uu___92_11580 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11581 -> false  in
      let reducibility uu___93_11585 =
        match uu___93_11585 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____11586 -> false  in
      let assumption uu___94_11590 =
        match uu___94_11590 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____11591 -> false  in
      let reification uu___95_11595 =
        match uu___95_11595 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____11596 -> true
        | uu____11597 -> false  in
      let inferred uu___96_11601 =
        match uu___96_11601 with
        | FStar_Syntax_Syntax.Discriminator uu____11602 -> true
        | FStar_Syntax_Syntax.Projector uu____11603 -> true
        | FStar_Syntax_Syntax.RecordType uu____11608 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____11617 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____11626 -> false  in
      let has_eq uu___97_11630 =
        match uu___97_11630 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____11631 -> false  in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (inferred x))
                         || (visibility x))
                        || (assumption x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Inline_for_extraction)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.New  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (assumption x)))
        | FStar_Syntax_Syntax.Inline_for_extraction  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (visibility x))
                          || (reducibility x))
                         || (reification x))
                        || (inferred x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Assumption)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Visible_default  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Irreducible  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Abstract  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Noeq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Unopteq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.TotalEffect  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (reification x)))
        | FStar_Syntax_Syntax.Logic  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) ||
                        (inferred x))
                       || (visibility x))
                      || (reducibility x)))
        | FStar_Syntax_Syntax.Reifiable  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Reflectable uu____11691 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11696 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____11700 =
        let uu____11701 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___98_11705  ->
                  match uu___98_11705 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11706 -> false))
           in
        FStar_All.pipe_right uu____11701 Prims.op_Negation  in
      if uu____11700
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____11719 =
            let uu____11724 =
              let uu____11725 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11725 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11724)  in
          FStar_Errors.raise_error uu____11719 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____11733 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11737 =
            let uu____11738 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____11738  in
          if uu____11737 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11743),uu____11744) ->
              ((let uu____11760 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____11760
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11764 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____11764
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11770 ->
              let uu____11779 =
                let uu____11780 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____11780  in
              if uu____11779 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11786 ->
              let uu____11793 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____11793 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11797 ->
              let uu____11804 =
                let uu____11805 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____11805  in
              if uu____11804 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11811 ->
              let uu____11812 =
                let uu____11813 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11813  in
              if uu____11812 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11819 ->
              let uu____11820 =
                let uu____11821 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11821  in
              if uu____11820 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11827 ->
              let uu____11840 =
                let uu____11841 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____11841  in
              if uu____11840 then err'1 () else ()
          | uu____11847 -> ()))
      else ()
  
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      Prims.bool ->
        FStar_TypeChecker_Env.env ->
          FStar_Ident.lident ->
            FStar_Ident.lident ->
              FStar_Syntax_Syntax.univ_names ->
                FStar_Syntax_Syntax.binders ->
                  FStar_Syntax_Syntax.binders ->
                    FStar_Syntax_Syntax.binders ->
                      FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun refine_domain  ->
        fun env  ->
          fun tc  ->
            fun lid  ->
              fun uvs  ->
                fun inductive_tps  ->
                  fun indices  ->
                    fun fields  ->
                      let p = FStar_Ident.range_of_lid lid  in
                      let pos q = FStar_Syntax_Syntax.withinfo q p  in
                      let projectee ptyp =
                        FStar_Syntax_Syntax.gen_bv "projectee"
                          (FStar_Pervasives_Native.Some p) ptyp
                         in
                      let inst_univs =
                        FStar_List.map
                          (fun u  -> FStar_Syntax_Syntax.U_name u) uvs
                         in
                      let tps = inductive_tps  in
                      let arg_typ =
                        let inst_tc =
                          let uu____11910 =
                            let uu____11913 =
                              let uu____11914 =
                                let uu____11921 =
                                  let uu____11922 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.Delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____11922
                                   in
                                (uu____11921, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____11914  in
                            FStar_Syntax_Syntax.mk uu____11913  in
                          uu____11910 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____11963  ->
                                  match uu____11963 with
                                  | (x,imp) ->
                                      let uu____11974 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____11974, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____11976 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____11976  in
                      let arg_binder =
                        if Prims.op_Negation refine_domain
                        then unrefined_arg_binder
                        else
                          (let disc_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some p) arg_typ
                              in
                           let sort =
                             let disc_fvar =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range disc_name p)
                                 FStar_Syntax_Syntax.Delta_equational
                                 FStar_Pervasives_Native.None
                                in
                             let uu____11985 =
                               let uu____11986 =
                                 let uu____11987 =
                                   let uu____11988 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____11989 =
                                     let uu____11990 =
                                       let uu____11991 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____11991
                                        in
                                     [uu____11990]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____11988
                                     uu____11989
                                    in
                                 uu____11987 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____11986  in
                             FStar_Syntax_Util.refine x uu____11985  in
                           let uu____11994 =
                             let uu___126_11995 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___126_11995.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___126_11995.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____11994)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____12010 =
                          FStar_List.map
                            (fun uu____12032  ->
                               match uu____12032 with
                               | (x,uu____12044) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____12010 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____12093  ->
                                match uu____12093 with
                                | (x,uu____12105) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let discriminator_ses =
                        if fvq <> FStar_Syntax_Syntax.Data_ctor
                        then []
                        else
                          (let discriminator_name =
                             FStar_Syntax_Util.mk_discriminator lid  in
                           let no_decl = false  in
                           let only_decl =
                             (let uu____12119 =
                                FStar_TypeChecker_Env.current_module env  in
                              FStar_Ident.lid_equals
                                FStar_Parser_Const.prims_lid uu____12119)
                               ||
                               (let uu____12121 =
                                  let uu____12122 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____12122.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____12121)
                              in
                           let quals =
                             let uu____12126 =
                               FStar_List.filter
                                 (fun uu___99_12130  ->
                                    match uu___99_12130 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____12131 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____12126
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____12152 =
                                 let uu____12153 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____12153  in
                               FStar_Syntax_Syntax.mk_Total uu____12152  in
                             let uu____12154 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____12154
                              in
                           let decl =
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng =
                                 (FStar_Ident.range_of_lid discriminator_name);
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____12157 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____12157
                            then
                              let uu____12158 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____12158
                            else ());
                           if only_decl
                           then [decl]
                           else
                             (let body =
                                if Prims.op_Negation refine_domain
                                then FStar_Syntax_Util.exp_true_bool
                                else
                                  (let arg_pats =
                                     FStar_All.pipe_right all_params
                                       (FStar_List.mapi
                                          (fun j  ->
                                             fun uu____12211  ->
                                               match uu____12211 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____12235 =
                                                       let uu____12238 =
                                                         let uu____12239 =
                                                           let uu____12246 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____12246,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____12239
                                                          in
                                                       pos uu____12238  in
                                                     (uu____12235, b)
                                                   else
                                                     (let uu____12250 =
                                                        let uu____12253 =
                                                          let uu____12254 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____12254
                                                           in
                                                        pos uu____12253  in
                                                      (uu____12250, b))))
                                      in
                                   let pat_true =
                                     let uu____12272 =
                                       let uu____12275 =
                                         let uu____12276 =
                                           let uu____12289 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.Delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____12289, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____12276
                                          in
                                       pos uu____12275  in
                                     (uu____12272,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____12323 =
                                       let uu____12326 =
                                         let uu____12327 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____12327
                                          in
                                       pos uu____12326  in
                                     (uu____12323,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____12339 =
                                     let uu____12342 =
                                       let uu____12343 =
                                         let uu____12366 =
                                           let uu____12369 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____12370 =
                                             let uu____12373 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____12373]  in
                                           uu____12369 :: uu____12370  in
                                         (arg_exp, uu____12366)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12343
                                        in
                                     FStar_Syntax_Syntax.mk uu____12342  in
                                   uu____12339 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____12380 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____12380
                                then
                                  FStar_Syntax_Syntax.Delta_abstract
                                    FStar_Syntax_Syntax.Delta_equational
                                else FStar_Syntax_Syntax.Delta_equational  in
                              let imp =
                                FStar_Syntax_Util.abs binders body
                                  FStar_Pervasives_Native.None
                                 in
                              let lbtyp =
                                if no_decl
                                then t
                                else FStar_Syntax_Syntax.tun  in
                              let lb =
                                let uu____12388 =
                                  let uu____12393 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____12393  in
                                let uu____12394 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____12388
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____12394 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____12400 =
                                  let uu____12401 =
                                    let uu____12408 =
                                      let uu____12411 =
                                        let uu____12412 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____12412
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____12411]  in
                                    ((false, [lb]), uu____12408)  in
                                  FStar_Syntax_Syntax.Sig_let uu____12401  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____12400;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____12430 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____12430
                               then
                                 let uu____12431 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____12431
                               else ());
                              [decl; impl]))
                         in
                      let arg_exp =
                        FStar_Syntax_Syntax.bv_to_name
                          (FStar_Pervasives_Native.fst arg_binder)
                         in
                      let binders =
                        FStar_List.append imp_binders [arg_binder]  in
                      let arg =
                        FStar_Syntax_Util.arg_of_non_null_binder arg_binder
                         in
                      let subst1 =
                        FStar_All.pipe_right fields
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____12473  ->
                                  match uu____12473 with
                                  | (a,uu____12479) ->
                                      let uu____12480 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____12480 with
                                       | (field_name,uu____12486) ->
                                           let field_proj_tm =
                                             let uu____12488 =
                                               let uu____12489 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   FStar_Syntax_Syntax.Delta_equational
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____12489
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____12488 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____12506 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____12538  ->
                                    match uu____12538 with
                                    | (x,uu____12546) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____12548 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____12548 with
                                         | (field_name,uu____12556) ->
                                             let t =
                                               let uu____12558 =
                                                 let uu____12559 =
                                                   let uu____12562 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____12562
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____12559
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____12558
                                                in
                                             let only_decl =
                                               (let uu____12566 =
                                                  FStar_TypeChecker_Env.current_module
                                                    env
                                                   in
                                                FStar_Ident.lid_equals
                                                  FStar_Parser_Const.prims_lid
                                                  uu____12566)
                                                 ||
                                                 (let uu____12568 =
                                                    let uu____12569 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____12569.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____12568)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____12583 =
                                                   FStar_List.filter
                                                     (fun uu___100_12587  ->
                                                        match uu___100_12587
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____12588 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____12583
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___101_12601  ->
                                                         match uu___101_12601
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____12602 ->
                                                             false))
                                                  in
                                               quals
                                                 ((FStar_Syntax_Syntax.Projector
                                                     (lid,
                                                       (x.FStar_Syntax_Syntax.ppname)))
                                                 :: iquals1)
                                                in
                                             let attrs =
                                               if only_decl
                                               then []
                                               else
                                                 [FStar_Syntax_Util.attr_substitute]
                                                in
                                             let decl =
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   (FStar_Ident.range_of_lid
                                                      field_name);
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____12621 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____12621
                                               then
                                                 let uu____12622 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____12622
                                               else ());
                                              if only_decl
                                              then [decl]
                                              else
                                                (let projection =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                     FStar_Pervasives_Native.None
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let arg_pats =
                                                   FStar_All.pipe_right
                                                     all_params
                                                     (FStar_List.mapi
                                                        (fun j  ->
                                                           fun uu____12670 
                                                             ->
                                                             match uu____12670
                                                             with
                                                             | (x1,imp) ->
                                                                 let b =
                                                                   FStar_Syntax_Syntax.is_implicit
                                                                    imp
                                                                    in
                                                                 if
                                                                   (i + ntps)
                                                                    = j
                                                                 then
                                                                   let uu____12694
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____12694,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____12710
                                                                    =
                                                                    let uu____12713
                                                                    =
                                                                    let uu____12714
                                                                    =
                                                                    let uu____12721
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____12721,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____12714
                                                                     in
                                                                    pos
                                                                    uu____12713
                                                                     in
                                                                    (uu____12710,
                                                                    b))
                                                                   else
                                                                    (let uu____12725
                                                                    =
                                                                    let uu____12728
                                                                    =
                                                                    let uu____12729
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____12729
                                                                     in
                                                                    pos
                                                                    uu____12728
                                                                     in
                                                                    (uu____12725,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____12745 =
                                                     let uu____12748 =
                                                       let uu____12749 =
                                                         let uu____12762 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____12762,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____12749
                                                        in
                                                     pos uu____12748  in
                                                   let uu____12771 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____12745,
                                                     FStar_Pervasives_Native.None,
                                                     uu____12771)
                                                    in
                                                 let body =
                                                   let uu____12783 =
                                                     let uu____12786 =
                                                       let uu____12787 =
                                                         let uu____12810 =
                                                           let uu____12813 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____12813]  in
                                                         (arg_exp,
                                                           uu____12810)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____12787
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____12786
                                                      in
                                                   uu____12783
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____12821 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____12821
                                                   then
                                                     FStar_Syntax_Syntax.Delta_abstract
                                                       FStar_Syntax_Syntax.Delta_equational
                                                   else
                                                     FStar_Syntax_Syntax.Delta_equational
                                                    in
                                                 let lbtyp =
                                                   if no_decl
                                                   then t
                                                   else
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let lb =
                                                   let uu____12828 =
                                                     let uu____12833 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____12833
                                                      in
                                                   let uu____12834 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____12828;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____12834;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____12840 =
                                                     let uu____12841 =
                                                       let uu____12848 =
                                                         let uu____12851 =
                                                           let uu____12852 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____12852
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____12851]  in
                                                       ((false, [lb]),
                                                         uu____12848)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____12841
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____12840;
                                                     FStar_Syntax_Syntax.sigrng
                                                       = p1;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = attrs
                                                   }  in
                                                 (let uu____12870 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____12870
                                                  then
                                                    let uu____12871 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____12871
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____12506 FStar_List.flatten
                         in
                      FStar_List.append discriminator_ses projectors_ses
  
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun tcs  ->
        fun se  ->
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_datacon
              (constr_lid,uvs,t,typ_lid,n_typars,uu____12911) when
              Prims.op_Negation
                (FStar_Ident.lid_equals constr_lid
                   FStar_Parser_Const.lexcons_lid)
              ->
              let uu____12916 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____12916 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____12938 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____12938 with
                    | (formals,uu____12954) ->
                        let uu____12971 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____13003 =
                                   let uu____13004 =
                                     let uu____13005 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____13005  in
                                   FStar_Ident.lid_equals typ_lid uu____13004
                                    in
                                 if uu____13003
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____13024,uvs',tps,typ0,uu____13028,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____13047 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              if
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____12971 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____13120 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____13120 with
                              | (indices,uu____13136) ->
                                  let refine_domain =
                                    let uu____13154 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___102_13159  ->
                                              match uu___102_13159 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____13160 -> true
                                              | uu____13169 -> false))
                                       in
                                    if uu____13154
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___103_13177 =
                                      match uu___103_13177 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____13180,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____13192 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____13193 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____13193 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.Data_ctor
                                    | FStar_Pervasives_Native.Some q -> q  in
                                  let iquals1 =
                                    if
                                      FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract iquals
                                    then FStar_Syntax_Syntax.Private ::
                                      iquals
                                    else iquals  in
                                  let fields =
                                    let uu____13204 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____13204 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____13269  ->
                                               fun uu____13270  ->
                                                 match (uu____13269,
                                                         uu____13270)
                                                 with
                                                 | ((x,uu____13288),(x',uu____13290))
                                                     ->
                                                     let uu____13299 =
                                                       let uu____13306 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____13306)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____13299) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____13307 -> []
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____13325 =
         let uu____13326 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____13326 haseq_suffix  in
       uu____13325 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    FStar_Ident.lid_of_ids
      (FStar_List.append lid.FStar_Ident.ns
         [FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)])
  
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders,
            FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple5)
  =
  fun en  ->
    fun ty  ->
      fun usubst  ->
        fun us  ->
          let uu____13380 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____13394,bs,t,uu____13397,uu____13398) ->
                (lid, bs, t)
            | uu____13407 -> failwith "Impossible!"  in
          match uu____13380 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____13429 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____13429 t  in
              let uu____13436 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____13436 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____13460 =
                       let uu____13461 = FStar_Syntax_Subst.compress t2  in
                       uu____13461.FStar_Syntax_Syntax.n  in
                     match uu____13460 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____13471) -> ibs
                     | uu____13488 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____13495 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.Delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____13496 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____13495 uu____13496
                      in
                   let ind1 =
                     let uu____13502 =
                       let uu____13503 =
                         FStar_List.map
                           (fun uu____13516  ->
                              match uu____13516 with
                              | (bv,aq) ->
                                  let uu____13527 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____13527, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____13503  in
                     uu____13502 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____13533 =
                       let uu____13534 =
                         FStar_List.map
                           (fun uu____13547  ->
                              match uu____13547 with
                              | (bv,aq) ->
                                  let uu____13558 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____13558, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____13534  in
                     uu____13533 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____13564 =
                       let uu____13565 =
                         let uu____13566 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____13566]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____13565
                        in
                     uu____13564 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____13587 =
                            let uu____13588 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____13588  in
                          FStar_TypeChecker_Rel.subtype_nosmt en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____13587) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____13599 =
                              let uu____13600 =
                                let uu____13601 =
                                  let uu____13602 =
                                    let uu____13603 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____13603
                                     in
                                  [uu____13602]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____13601
                                 in
                              uu____13600 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____13599)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___127_13610 = fml  in
                     let uu____13611 =
                       let uu____13612 =
                         let uu____13619 =
                           let uu____13620 =
                             let uu____13631 =
                               let uu____13634 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____13634]  in
                             [uu____13631]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____13620  in
                         (fml, uu____13619)  in
                       FStar_Syntax_Syntax.Tm_meta uu____13612  in
                     {
                       FStar_Syntax_Syntax.n = uu____13611;
                       FStar_Syntax_Syntax.pos =
                         (uu___127_13610.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___127_13610.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____13647 =
                              let uu____13648 =
                                let uu____13649 =
                                  let uu____13650 =
                                    let uu____13651 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____13651
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____13650  in
                                [uu____13649]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____13648
                               in
                            uu____13647 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____13676 =
                              let uu____13677 =
                                let uu____13678 =
                                  let uu____13679 =
                                    let uu____13680 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____13680
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____13679  in
                                [uu____13678]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____13677
                               in
                            uu____13676 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) bs2 fml2
                      in
                   let axiom_lid = get_haseq_axiom_lid lid  in
                   (axiom_lid, fml3, bs2, ibs1, haseq_bs))
  