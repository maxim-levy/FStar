open Prims
type free_vars_and_fvars =
  {
  tmvs: FStar_Syntax_Syntax.free_vars ;
  tyvs: FStar_Syntax_Syntax.free_vars ;
  lids: FStar_Ident.lident FStar_Util.set }[@@deriving show]
let (__proj__Mkfree_vars_and_fvars__item__tmvs :
  free_vars_and_fvars -> FStar_Syntax_Syntax.free_vars) =
  fun projectee  ->
    match projectee with
    | { tmvs = __fname__tmvs; tyvs = __fname__tyvs; lids = __fname__lids;_}
        -> __fname__tmvs
  
let (__proj__Mkfree_vars_and_fvars__item__tyvs :
  free_vars_and_fvars -> FStar_Syntax_Syntax.free_vars) =
  fun projectee  ->
    match projectee with
    | { tmvs = __fname__tmvs; tyvs = __fname__tyvs; lids = __fname__lids;_}
        -> __fname__tyvs
  
let (__proj__Mkfree_vars_and_fvars__item__lids :
  free_vars_and_fvars -> FStar_Ident.lident FStar_Util.set) =
  fun projectee  ->
    match projectee with
    | { tmvs = __fname__tmvs; tyvs = __fname__tyvs; lids = __fname__lids;_}
        -> __fname__lids
  
let (no_vars : FStar_Syntax_Syntax.free_vars) =
  {
    FStar_Syntax_Syntax.free_names = [];
    FStar_Syntax_Syntax.free_uvars = [];
    FStar_Syntax_Syntax.free_univs = [];
    FStar_Syntax_Syntax.free_univ_names = []
  } 
let (no_lids : FStar_Ident.lident FStar_Util.set) =
  FStar_Syntax_Syntax.new_fv_set () 
let (no_free_vars : free_vars_and_fvars) =
  { tmvs = no_vars; tyvs = no_vars; lids = no_lids } 
let (singleton_fvar : FStar_Syntax_Syntax.fv -> free_vars_and_fvars) =
  fun fv  ->
    let uu____64 =
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v no_lids
       in
    { tmvs = no_vars; tyvs = no_vars; lids = uu____64 }
  
let (singleton_bv : FStar_Syntax_Syntax.bv -> free_vars_and_fvars) =
  fun x  ->
    {
      tmvs =
        (let uu___23_72 = no_vars  in
         {
           FStar_Syntax_Syntax.free_names = [x];
           FStar_Syntax_Syntax.free_uvars =
             (uu___23_72.FStar_Syntax_Syntax.free_uvars);
           FStar_Syntax_Syntax.free_univs =
             (uu___23_72.FStar_Syntax_Syntax.free_univs);
           FStar_Syntax_Syntax.free_univ_names =
             (uu___23_72.FStar_Syntax_Syntax.free_univ_names)
         });
      tyvs = no_vars;
      lids = no_lids
    }
  
let (singleton_uv :
  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple2 -> free_vars_and_fvars)
  =
  fun x  ->
    {
      tmvs =
        (let uu___24_110 = no_vars  in
         {
           FStar_Syntax_Syntax.free_names =
             (uu___24_110.FStar_Syntax_Syntax.free_names);
           FStar_Syntax_Syntax.free_uvars = [x];
           FStar_Syntax_Syntax.free_univs =
             (uu___24_110.FStar_Syntax_Syntax.free_univs);
           FStar_Syntax_Syntax.free_univ_names =
             (uu___24_110.FStar_Syntax_Syntax.free_univ_names)
         });
      tyvs = no_vars;
      lids = no_lids
    }
  
let (singleton_univ :
  FStar_Syntax_Syntax.universe_uvar -> free_vars_and_fvars) =
  fun x  ->
    {
      tmvs =
        (let uu___25_148 = no_vars  in
         {
           FStar_Syntax_Syntax.free_names =
             (uu___25_148.FStar_Syntax_Syntax.free_names);
           FStar_Syntax_Syntax.free_uvars =
             (uu___25_148.FStar_Syntax_Syntax.free_uvars);
           FStar_Syntax_Syntax.free_univs = [x];
           FStar_Syntax_Syntax.free_univ_names =
             (uu___25_148.FStar_Syntax_Syntax.free_univ_names)
         });
      tyvs = no_vars;
      lids = no_lids
    }
  
let (singleton_univ_name :
  FStar_Syntax_Syntax.univ_name -> free_vars_and_fvars) =
  fun x  ->
    {
      tmvs =
        (let uu___26_154 = no_vars  in
         {
           FStar_Syntax_Syntax.free_names =
             (uu___26_154.FStar_Syntax_Syntax.free_names);
           FStar_Syntax_Syntax.free_uvars =
             (uu___26_154.FStar_Syntax_Syntax.free_uvars);
           FStar_Syntax_Syntax.free_univs =
             (uu___26_154.FStar_Syntax_Syntax.free_univs);
           FStar_Syntax_Syntax.free_univ_names = [x]
         });
      tyvs = no_vars;
      lids = no_lids
    }
  
let (union_vars :
  FStar_Syntax_Syntax.free_vars ->
    FStar_Syntax_Syntax.free_vars -> FStar_Syntax_Syntax.free_vars)
  =
  fun f1  ->
    fun f2  ->
      {
        FStar_Syntax_Syntax.free_names =
          (FStar_List.append f1.FStar_Syntax_Syntax.free_names
             f2.FStar_Syntax_Syntax.free_names);
        FStar_Syntax_Syntax.free_uvars =
          (FStar_List.append f1.FStar_Syntax_Syntax.free_uvars
             f2.FStar_Syntax_Syntax.free_uvars);
        FStar_Syntax_Syntax.free_univs =
          (FStar_List.append f1.FStar_Syntax_Syntax.free_univs
             f2.FStar_Syntax_Syntax.free_univs);
        FStar_Syntax_Syntax.free_univ_names =
          (FStar_List.append f1.FStar_Syntax_Syntax.free_univ_names
             f2.FStar_Syntax_Syntax.free_univ_names)
      }
  
let (union :
  free_vars_and_fvars -> free_vars_and_fvars -> free_vars_and_fvars) =
  fun f1  ->
    fun f2  ->
      let uu____183 = union_vars f1.tmvs f2.tmvs  in
      let uu____184 = union_vars f1.tyvs f2.tyvs  in
      let uu____185 = FStar_Util.set_union f1.lids f2.lids  in
      { tmvs = uu____183; tyvs = uu____184; lids = uu____185 }
  
let (type_level : free_vars_and_fvars -> free_vars_and_fvars) =
  fun fvs  ->
    let uu___27_191 = fvs  in
    let uu____192 = union_vars fvs.tmvs fvs.tyvs  in
    { tmvs = no_vars; tyvs = uu____192; lids = (uu___27_191.lids) }
  
let rec (free_univs : FStar_Syntax_Syntax.universe -> free_vars_and_fvars) =
  fun u  ->
    let uu____196 = FStar_Syntax_Subst.compress_univ u  in
    match uu____196 with
    | FStar_Syntax_Syntax.U_zero  -> no_free_vars
    | FStar_Syntax_Syntax.U_bvar uu____197 -> no_free_vars
    | FStar_Syntax_Syntax.U_unknown  -> no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let uu____208 = free_univs x  in union out uu____208)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u1 -> singleton_univ u1
  
let rec (free_names_and_uvs' :
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars) =
  fun tm  ->
    fun use_cache  ->
      let aux_binders bs from_body =
        let from_binders =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun n1  ->
                  fun uu____278  ->
                    match uu____278 with
                    | (x,uu____284) ->
                        let uu____285 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache
                           in
                        union n1 uu____285) no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____287 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____313 =
            let uu____314 =
              free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache  in
            FStar_All.pipe_left type_level uu____314  in
          union (singleton_bv x) uu____313
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          let uu____355 =
            free_names_and_uvars bv.FStar_Syntax_Syntax.sort use_cache  in
          FStar_All.pipe_left type_level uu____355
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant uu____357 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_lazy uu____358 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_unknown  -> no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
          let f = free_names_and_uvars t1 use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let uu____371 = free_univs u  in union out uu____371)
            f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____374) ->
          let uu____395 = free_names_and_uvars t1 use_cache  in
          aux_binders bs uu____395
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____414 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs uu____414
      | FStar_Syntax_Syntax.Tm_refine (bv,t1) ->
          let uu____421 = free_names_and_uvars t1 use_cache  in
          aux_binders [(bv, FStar_Pervasives_Native.None)] uu____421
      | FStar_Syntax_Syntax.Tm_app (t1,args) ->
          let uu____458 = free_names_and_uvars t1 use_cache  in
          free_names_and_uvars_args args uu____458 use_cache
      | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
          let uu____497 =
            let uu____516 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____539  ->
                   match uu____539 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> no_free_vars
                         | FStar_Pervasives_Native.Some w ->
                             free_names_and_uvars w use_cache
                          in
                       let n2 = free_names_and_uvars t2 use_cache  in
                       let n3 =
                         let uu____577 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right uu____577
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____587 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n3 uu____587) n1)
                          in
                       let uu____588 = union n11 n2  in union n3 uu____588)
              uu____516
             in
          FStar_All.pipe_right pats uu____497
      | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____607) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          let u2 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> free_names_and_uvars t2 use_cache
            | FStar_Util.Inr c2 -> free_names_and_uvars_comp c2 use_cache  in
          (match FStar_Pervasives_Native.snd asc with
           | FStar_Pervasives_Native.None  -> union u1 u2
           | FStar_Pervasives_Native.Some tac ->
               let uu____695 = union u1 u2  in
               let uu____696 = free_names_and_uvars tac use_cache  in
               union uu____695 uu____696)
      | FStar_Syntax_Syntax.Tm_let (lbs,t1) ->
          let uu____715 =
            let uu____720 = free_names_and_uvars t1 use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____726 =
                     let uu____727 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let uu____728 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union uu____727 uu____728  in
                   union n1 uu____726) uu____720
             in
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____715
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let u1 = free_names_and_uvars t1 use_cache  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern args ->
               FStar_List.fold_right
                 (fun a  ->
                    fun acc  -> free_names_and_uvars_args a acc use_cache)
                 args u1
           | FStar_Syntax_Syntax.Meta_monadic (uu____771,t') ->
               let uu____777 = free_names_and_uvars t' use_cache  in
               union u1 uu____777
           | FStar_Syntax_Syntax.Meta_monadic_lift (uu____778,uu____779,t')
               ->
               let uu____785 = free_names_and_uvars t' use_cache  in
               union u1 uu____785
           | FStar_Syntax_Syntax.Meta_quoted (qt,qi) ->
               if qi.FStar_Syntax_Syntax.qopen
               then
                 let uu____792 = free_names_and_uvars qt use_cache  in
                 union u1 uu____792
               else u1
           | FStar_Syntax_Syntax.Meta_labeled uu____794 -> u1
           | FStar_Syntax_Syntax.Meta_desugared uu____801 -> u1
           | FStar_Syntax_Syntax.Meta_named uu____802 -> u1)

and (free_names_and_uvars :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun t  ->
    fun use_cache  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let uu____808 = FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars  in
      match uu____808 with
      | FStar_Pervasives_Native.Some (tmvs,tyvs) when
          let uu____852 = should_invalidate_cache tmvs use_cache  in
          Prims.op_Negation uu____852 -> { tmvs; tyvs; lids = no_lids }
      | uu____853 ->
          (FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
             FStar_Pervasives_Native.None;
           (let n1 = free_names_and_uvs' t1 use_cache  in
            FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars
              (FStar_Pervasives_Native.Some ((n1.tmvs), (n1.tyvs)));
            n1))

and (free_names_and_uvars_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    free_vars_and_fvars -> Prims.bool -> free_vars_and_fvars)
  =
  fun args  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____964  ->
                  match uu____964 with
                  | (x,uu____972) ->
                      let uu____977 = free_names_and_uvars x use_cache  in
                      union n1 uu____977) acc)

and (free_names_and_uvars_binders :
  FStar_Syntax_Syntax.binders ->
    free_vars_and_fvars -> Prims.bool -> free_vars_and_fvars)
  =
  fun bs  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun n1  ->
                fun uu____991  ->
                  match uu____991 with
                  | (x,uu____997) ->
                      let uu____998 =
                        free_names_and_uvars x.FStar_Syntax_Syntax.sort
                          use_cache
                         in
                      union n1 uu____998) acc)

and (free_names_and_uvars_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    Prims.bool -> free_vars_and_fvars)
  =
  fun c  ->
    fun use_cache  ->
      let uu____1003 = FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars  in
      match uu____1003 with
      | FStar_Pervasives_Native.Some (tmvs,tyvs) ->
          let uu____1047 = should_invalidate_cache tmvs use_cache  in
          if uu____1047
          then
            (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
               FStar_Pervasives_Native.None;
             free_names_and_uvars_comp c use_cache)
          else { tmvs; tyvs; lids = no_lids }
      | uu____1085 ->
          let n1 =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
                free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u)
                ->
                let uu____1115 = free_univs u  in
                let uu____1116 = free_names_and_uvars t use_cache  in
                union uu____1115 uu____1116
            | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
                let uu____1125 = free_univs u  in
                let uu____1126 = free_names_and_uvars t use_cache  in
                union uu____1125 uu____1126
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1129 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache
                     in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args uu____1129 use_cache
                   in
                FStar_List.fold_left
                  (fun us1  ->
                     fun u  ->
                       let uu____1135 = free_univs u  in union us1 uu____1135)
                  us ct.FStar_Syntax_Syntax.comp_univs
             in
          (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars
             (FStar_Pervasives_Native.Some ((n1.tmvs), (n1.tyvs)));
           n1)

and (should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool) =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars
            (FStar_Util.for_some
               (fun uu____1203  ->
                  match uu____1203 with
                  | (u,uu____1211) ->
                      let uu____1216 = FStar_Syntax_Unionfind.find u  in
                      (match uu____1216 with
                       | FStar_Pervasives_Native.Some uu____1219 -> true
                       | uu____1220 -> false))))
           ||
           (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____1229 = FStar_Syntax_Unionfind.univ_find u  in
                    match uu____1229 with
                    | FStar_Pervasives_Native.Some uu____1232 -> true
                    | FStar_Pervasives_Native.None  -> false))))

let compare_uv :
  'Auu____1237 'Auu____1238 .
    (FStar_Syntax_Syntax.uvar,'Auu____1237) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.uvar,'Auu____1238) FStar_Pervasives_Native.tuple2
        -> Prims.int
  =
  fun uv1  ->
    fun uv2  ->
      let uu____1263 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv1)  in
      let uu____1264 =
        FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv2)  in
      uu____1263 - uu____1264
  
let (new_uv_set : Prims.unit -> FStar_Syntax_Syntax.uvars) =
  fun uu____1267  -> FStar_Util.new_set compare_uv 
let (compare_universe_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.int)
  =
  fun x  ->
    fun y  ->
      let uu____1284 = FStar_Syntax_Unionfind.univ_uvar_id x  in
      let uu____1285 = FStar_Syntax_Unionfind.univ_uvar_id y  in
      uu____1284 - uu____1285
  
let (new_universe_uvar_set :
  Prims.unit -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun uu____1290  -> FStar_Util.new_set compare_universe_uvar 
let (empty : FStar_Syntax_Syntax.bv FStar_Util.set) =
  FStar_Util.new_set FStar_Syntax_Syntax.order_bv 
let (names :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t  ->
    let uu____1300 =
      let uu____1303 =
        let uu____1304 = free_names_and_uvars t true  in uu____1304.tmvs  in
      uu____1303.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1300 FStar_Syntax_Syntax.order_bv
  
let (names_full :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun t  ->
    let uu____1310 =
      let uu____1313 =
        let uu____1316 =
          let uu____1317 = free_names_and_uvars t true  in uu____1317.tmvs
           in
        uu____1316.FStar_Syntax_Syntax.free_names  in
      let uu____1318 =
        let uu____1321 =
          let uu____1322 = free_names_and_uvars t true  in uu____1322.tyvs
           in
        uu____1321.FStar_Syntax_Syntax.free_names  in
      FStar_List.append uu____1313 uu____1318  in
    FStar_Util.as_set uu____1310 FStar_Syntax_Syntax.order_bv
  
let (uvars :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set)
  =
  fun t  ->
    let uu____1332 =
      let uu____1351 =
        let uu____1352 = free_names_and_uvars t true  in uu____1352.tmvs  in
      uu____1351.FStar_Syntax_Syntax.free_uvars  in
    FStar_Util.as_set uu____1332 compare_uv
  
let (univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set)
  =
  fun t  ->
    let uu____1378 =
      let uu____1381 =
        let uu____1382 = free_names_and_uvars t true  in uu____1382.tmvs  in
      uu____1381.FStar_Syntax_Syntax.free_univs  in
    FStar_Util.as_set uu____1378 compare_universe_uvar
  
let (univnames :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun t  ->
    let uu____1388 =
      let uu____1391 =
        let uu____1392 = free_names_and_uvars t true  in uu____1392.tmvs  in
      uu____1391.FStar_Syntax_Syntax.free_univ_names  in
    FStar_Util.as_set uu____1388 FStar_Syntax_Syntax.order_univ_name
  
let (fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set) =
  fun t  -> let uu____1398 = free_names_and_uvars t false  in uu____1398.lids 
let (names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun bs  ->
    let uu____1404 =
      let uu____1407 =
        let uu____1408 = free_names_and_uvars_binders bs no_free_vars true
           in
        uu____1408.tmvs  in
      uu____1407.FStar_Syntax_Syntax.free_names  in
    FStar_Util.as_set uu____1404 FStar_Syntax_Syntax.order_bv
  