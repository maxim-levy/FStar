open Prims
let subst_to_string :
  'Auu____5 .
    (FStar_Syntax_Syntax.bv,'Auu____5) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun s  ->
    let uu____23 =
      FStar_All.pipe_right s
        (FStar_List.map
           (fun uu____41  ->
              match uu____41 with
              | (b,uu____47) ->
                  (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText))
       in
    FStar_All.pipe_right uu____23 (FStar_String.concat ", ")
  
let rec apply_until_some :
  'Auu____58 'Auu____59 .
    ('Auu____58 -> 'Auu____59 FStar_Pervasives_Native.option) ->
      'Auu____58 Prims.list ->
        ('Auu____58 Prims.list,'Auu____59) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun f  ->
    fun s  ->
      match s with
      | [] -> FStar_Pervasives_Native.None
      | s0::rest ->
          let uu____101 = f s0  in
          (match uu____101 with
           | FStar_Pervasives_Native.None  -> apply_until_some f rest
           | FStar_Pervasives_Native.Some st ->
               FStar_Pervasives_Native.Some (rest, st))
  
let map_some_curry :
  'Auu____133 'Auu____134 'Auu____135 .
    ('Auu____133 -> 'Auu____134 -> 'Auu____135) ->
      'Auu____135 ->
        ('Auu____133,'Auu____134) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option -> 'Auu____135
  =
  fun f  ->
    fun x  ->
      fun uu___90_162  ->
        match uu___90_162 with
        | FStar_Pervasives_Native.None  -> x
        | FStar_Pervasives_Native.Some (a,b) -> f a b
  
let apply_until_some_then_map :
  'Auu____197 'Auu____198 'Auu____199 .
    ('Auu____197 -> 'Auu____198 FStar_Pervasives_Native.option) ->
      'Auu____197 Prims.list ->
        ('Auu____197 Prims.list -> 'Auu____198 -> 'Auu____199) ->
          'Auu____199 -> 'Auu____199
  =
  fun f  ->
    fun s  ->
      fun g  ->
        fun t  ->
          let uu____247 = apply_until_some f s  in
          FStar_All.pipe_right uu____247 (map_some_curry g t)
  
let compose_subst :
  'Auu____272 .
    ('Auu____272 Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____272 Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 ->
        ('Auu____272 Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
          FStar_Pervasives_Native.tuple2
  =
  fun s1  ->
    fun s2  ->
      let s =
        FStar_List.append (FStar_Pervasives_Native.fst s1)
          (FStar_Pervasives_Native.fst s2)
         in
      let ropt =
        match FStar_Pervasives_Native.snd s2 with
        | FStar_Syntax_Syntax.SomeUseRange uu____323 ->
            FStar_Pervasives_Native.snd s2
        | uu____326 -> FStar_Pervasives_Native.snd s1  in
      (s, ropt)
  
let (delay :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun s  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
            t.FStar_Syntax_Syntax.pos
      | uu____408 ->
          FStar_Syntax_Syntax.mk_Tm_delayed (t, s) t.FStar_Syntax_Syntax.pos
  
let rec (force_uvar' :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar
        ({ FStar_Syntax_Syntax.ctx_uvar_head = uv;
           FStar_Syntax_Syntax.ctx_uvar_gamma = uu____431;
           FStar_Syntax_Syntax.ctx_uvar_binders = uu____432;
           FStar_Syntax_Syntax.ctx_uvar_typ = uu____433;
           FStar_Syntax_Syntax.ctx_uvar_reason = uu____434;
           FStar_Syntax_Syntax.ctx_uvar_should_check = uu____435;
           FStar_Syntax_Syntax.ctx_uvar_range = uu____436;_},s)
        ->
        let uu____474 = FStar_Syntax_Unionfind.find uv  in
        (match uu____474 with
         | FStar_Pervasives_Native.Some t' ->
             let uu____484 =
               let uu____487 =
                 let uu____494 = delay t' s  in force_uvar' uu____494  in
               FStar_Pervasives_Native.fst uu____487  in
             (uu____484, true)
         | uu____499 -> (t, false))
    | uu____504 -> (t, false)
  
let (force_uvar :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____522 = force_uvar' t  in
    match uu____522 with
    | (t',forced) ->
        if Prims.op_Negation forced
        then (t, forced)
        else
          (let uu____550 =
             delay t'
               ([],
                 (FStar_Syntax_Syntax.SomeUseRange
                    (t.FStar_Syntax_Syntax.pos)))
              in
           (uu____550, forced))
  
let rec (try_read_memo_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,Prims.bool)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed (f,m) ->
        let uu____618 = FStar_ST.op_Bang m  in
        (match uu____618 with
         | FStar_Pervasives_Native.None  -> (t, false)
         | FStar_Pervasives_Native.Some t' ->
             let uu____691 = try_read_memo_aux t'  in
             (match uu____691 with
              | (t'1,shorten) ->
                  (if shorten
                   then
                     FStar_ST.op_Colon_Equals m
                       (FStar_Pervasives_Native.Some t'1)
                   else ();
                   (t'1, true))))
    | uu____769 -> (t, false)
  
let (try_read_memo :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____783 = try_read_memo_aux t  in
    FStar_Pervasives_Native.fst uu____783
  
let rec (compress_univ :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unif u' ->
        let uu____806 = FStar_Syntax_Unionfind.univ_find u'  in
        (match uu____806 with
         | FStar_Pervasives_Native.Some u1 -> compress_univ u1
         | uu____810 -> u)
    | uu____813 -> u
  
let (subst_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___91_834  ->
           match uu___91_834 with
           | FStar_Syntax_Syntax.DB (i,x) when
               i = a.FStar_Syntax_Syntax.index ->
               let uu____839 =
                 let uu____840 =
                   let uu____841 = FStar_Syntax_Syntax.range_of_bv a  in
                   FStar_Syntax_Syntax.set_range_of_bv x uu____841  in
                 FStar_Syntax_Syntax.bv_to_name uu____840  in
               FStar_Pervasives_Native.Some uu____839
           | uu____842 -> FStar_Pervasives_Native.None)
  
let (subst_nm :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun a  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___92_867  ->
           match uu___92_867 with
           | FStar_Syntax_Syntax.NM (x,i) when FStar_Syntax_Syntax.bv_eq a x
               ->
               let uu____874 =
                 FStar_Syntax_Syntax.bv_to_tm
                   (let uu___98_877 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___98_877.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index = i;
                      FStar_Syntax_Syntax.sort =
                        (uu___98_877.FStar_Syntax_Syntax.sort)
                    })
                  in
               FStar_Pervasives_Native.Some uu____874
           | FStar_Syntax_Syntax.NT (x,t) when FStar_Syntax_Syntax.bv_eq a x
               -> FStar_Pervasives_Native.Some t
           | uu____888 -> FStar_Pervasives_Native.None)
  
let (subst_univ_bv :
  Prims.int ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___93_910  ->
           match uu___93_910 with
           | FStar_Syntax_Syntax.UN (y,t) when x = y ->
               FStar_Pervasives_Native.Some t
           | uu____915 -> FStar_Pervasives_Native.None)
  
let (subst_univ_nm :
  FStar_Syntax_Syntax.univ_name ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun x  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___94_935  ->
           match uu___94_935 with
           | FStar_Syntax_Syntax.UD (y,i) when
               x.FStar_Ident.idText = y.FStar_Ident.idText ->
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_bvar i)
           | uu____940 -> FStar_Pervasives_Native.None)
  
let rec (subst_univ :
  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun s  ->
    fun u  ->
      let u1 = compress_univ u  in
      match u1 with
      | FStar_Syntax_Syntax.U_bvar x ->
          apply_until_some_then_map (subst_univ_bv x) s subst_univ u1
      | FStar_Syntax_Syntax.U_name x ->
          apply_until_some_then_map (subst_univ_nm x) s subst_univ u1
      | FStar_Syntax_Syntax.U_zero  -> u1
      | FStar_Syntax_Syntax.U_unknown  -> u1
      | FStar_Syntax_Syntax.U_unif uu____966 -> u1
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu____976 = subst_univ s u2  in
          FStar_Syntax_Syntax.U_succ uu____976
      | FStar_Syntax_Syntax.U_max us ->
          let uu____980 = FStar_List.map (subst_univ s) us  in
          FStar_Syntax_Syntax.U_max uu____980
  
let tag_with_range :
  'Auu____989 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ('Auu____989,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> t
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1015 =
            let uu____1016 = FStar_Range.use_range t.FStar_Syntax_Syntax.pos
               in
            let uu____1017 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1016 uu____1017  in
          if uu____1015
          then t
          else
            (let r1 =
               let uu____1022 = FStar_Range.use_range r  in
               FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos uu____1022
                in
             let t' =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_bvar bv ->
                   let uu____1025 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_bvar uu____1025
               | FStar_Syntax_Syntax.Tm_name bv ->
                   let uu____1027 = FStar_Syntax_Syntax.set_range_of_bv bv r1
                      in
                   FStar_Syntax_Syntax.Tm_name uu____1027
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   let v1 =
                     let uu___99_1033 = fv.FStar_Syntax_Syntax.fv_name  in
                     let uu____1034 = FStar_Ident.set_lid_range l r1  in
                     {
                       FStar_Syntax_Syntax.v = uu____1034;
                       FStar_Syntax_Syntax.p =
                         (uu___99_1033.FStar_Syntax_Syntax.p)
                     }  in
                   let fv1 =
                     let uu___100_1036 = fv  in
                     {
                       FStar_Syntax_Syntax.fv_name = v1;
                       FStar_Syntax_Syntax.fv_delta =
                         (uu___100_1036.FStar_Syntax_Syntax.fv_delta);
                       FStar_Syntax_Syntax.fv_qual =
                         (uu___100_1036.FStar_Syntax_Syntax.fv_qual)
                     }  in
                   FStar_Syntax_Syntax.Tm_fvar fv1
               | t' -> t'  in
             let uu___101_1038 = t  in
             {
               FStar_Syntax_Syntax.n = t';
               FStar_Syntax_Syntax.pos = r1;
               FStar_Syntax_Syntax.vars =
                 (uu___101_1038.FStar_Syntax_Syntax.vars)
             })
  
let tag_lid_with_range :
  'Auu____1047 .
    FStar_Ident.lident ->
      ('Auu____1047,FStar_Syntax_Syntax.maybe_set_use_range)
        FStar_Pervasives_Native.tuple2 -> FStar_Ident.lident
  =
  fun l  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> l
      | FStar_Syntax_Syntax.SomeUseRange r ->
          let uu____1067 =
            let uu____1068 =
              let uu____1069 = FStar_Ident.range_of_lid l  in
              FStar_Range.use_range uu____1069  in
            let uu____1070 = FStar_Range.use_range r  in
            FStar_Range.rng_included uu____1068 uu____1070  in
          if uu____1067
          then l
          else
            (let uu____1072 =
               let uu____1073 = FStar_Ident.range_of_lid l  in
               let uu____1074 = FStar_Range.use_range r  in
               FStar_Range.set_use_range uu____1073 uu____1074  in
             FStar_Ident.set_lid_range l uu____1072)
  
let (mk_range :
  FStar_Range.range -> FStar_Syntax_Syntax.subst_ts -> FStar_Range.range) =
  fun r  ->
    fun s  ->
      match FStar_Pervasives_Native.snd s with
      | FStar_Syntax_Syntax.NoUseRange  -> r
      | FStar_Syntax_Syntax.SomeUseRange r' ->
          let uu____1090 =
            let uu____1091 = FStar_Range.use_range r  in
            let uu____1092 = FStar_Range.use_range r'  in
            FStar_Range.rng_included uu____1091 uu____1092  in
          if uu____1090
          then r
          else
            (let uu____1094 = FStar_Range.use_range r'  in
             FStar_Range.set_use_range r uu____1094)
  
let rec (subst' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let subst_tail tl1 = subst' (tl1, (FStar_Pervasives_Native.snd s))  in
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1194 ->
          let t0 = try_read_memo t  in
          (match t0.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_constant uu____1202 ->
               tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_fvar uu____1207 -> tag_with_range t0 s
           | FStar_Syntax_Syntax.Tm_delayed ((t',s'),m) ->
               FStar_Syntax_Syntax.mk_Tm_delayed (t', (compose_subst s' s))
                 t.FStar_Syntax_Syntax.pos
           | FStar_Syntax_Syntax.Tm_bvar a ->
               apply_until_some_then_map (subst_bv a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_name a ->
               apply_until_some_then_map (subst_nm a)
                 (FStar_Pervasives_Native.fst s) subst_tail t0
           | FStar_Syntax_Syntax.Tm_type u ->
               let uu____1276 = mk_range t0.FStar_Syntax_Syntax.pos s  in
               let uu____1277 =
                 let uu____1284 =
                   let uu____1285 =
                     subst_univ (FStar_Pervasives_Native.fst s) u  in
                   FStar_Syntax_Syntax.Tm_type uu____1285  in
                 FStar_Syntax_Syntax.mk uu____1284  in
               uu____1277 FStar_Pervasives_Native.None uu____1276
           | uu____1293 ->
               let uu____1294 = mk_range t.FStar_Syntax_Syntax.pos s  in
               FStar_Syntax_Syntax.mk_Tm_delayed (t0, s) uu____1294)

and (subst_flags' :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun s  ->
    fun flags  ->
      FStar_All.pipe_right flags
        (FStar_List.map
           (fun uu___95_1306  ->
              match uu___95_1306 with
              | FStar_Syntax_Syntax.DECREASES a ->
                  let uu____1310 = subst' s a  in
                  FStar_Syntax_Syntax.DECREASES uu____1310
              | f -> f))

and (subst_comp_typ' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1336 ->
          let uu___102_1345 = t  in
          let uu____1346 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s))
              t.FStar_Syntax_Syntax.comp_univs
             in
          let uu____1353 =
            tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s  in
          let uu____1358 = subst' s t.FStar_Syntax_Syntax.result_typ  in
          let uu____1359 =
            FStar_List.map
              (fun uu____1378  ->
                 match uu____1378 with
                 | (t1,imp) ->
                     let uu____1389 = subst' s t1  in (uu____1389, imp))
              t.FStar_Syntax_Syntax.effect_args
             in
          let uu____1390 = subst_flags' s t.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs = uu____1346;
            FStar_Syntax_Syntax.effect_name = uu____1353;
            FStar_Syntax_Syntax.result_typ = uu____1358;
            FStar_Syntax_Syntax.effect_args = uu____1359;
            FStar_Syntax_Syntax.flags = uu____1390
          }

and (subst_comp' :
  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      match s with
      | ([],FStar_Syntax_Syntax.NoUseRange ) -> t
      | ([]::[],FStar_Syntax_Syntax.NoUseRange ) -> t
      | uu____1421 ->
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (t1,uopt) ->
               let uu____1442 = subst' s t1  in
               let uu____1443 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_Total' uu____1442 uu____1443
           | FStar_Syntax_Syntax.GTotal (t1,uopt) ->
               let uu____1460 = subst' s t1  in
               let uu____1461 =
                 FStar_Option.map
                   (subst_univ (FStar_Pervasives_Native.fst s)) uopt
                  in
               FStar_Syntax_Syntax.mk_GTotal' uu____1460 uu____1461
           | FStar_Syntax_Syntax.Comp ct ->
               let uu____1469 = subst_comp_typ' s ct  in
               FStar_Syntax_Syntax.mk_Comp uu____1469)

let (shift :
  Prims.int -> FStar_Syntax_Syntax.subst_elt -> FStar_Syntax_Syntax.subst_elt)
  =
  fun n1  ->
    fun s  ->
      match s with
      | FStar_Syntax_Syntax.DB (i,t) -> FStar_Syntax_Syntax.DB ((i + n1), t)
      | FStar_Syntax_Syntax.UN (i,t) -> FStar_Syntax_Syntax.UN ((i + n1), t)
      | FStar_Syntax_Syntax.NM (x,i) -> FStar_Syntax_Syntax.NM (x, (i + n1))
      | FStar_Syntax_Syntax.UD (x,i) -> FStar_Syntax_Syntax.UD (x, (i + n1))
      | FStar_Syntax_Syntax.NT uu____1488 -> s
  
let (shift_subst :
  Prims.int -> FStar_Syntax_Syntax.subst_t -> FStar_Syntax_Syntax.subst_t) =
  fun n1  -> fun s  -> FStar_List.map (shift n1) s 
let shift_subst' :
  'Auu____1511 .
    Prims.int ->
      (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1511)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.subst_t Prims.list,'Auu____1511)
          FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun s  ->
      let uu____1540 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
          (FStar_List.map (shift_subst n1))
         in
      (uu____1540, (FStar_Pervasives_Native.snd s))
  
let subst_binder' :
  'Auu____1559 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.bv,'Auu____1559) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.bv,'Auu____1559) FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1577  ->
      match uu____1577 with
      | (x,imp) ->
          let uu____1584 =
            let uu___103_1585 = x  in
            let uu____1586 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___103_1585.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___103_1585.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____1586
            }  in
          (uu____1584, imp)
  
let subst_binders' :
  'Auu____1593 .
    (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
      FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,'Auu____1593) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____1593) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.mapi
           (fun i  ->
              fun b  ->
                if i = (Prims.parse_int "0")
                then subst_binder' s b
                else
                  (let uu____1671 = shift_subst' i s  in
                   subst_binder' uu____1671 b)))
  
let (subst_binders :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  -> subst_binders' ([s], FStar_Syntax_Syntax.NoUseRange) bs
  
let subst_arg' :
  'Auu____1706 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1706) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1706)
          FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    fun uu____1724  ->
      match uu____1724 with
      | (t,imp) -> let uu____1731 = subst' s t  in (uu____1731, imp)
  
let subst_args' :
  'Auu____1737 .
    FStar_Syntax_Syntax.subst_ts ->
      (FStar_Syntax_Syntax.term,'Auu____1737) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____1737)
          FStar_Pervasives_Native.tuple2 Prims.list
  = fun s  -> FStar_List.map (subst_arg' s) 
let (subst_pat' :
  (FStar_Syntax_Syntax.subst_t Prims.list,FStar_Syntax_Syntax.maybe_set_use_range)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Syntax_Syntax.pat,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun s  ->
    fun p  ->
      let rec aux n1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu____1824 -> (p1, n1)
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1843 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1897  ->
                      fun uu____1898  ->
                        match (uu____1897, uu____1898) with
                        | ((pats1,n2),(p2,imp)) ->
                            let uu____1977 = aux n2 p2  in
                            (match uu____1977 with
                             | (p3,m) -> (((p3, imp) :: pats1), m))) 
                   ([], n1))
               in
            (match uu____1843 with
             | (pats1,n2) ->
                 ((let uu___104_2033 = p1  in
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, (FStar_List.rev pats1)));
                     FStar_Syntax_Syntax.p =
                       (uu___104_2033.FStar_Syntax_Syntax.p)
                   }), n2))
        | FStar_Syntax_Syntax.Pat_var x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___105_2057 = x  in
              let uu____2058 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___105_2057.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___105_2057.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2058
              }  in
            ((let uu___106_2060 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                FStar_Syntax_Syntax.p = (uu___106_2060.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___107_2072 = x  in
              let uu____2073 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___107_2072.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___107_2072.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2073
              }  in
            ((let uu___108_2075 = p1  in
              {
                FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                FStar_Syntax_Syntax.p = (uu___108_2075.FStar_Syntax_Syntax.p)
              }), (n1 + (Prims.parse_int "1")))
        | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
            let s1 = shift_subst' n1 s  in
            let x1 =
              let uu___109_2092 = x  in
              let uu____2093 = subst' s1 x.FStar_Syntax_Syntax.sort  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___109_2092.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___109_2092.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____2093
              }  in
            let t01 = subst' s1 t0  in
            ((let uu___110_2096 = p1  in
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
                FStar_Syntax_Syntax.p = (uu___110_2096.FStar_Syntax_Syntax.p)
              }), n1)
         in
      aux (Prims.parse_int "0") p
  
let (push_subst_lcomp :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun lopt  ->
      match lopt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____2120 =
            let uu___111_2121 = rc  in
            let uu____2122 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (subst' s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___111_2121.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2122;
              FStar_Syntax_Syntax.residual_flags =
                (uu___111_2121.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____2120
  
let (compose_uvar_subst :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.subst_ts ->
      FStar_Syntax_Syntax.subst_ts -> FStar_Syntax_Syntax.subst_ts)
  =
  fun u  ->
    fun s0  ->
      fun s  ->
        let should_retain x =
          FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
            (FStar_Util.for_some
               (fun uu____2165  ->
                  match uu____2165 with
                  | (x',uu____2171) -> FStar_Syntax_Syntax.bv_eq x x'))
           in
        let rec aux uu___97_2183 =
          match uu___97_2183 with
          | [] -> []
          | hd_subst::rest ->
              let hd1 =
                FStar_All.pipe_right hd_subst
                  (FStar_List.collect
                     (fun uu___96_2214  ->
                        match uu___96_2214 with
                        | FStar_Syntax_Syntax.NT (x,t) ->
                            let uu____2223 = should_retain x  in
                            if uu____2223
                            then
                              let uu____2226 =
                                let uu____2227 =
                                  let uu____2234 =
                                    delay t
                                      (rest, FStar_Syntax_Syntax.NoUseRange)
                                     in
                                  (x, uu____2234)  in
                                FStar_Syntax_Syntax.NT uu____2227  in
                              [uu____2226]
                            else []
                        | FStar_Syntax_Syntax.NM (x,i) ->
                            let uu____2244 = should_retain x  in
                            if uu____2244
                            then
                              let x_i =
                                FStar_Syntax_Syntax.bv_to_tm
                                  (let uu___112_2250 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___112_2250.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index = i;
                                     FStar_Syntax_Syntax.sort =
                                       (uu___112_2250.FStar_Syntax_Syntax.sort)
                                   })
                                 in
                              let t =
                                subst' (rest, FStar_Syntax_Syntax.NoUseRange)
                                  x_i
                                 in
                              (match t.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_bvar x_j ->
                                   [FStar_Syntax_Syntax.NM
                                      (x, (x_j.FStar_Syntax_Syntax.index))]
                               | uu____2259 ->
                                   [FStar_Syntax_Syntax.NT (x, t)])
                            else []
                        | uu____2263 -> []))
                 in
              let uu____2264 = aux rest  in FStar_List.append hd1 uu____2264
           in
        let uu____2267 =
          aux
            (FStar_List.append (FStar_Pervasives_Native.fst s0)
               (FStar_Pervasives_Native.fst s))
           in
        match uu____2267 with
        | [] -> ([], (FStar_Pervasives_Native.snd s))
        | s' -> ([s'], (FStar_Pervasives_Native.snd s))
  
let rec (push_subst :
  FStar_Syntax_Syntax.subst_ts ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun t  ->
      let mk1 t' =
        let uu____2329 = mk_range t.FStar_Syntax_Syntax.pos s  in
        FStar_Syntax_Syntax.mk t' FStar_Pervasives_Native.None uu____2329  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2332 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i -> t
      | FStar_Syntax_Syntax.Tm_constant uu____2358 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_fvar uu____2363 -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_unknown  -> tag_with_range t s
      | FStar_Syntax_Syntax.Tm_uvar (uv,s0) ->
          let uu____2390 =
            FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head
             in
          (match uu____2390 with
           | FStar_Pervasives_Native.None  ->
               let uu____2395 =
                 let uu___113_2398 = t  in
                 let uu____2401 =
                   let uu____2402 =
                     let uu____2415 = compose_uvar_subst uv s0 s  in
                     (uv, uu____2415)  in
                   FStar_Syntax_Syntax.Tm_uvar uu____2402  in
                 {
                   FStar_Syntax_Syntax.n = uu____2401;
                   FStar_Syntax_Syntax.pos =
                     (uu___113_2398.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___113_2398.FStar_Syntax_Syntax.vars)
                 }  in
               tag_with_range uu____2395 s
           | FStar_Pervasives_Native.Some t1 ->
               push_subst (compose_subst s0 s) t1)
      | FStar_Syntax_Syntax.Tm_type uu____2431 -> subst' s t
      | FStar_Syntax_Syntax.Tm_bvar uu____2432 -> subst' s t
      | FStar_Syntax_Syntax.Tm_name uu____2433 -> subst' s t
      | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
          let us1 =
            FStar_List.map (subst_univ (FStar_Pervasives_Native.fst s)) us
             in
          let uu____2447 = FStar_Syntax_Syntax.mk_Tm_uinst t' us1  in
          tag_with_range uu____2447 s
      | FStar_Syntax_Syntax.Tm_app (t0,args) ->
          let uu____2474 =
            let uu____2475 =
              let uu____2490 = subst' s t0  in
              let uu____2491 = subst_args' s args  in
              (uu____2490, uu____2491)  in
            FStar_Syntax_Syntax.Tm_app uu____2475  in
          mk1 uu____2474
      | FStar_Syntax_Syntax.Tm_ascribed (t0,(annot,topt),lopt) ->
          let annot1 =
            match annot with
            | FStar_Util.Inl t1 ->
                let uu____2584 = subst' s t1  in FStar_Util.Inl uu____2584
            | FStar_Util.Inr c ->
                let uu____2596 = subst_comp' s c  in
                FStar_Util.Inr uu____2596
             in
          let uu____2603 =
            let uu____2604 =
              let uu____2631 = subst' s t0  in
              let uu____2632 =
                let uu____2649 = FStar_Util.map_opt topt (subst' s)  in
                (annot1, uu____2649)  in
              (uu____2631, uu____2632, lopt)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2604  in
          mk1 uu____2603
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let n1 = FStar_List.length bs  in
          let s' = shift_subst' n1 s  in
          let uu____2729 =
            let uu____2730 =
              let uu____2747 = subst_binders' s bs  in
              let uu____2754 = subst' s' body  in
              let uu____2755 = push_subst_lcomp s' lopt  in
              (uu____2747, uu____2754, uu____2755)  in
            FStar_Syntax_Syntax.Tm_abs uu____2730  in
          mk1 uu____2729
      | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
          let n1 = FStar_List.length bs  in
          let uu____2791 =
            let uu____2792 =
              let uu____2805 = subst_binders' s bs  in
              let uu____2812 =
                let uu____2815 = shift_subst' n1 s  in
                subst_comp' uu____2815 comp  in
              (uu____2805, uu____2812)  in
            FStar_Syntax_Syntax.Tm_arrow uu____2792  in
          mk1 uu____2791
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let x1 =
            let uu___114_2841 = x  in
            let uu____2842 = subst' s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___114_2841.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___114_2841.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____2842
            }  in
          let phi1 =
            let uu____2844 = shift_subst' (Prims.parse_int "1") s  in
            subst' uu____2844 phi  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (x1, phi1))
      | FStar_Syntax_Syntax.Tm_match (t0,pats) ->
          let t01 = subst' s t0  in
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____2965  ->
                    match uu____2965 with
                    | (pat,wopt,branch) ->
                        let uu____2995 = subst_pat' s pat  in
                        (match uu____2995 with
                         | (pat1,n1) ->
                             let s1 = shift_subst' n1 s  in
                             let wopt1 =
                               match wopt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3023 = subst' s1 w  in
                                   FStar_Pervasives_Native.Some uu____3023
                                in
                             let branch1 = subst' s1 branch  in
                             (pat1, wopt1, branch1))))
             in
          mk1 (FStar_Syntax_Syntax.Tm_match (t01, pats1))
      | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),body) ->
          let n1 = FStar_List.length lbs  in
          let sn = shift_subst' n1 s  in
          let body1 = subst' sn body  in
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let lbt = subst' s lb.FStar_Syntax_Syntax.lbtyp  in
                    let lbd =
                      let uu____3092 =
                        is_rec &&
                          (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)
                         in
                      if uu____3092
                      then subst' sn lb.FStar_Syntax_Syntax.lbdef
                      else subst' s lb.FStar_Syntax_Syntax.lbdef  in
                    let lbname =
                      match lb.FStar_Syntax_Syntax.lbname with
                      | FStar_Util.Inl x ->
                          FStar_Util.Inl
                            (let uu___115_3107 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___115_3107.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___115_3107.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = lbt
                             })
                      | FStar_Util.Inr fv -> FStar_Util.Inr fv  in
                    let uu___116_3109 = lb  in
                    {
                      FStar_Syntax_Syntax.lbname = lbname;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___116_3109.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = lbt;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___116_3109.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = lbd;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___116_3109.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___116_3109.FStar_Syntax_Syntax.lbpos)
                    }))
             in
          mk1 (FStar_Syntax_Syntax.Tm_let ((is_rec, lbs1), body1))
      | FStar_Syntax_Syntax.Tm_meta (t0,FStar_Syntax_Syntax.Meta_pattern ps)
          ->
          let uu____3136 =
            let uu____3137 =
              let uu____3144 = subst' s t0  in
              let uu____3145 =
                let uu____3146 =
                  FStar_All.pipe_right ps (FStar_List.map (subst_args' s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____3146  in
              (uu____3144, uu____3145)  in
            FStar_Syntax_Syntax.Tm_meta uu____3137  in
          mk1 uu____3136
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic (m,t1)) ->
          let uu____3200 =
            let uu____3201 =
              let uu____3208 = subst' s t0  in
              let uu____3209 =
                let uu____3210 =
                  let uu____3217 = subst' s t1  in (m, uu____3217)  in
                FStar_Syntax_Syntax.Meta_monadic uu____3210  in
              (uu____3208, uu____3209)  in
            FStar_Syntax_Syntax.Tm_meta uu____3201  in
          mk1 uu____3200
      | FStar_Syntax_Syntax.Tm_meta
          (t0,FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t1)) ->
          let uu____3234 =
            let uu____3235 =
              let uu____3242 = subst' s t0  in
              let uu____3243 =
                let uu____3244 =
                  let uu____3253 = subst' s t1  in (m1, m2, uu____3253)  in
                FStar_Syntax_Syntax.Meta_monadic_lift uu____3244  in
              (uu____3242, uu____3243)  in
            FStar_Syntax_Syntax.Tm_meta uu____3235  in
          mk1 uu____3234
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          (match qi.FStar_Syntax_Syntax.qkind with
           | FStar_Syntax_Syntax.Quote_dynamic  ->
               let uu____3266 =
                 let uu____3267 =
                   let uu____3274 = subst' s tm  in (uu____3274, qi)  in
                 FStar_Syntax_Syntax.Tm_quoted uu____3267  in
               mk1 uu____3266
           | FStar_Syntax_Syntax.Quote_static  ->
               let qi1 = FStar_Syntax_Syntax.on_antiquoted (subst' s) qi  in
               mk1 (FStar_Syntax_Syntax.Tm_quoted (tm, qi1)))
      | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
          let uu____3286 =
            let uu____3287 = let uu____3294 = subst' s t1  in (uu____3294, m)
               in
            FStar_Syntax_Syntax.Tm_meta uu____3287  in
          mk1 uu____3286
  
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = try_read_memo t  in
    let uu____3305 = force_uvar t1  in
    match uu____3305 with
    | (t2,uu____3313) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_delayed ((t',s),memo) ->
             ((let uu____3364 =
                 let uu____3369 = push_subst s t'  in
                 FStar_Pervasives_Native.Some uu____3369  in
               FStar_ST.op_Colon_Equals memo uu____3364);
              compress t2)
         | uu____3427 -> t2)
  
let (subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun t  -> subst' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (set_use_range :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____3460 =
        let uu____3469 =
          let uu____3470 =
            let uu____3471 = FStar_Range.use_range r  in
            FStar_Range.set_def_range r uu____3471  in
          FStar_Syntax_Syntax.SomeUseRange uu____3470  in
        ([], uu____3469)  in
      subst' uu____3460 t
  
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s  -> fun t  -> subst_comp' ([s], FStar_Syntax_Syntax.NoUseRange) t 
let (closing_subst :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun bs  ->
    let uu____3507 =
      FStar_List.fold_right
        (fun uu____3530  ->
           fun uu____3531  ->
             match (uu____3530, uu____3531) with
             | ((x,uu____3559),(subst1,n1)) ->
                 (((FStar_Syntax_Syntax.NM (x, n1)) :: subst1),
                   (n1 + (Prims.parse_int "1")))) bs
        ([], (Prims.parse_int "0"))
       in
    FStar_All.pipe_right uu____3507 FStar_Pervasives_Native.fst
  
let open_binders' :
  'Auu____3594 .
    (FStar_Syntax_Syntax.bv,'Auu____3594) FStar_Pervasives_Native.tuple2
      Prims.list ->
      ((FStar_Syntax_Syntax.bv,'Auu____3594) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_Syntax_Syntax.subst_elt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    let rec aux bs1 o =
      match bs1 with
      | [] -> ([], o)
      | (x,imp)::bs' ->
          let x' =
            let uu___117_3705 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____3706 = subst o x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___117_3705.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___117_3705.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____3706
            }  in
          let o1 =
            let uu____3710 = shift_subst (Prims.parse_int "1") o  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____3710
             in
          let uu____3711 = aux bs' o1  in
          (match uu____3711 with | (bs'1,o2) -> (((x', imp) :: bs'1), o2))
       in
    aux bs []
  
let (open_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____3771 = open_binders' bs  in
    FStar_Pervasives_Native.fst uu____3771
  
let (open_term' :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.subst_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun bs  ->
    fun t  ->
      let uu____3808 = open_binders' bs  in
      match uu____3808 with
      | (bs',opening) ->
          let uu____3845 = subst opening t  in (bs', uu____3845, opening)
  
let (open_term :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____3860 = open_term' bs t  in
      match uu____3860 with | (b,t1,uu____3873) -> (b, t1)
  
let (open_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      let uu____3888 = open_binders' bs  in
      match uu____3888 with
      | (bs',opening) ->
          let uu____3923 = subst_comp opening t  in (bs', uu____3923)
  
let (open_pat :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec open_pat_aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____3972 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____3995 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4061  ->
                    fun uu____4062  ->
                      match (uu____4061, uu____4062) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4165 = open_pat_aux sub2 p2  in
                          (match uu____4165 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____3995 with
           | (pats1,sub2) ->
               ((let uu___118_4267 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___118_4267.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x' =
            let uu___119_4286 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4287 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___119_4286.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___119_4286.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4287
            }  in
          let sub2 =
            let uu____4291 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4291
             in
          ((let uu___120_4297 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x');
              FStar_Syntax_Syntax.p = (uu___120_4297.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x' =
            let uu___121_4302 = FStar_Syntax_Syntax.freshen_bv x  in
            let uu____4303 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___121_4302.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___121_4302.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4303
            }  in
          let sub2 =
            let uu____4307 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x')) ::
              uu____4307
             in
          ((let uu___122_4313 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x');
              FStar_Syntax_Syntax.p = (uu___122_4313.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___123_4323 = x  in
            let uu____4324 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___123_4323.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___123_4323.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4324
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___124_4331 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___124_4331.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    open_pat_aux [] p
  
let (open_branch' :
  FStar_Syntax_Syntax.branch ->
    (FStar_Syntax_Syntax.branch,FStar_Syntax_Syntax.subst_t)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____4344  ->
    match uu____4344 with
    | (p,wopt,e) ->
        let uu____4368 = open_pat p  in
        (match uu____4368 with
         | (p1,opening) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____4397 = subst opening w  in
                   FStar_Pervasives_Native.Some uu____4397
                in
             let e1 = subst opening e  in ((p1, wopt1, e1), opening))
  
let (open_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun br  ->
    let uu____4414 = open_branch' br  in
    match uu____4414 with | (br1,uu____4420) -> br1
  
let (close :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> let uu____4431 = closing_subst bs  in subst uu____4431 t
  
let (close_comp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun bs  ->
    fun c  -> let uu____4444 = closing_subst bs  in subst_comp uu____4444 c
  
let (close_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let rec aux s bs1 =
      match bs1 with
      | [] -> []
      | (x,imp)::tl1 ->
          let x1 =
            let uu___125_4501 = x  in
            let uu____4502 = subst s x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___125_4501.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___125_4501.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4502
            }  in
          let s' =
            let uu____4506 = shift_subst (Prims.parse_int "1") s  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4506
             in
          let uu____4507 = aux s' tl1  in (x1, imp) :: uu____4507
       in
    aux [] bs
  
let (close_lcomp :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun bs  ->
    fun lc  ->
      let s = closing_subst bs  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
        (fun uu____4533  ->
           let uu____4534 = FStar_Syntax_Syntax.lcomp_comp lc  in
           subst_comp s uu____4534)
  
let (close_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.subst_elt
                                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun p  ->
    let rec aux sub1 p1 =
      match p1.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu____4587 -> (p1, sub1)
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let uu____4610 =
            FStar_All.pipe_right pats
              (FStar_List.fold_left
                 (fun uu____4676  ->
                    fun uu____4677  ->
                      match (uu____4676, uu____4677) with
                      | ((pats1,sub2),(p2,imp)) ->
                          let uu____4780 = aux sub2 p2  in
                          (match uu____4780 with
                           | (p3,sub3) -> (((p3, imp) :: pats1), sub3)))
                 ([], sub1))
             in
          (match uu____4610 with
           | (pats1,sub2) ->
               ((let uu___126_4882 = p1  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons
                        (fv, (FStar_List.rev pats1)));
                   FStar_Syntax_Syntax.p =
                     (uu___126_4882.FStar_Syntax_Syntax.p)
                 }), sub2))
      | FStar_Syntax_Syntax.Pat_var x ->
          let x1 =
            let uu___127_4901 = x  in
            let uu____4902 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___127_4901.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___127_4901.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4902
            }  in
          let sub2 =
            let uu____4906 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4906
             in
          ((let uu___128_4912 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
              FStar_Syntax_Syntax.p = (uu___128_4912.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_wild x ->
          let x1 =
            let uu___129_4917 = x  in
            let uu____4918 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_4917.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_4917.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4918
            }  in
          let sub2 =
            let uu____4922 = shift_subst (Prims.parse_int "1") sub1  in
            (FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))) ::
              uu____4922
             in
          ((let uu___130_4928 = p1  in
            {
              FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
              FStar_Syntax_Syntax.p = (uu___130_4928.FStar_Syntax_Syntax.p)
            }), sub2)
      | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
          let x1 =
            let uu___131_4938 = x  in
            let uu____4939 = subst sub1 x.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_4938.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_4938.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____4939
            }  in
          let t01 = subst sub1 t0  in
          ((let uu___132_4946 = p1  in
            {
              FStar_Syntax_Syntax.v =
                (FStar_Syntax_Syntax.Pat_dot_term (x1, t01));
              FStar_Syntax_Syntax.p = (uu___132_4946.FStar_Syntax_Syntax.p)
            }), sub1)
       in
    aux [] p
  
let (close_branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch)
  =
  fun uu____4955  ->
    match uu____4955 with
    | (p,wopt,e) ->
        let uu____4975 = close_pat p  in
        (match uu____4975 with
         | (p1,closing) ->
             let wopt1 =
               match wopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some w ->
                   let uu____5012 = subst closing w  in
                   FStar_Pervasives_Native.Some uu____5012
                in
             let e1 = subst closing e  in (p1, wopt1, e1))
  
let (univ_var_opening :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.subst_elt Prims.list,FStar_Syntax_Syntax.univ_name
                                                Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    let s =
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  ->
              fun u  ->
                FStar_Syntax_Syntax.UN
                  ((n1 - i), (FStar_Syntax_Syntax.U_name u))))
       in
    (s, us)
  
let (univ_var_closing :
  FStar_Syntax_Syntax.univ_names -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun us  ->
    let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
    FStar_All.pipe_right us
      (FStar_List.mapi
         (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
  
let (open_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun t  ->
      let uu____5087 = univ_var_opening us  in
      match uu____5087 with | (s,us') -> let t1 = subst s t  in (us', t1)
  
let (open_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2)
  =
  fun us  ->
    fun c  ->
      let uu____5129 = univ_var_opening us  in
      match uu____5129 with
      | (s,us') -> let uu____5152 = subst_comp s c  in (us', uu____5152)
  
let (close_univ_vars :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun us  -> fun t  -> let s = univ_var_closing us  in subst s t 
let (close_univ_vars_comp :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun us  ->
    fun c  ->
      let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
      let s =
        FStar_All.pipe_right us
          (FStar_List.mapi
             (fun i  -> fun u  -> FStar_Syntax_Syntax.UD (u, (n1 - i))))
         in
      subst_comp s c
  
let (open_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun lbs  ->
    fun t  ->
      let uu____5208 =
        let uu____5219 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5219
        then ((Prims.parse_int "0"), lbs, [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5252  ->
                 match uu____5252 with
                 | (i,lbs1,out) ->
                     let x =
                       let uu____5285 =
                         FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                       FStar_Syntax_Syntax.freshen_bv uu____5285  in
                     ((i + (Prims.parse_int "1")),
                       ((let uu___133_5291 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___133_5291.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp =
                             (uu___133_5291.FStar_Syntax_Syntax.lbtyp);
                           FStar_Syntax_Syntax.lbeff =
                             (uu___133_5291.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___133_5291.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___133_5291.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___133_5291.FStar_Syntax_Syntax.lbpos)
                         }) :: lbs1), ((FStar_Syntax_Syntax.DB (i, x)) ::
                       out))) lbs ((Prims.parse_int "0"), [], [])
         in
      match uu____5208 with
      | (n_let_recs,lbs1,let_rec_opening) ->
          let lbs2 =
            FStar_All.pipe_right lbs1
              (FStar_List.map
                 (fun lb  ->
                    let uu____5329 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5357  ->
                             match uu____5357 with
                             | (i,us,out) ->
                                 let u1 =
                                   FStar_Syntax_Syntax.new_univ_name
                                     FStar_Pervasives_Native.None
                                    in
                                 ((i + (Prims.parse_int "1")), (u1 :: us),
                                   ((FStar_Syntax_Syntax.UN
                                       (i, (FStar_Syntax_Syntax.U_name u1)))
                                   :: out))) lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, [], let_rec_opening)
                       in
                    match uu____5329 with
                    | (uu____5398,us,u_let_rec_opening) ->
                        let uu___134_5409 = lb  in
                        let uu____5410 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5411 =
                          subst u_let_rec_opening
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___134_5409.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = us;
                          FStar_Syntax_Syntax.lbtyp = uu____5410;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___134_5409.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5411;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___134_5409.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___134_5409.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_opening t  in (lbs2, t1)
  
let (close_let_rec :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun lbs  ->
    fun t  ->
      let uu____5435 =
        let uu____5442 = FStar_Syntax_Syntax.is_top_level lbs  in
        if uu____5442
        then ((Prims.parse_int "0"), [])
        else
          FStar_List.fold_right
            (fun lb  ->
               fun uu____5464  ->
                 match uu____5464 with
                 | (i,out) ->
                     let uu____5483 =
                       let uu____5486 =
                         let uu____5487 =
                           let uu____5492 =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           (uu____5492, i)  in
                         FStar_Syntax_Syntax.NM uu____5487  in
                       uu____5486 :: out  in
                     ((i + (Prims.parse_int "1")), uu____5483)) lbs
            ((Prims.parse_int "0"), [])
         in
      match uu____5435 with
      | (n_let_recs,let_rec_closing) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____5524 =
                      FStar_List.fold_right
                        (fun u  ->
                           fun uu____5542  ->
                             match uu____5542 with
                             | (i,out) ->
                                 ((i + (Prims.parse_int "1")),
                                   ((FStar_Syntax_Syntax.UD (u, i)) :: out)))
                        lb.FStar_Syntax_Syntax.lbunivs
                        (n_let_recs, let_rec_closing)
                       in
                    match uu____5524 with
                    | (uu____5565,u_let_rec_closing) ->
                        let uu___135_5571 = lb  in
                        let uu____5572 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____5573 =
                          subst u_let_rec_closing
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___135_5571.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___135_5571.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp = uu____5572;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___135_5571.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____5573;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___135_5571.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___135_5571.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let t1 = subst let_rec_closing t  in (lbs1, t1)
  
let (close_tscheme :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun binders  ->
    fun uu____5586  ->
      match uu____5586 with
      | (us,t) ->
          let n1 = (FStar_List.length binders) - (Prims.parse_int "1")  in
          let k = FStar_List.length us  in
          let s =
            FStar_List.mapi
              (fun i  ->
                 fun uu____5615  ->
                   match uu____5615 with
                   | (x,uu____5621) ->
                       FStar_Syntax_Syntax.NM (x, (k + (n1 - i)))) binders
             in
          let t1 = subst s t  in (us, t1)
  
let (close_univ_vars_tscheme :
  FStar_Syntax_Syntax.univ_names ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun us  ->
    fun uu____5642  ->
      match uu____5642 with
      | (us',t) ->
          let n1 = (FStar_List.length us) - (Prims.parse_int "1")  in
          let k = FStar_List.length us'  in
          let s =
            FStar_List.mapi
              (fun i  -> fun x  -> FStar_Syntax_Syntax.UD (x, (k + (n1 - i))))
              us
             in
          let uu____5668 = subst s t  in (us', uu____5668)
  
let (subst_tscheme :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme)
  =
  fun s  ->
    fun uu____5684  ->
      match uu____5684 with
      | (us,t) ->
          let s1 = shift_subst (FStar_List.length us) s  in
          let uu____5698 = subst s1 t  in (us, uu____5698)
  
let (opening_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  ->
    let n1 = (FStar_List.length bs) - (Prims.parse_int "1")  in
    FStar_All.pipe_right bs
      (FStar_List.mapi
         (fun i  ->
            fun uu____5728  ->
              match uu____5728 with
              | (x,uu____5734) -> FStar_Syntax_Syntax.DB ((n1 - i), x)))
  
let (closing_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t) =
  fun bs  -> closing_subst bs 
let (open_term_1 :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun b  ->
    fun t  ->
      let uu____5754 = open_term [b] t  in
      match uu____5754 with
      | (b1::[],t1) -> (b1, t1)
      | uu____5785 -> failwith "impossible: open_term_1"
  
let (open_term_bvs :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bvs  ->
    fun t  ->
      let uu____5814 =
        let uu____5819 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
        open_term uu____5819 t  in
      match uu____5814 with
      | (bs,t1) ->
          let uu____5838 = FStar_List.map FStar_Pervasives_Native.fst bs  in
          (uu____5838, t1)
  
let (open_term_bv :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bv  ->
    fun t  ->
      let uu____5861 = open_term_bvs [bv] t  in
      match uu____5861 with
      | (bv1::[],t1) -> (bv1, t1)
      | uu____5876 -> failwith "impossible: open_term_bv"
  