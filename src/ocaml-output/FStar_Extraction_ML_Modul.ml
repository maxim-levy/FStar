open Prims
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____9 =
        let uu____12 =
          let uu____13 =
            let uu____28 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____29 =
              let uu____32 = FStar_Syntax_Syntax.iarg t  in
              let uu____33 =
                let uu____36 =
                  let uu____37 =
                    let uu____38 =
                      let uu____41 =
                        let uu____42 =
                          let uu____43 =
                            let uu____48 =
                              let uu____49 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.strcat "Not yet implemented:" uu____49
                               in
                            (uu____48, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____43  in
                        FStar_Syntax_Syntax.Tm_constant uu____42  in
                      FStar_Syntax_Syntax.mk uu____41  in
                    uu____38 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____37  in
                [uu____36]  in
              uu____32 :: uu____33  in
            (uu____28, uu____29)  in
          FStar_Syntax_Syntax.Tm_app uu____13  in
        FStar_Syntax_Syntax.mk uu____12  in
      uu____9 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mangle_projector_lid : FStar_Ident.lident -> FStar_Ident.lident) =
  fun x  -> x 
let (lident_as_mlsymbol :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun id1  ->
    FStar_Extraction_ML_Syntax.avoid_keyword
      (id1.FStar_Ident.ident).FStar_Ident.idText
  
let as_pair :
  'Auu____66 .
    'Auu____66 Prims.list ->
      ('Auu____66,'Auu____66) FStar_Pervasives_Native.tuple2
  =
  fun uu___65_76  ->
    match uu___65_76 with
    | a::b::[] -> (a, b)
    | uu____81 -> failwith "Expected a list with 2 elements"
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____93 = FStar_Syntax_Subst.compress x  in
    match uu____93 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____97;
        FStar_Syntax_Syntax.vars = uu____98;_} when
        let uu____105 =
          let uu____106 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____106  in
        uu____105 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____108;
        FStar_Syntax_Syntax.vars = uu____109;_} when
        let uu____116 =
          let uu____117 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____117  in
        uu____116 = "FStar.Pervasives.CInline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____119;
        FStar_Syntax_Syntax.vars = uu____120;_} when
        let uu____127 =
          let uu____128 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____128  in
        uu____127 = "FStar.Pervasives.Substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____130;
        FStar_Syntax_Syntax.vars = uu____131;_} when
        let uu____138 =
          let uu____139 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____139  in
        uu____138 = "FStar.Pervasives.Gc" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____141;
             FStar_Syntax_Syntax.vars = uu____142;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____144));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____145;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____146;_},uu____147)::[]);
        FStar_Syntax_Syntax.pos = uu____148;
        FStar_Syntax_Syntax.vars = uu____149;_} when
        let uu____192 =
          let uu____193 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____193  in
        uu____192 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____195;
             FStar_Syntax_Syntax.vars = uu____196;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (s,uu____198));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____199;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____200;_},uu____201)::[]);
        FStar_Syntax_Syntax.pos = uu____202;
        FStar_Syntax_Syntax.vars = uu____203;_} when
        let uu____246 =
          let uu____247 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____247  in
        uu____246 = "FStar.Pervasives.Comment" ->
        FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.Comment s)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____249));
        FStar_Syntax_Syntax.pos = uu____250;
        FStar_Syntax_Syntax.vars = uu____251;_} when data = "KremlinPrivate"
        -> FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____259));
        FStar_Syntax_Syntax.pos = uu____260;
        FStar_Syntax_Syntax.vars = uu____261;_} when data = "c_inline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string (data,uu____269));
        FStar_Syntax_Syntax.pos = uu____270;
        FStar_Syntax_Syntax.vars = uu____271;_} when data = "substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____279);
        FStar_Syntax_Syntax.pos = uu____280;
        FStar_Syntax_Syntax.vars = uu____281;_} -> extract_meta x1
    | a -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____305 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____305) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,Prims.string Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____343  ->
             match uu____343 with
             | (bv,uu____353) ->
                 let uu____354 =
                   let uu____355 =
                     let uu____358 =
                       let uu____359 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____359  in
                     FStar_Pervasives_Native.Some uu____358  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____355  in
                 let uu____360 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____354, uu____360)) env bs
  
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.term ->
            (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mlmodule1
                                            Prims.list)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun attrs  ->
          fun def  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let def1 =
              let uu____392 =
                let uu____393 = FStar_Syntax_Subst.compress def  in
                FStar_All.pipe_right uu____393 FStar_Syntax_Util.unmeta  in
              FStar_All.pipe_right uu____392 FStar_Syntax_Util.un_uinst  in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____395 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____412 -> def1  in
            let uu____413 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____424) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____445 -> ([], def2)  in
            match uu____413 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___66_466  ->
                       match uu___66_466 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____467 -> false) quals
                   in
                let uu____468 = binders_as_mlty_binders env bs  in
                (match uu____468 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____488 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body  in
                       FStar_All.pipe_right uu____488
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1))
                        in
                     let mangled_projector =
                       let uu____492 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___67_497  ->
                                 match uu___67_497 with
                                 | FStar_Syntax_Syntax.Projector uu____498 ->
                                     true
                                 | uu____503 -> false))
                          in
                       if uu____492
                       then
                         let mname = mangle_projector_lid lid  in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None  in
                     let metadata = extract_metadata attrs  in
                     let td =
                       let uu____534 =
                         let uu____555 = lident_as_mlsymbol lid  in
                         (assumed, uu____555, mangled_projector, ml_bs,
                           metadata,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                          in
                       [uu____534]  in
                     let def3 =
                       let uu____607 =
                         let uu____608 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid)
                            in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____608  in
                       [uu____607; FStar_Extraction_ML_Syntax.MLM_Ty td]  in
                     let env2 =
                       let uu____610 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___68_614  ->
                                 match uu___68_614 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____615 -> false))
                          in
                       if uu____610
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td
                        in
                     (env2, def3))
  
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }[@@deriving show]
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
  
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dtyp
  
type inductive_family =
  {
  iname: FStar_Ident.lident ;
  iparams: FStar_Syntax_Syntax.binders ;
  ityp: FStar_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list ;
  imetadata: FStar_Extraction_ML_Syntax.metadata }[@@deriving show]
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iname
  
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iparams
  
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__ityp
  
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__idatas
  
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__iquals
  
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; imetadata = __fname__imetadata;_} ->
        __fname__imetadata
  
let (print_ifamily : inductive_family -> Prims.unit) =
  fun i  ->
    let uu____754 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____755 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____756 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____757 =
      let uu____758 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____769 = FStar_Syntax_Print.lid_to_string d.dname  in
                let uu____770 =
                  let uu____771 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.strcat " : " uu____771  in
                Prims.strcat uu____769 uu____770))
         in
      FStar_All.pipe_right uu____758 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____754 uu____755 uu____756
      uu____757
  
let bundle_as_inductive_families :
  'Auu____779 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____779 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____810 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____857 = FStar_Syntax_Subst.open_term bs t  in
                       (match uu____857 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____896,t2,l',nparams,uu____900)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____905 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____905 with
                                           | (bs',body) ->
                                               let uu____938 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____938 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____1009  ->
                                                           fun uu____1010  ->
                                                             match (uu____1009,
                                                                    uu____1010)
                                                             with
                                                             | ((b',uu____1028),
                                                                (b,uu____1030))
                                                                 ->
                                                                 let uu____1039
                                                                   =
                                                                   let uu____1046
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____1046)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1039)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____1048 =
                                                        let uu____1051 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1051
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____1048
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1056 -> []))
                               in
                            let metadata =
                              extract_metadata
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs)
                               in
                            let env2 =
                              let uu____1061 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1061
                               in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 imetadata = metadata
                               }]))
                   | uu____1064 -> (env1, [])) env ses
             in
          match uu____810 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
  
type env_t = FStar_Extraction_ML_UEnv.env[@@deriving show]
let (extract_bundle :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1140 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1140
           in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]  in
        let names1 =
          let uu____1147 =
            let uu____1148 =
              let uu____1151 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____1151  in
            uu____1148.FStar_Syntax_Syntax.n  in
          match uu____1147 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1155) ->
              FStar_List.map
                (fun uu____1181  ->
                   match uu____1181 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1187;
                        FStar_Syntax_Syntax.sort = uu____1188;_},uu____1189)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1192 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____1203 =
          let uu____1204 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
          FStar_Pervasives_Native.fst uu____1204  in
        let uu____1209 =
          let uu____1220 = lident_as_mlsymbol ctor.dname  in
          let uu____1221 =
            let uu____1228 = FStar_Extraction_ML_Util.argTypes mlt  in
            FStar_List.zip names1 uu____1228  in
          (uu____1220, uu____1221)  in
        (uu____1203, uu____1209)  in
      let extract_one_family env1 ind =
        let uu____1276 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____1276 with
        | (env2,vars) ->
            let uu____1311 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2)
               in
            (match uu____1311 with
             | (env3,ctors) ->
                 let uu____1404 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____1404 with
                  | (indices,uu____1440) ->
                      let ml_params =
                        let uu____1460 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1479  ->
                                    let uu____1484 =
                                      FStar_Util.string_of_int i  in
                                    Prims.strcat "'dummyV" uu____1484))
                           in
                        FStar_List.append vars uu____1460  in
                      let tbody =
                        let uu____1486 =
                          FStar_Util.find_opt
                            (fun uu___69_1491  ->
                               match uu___69_1491 with
                               | FStar_Syntax_Syntax.RecordType uu____1492 ->
                                   true
                               | uu____1501 -> false) ind.iquals
                           in
                        match uu____1486 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1512 = FStar_List.hd ctors  in
                            (match uu____1512 with
                             | (uu____1533,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____1572  ->
                                          match uu____1572 with
                                          | (uu____1581,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____1584 =
                                                lident_as_mlsymbol lid  in
                                              (uu____1584, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1585 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____1588 =
                        let uu____1607 = lident_as_mlsymbol ind.iname  in
                        (false, uu____1607, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env3, uu____1588)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1641,t,uu____1643,uu____1644,uu____1645);
            FStar_Syntax_Syntax.sigrng = uu____1646;
            FStar_Syntax_Syntax.sigquals = uu____1647;
            FStar_Syntax_Syntax.sigmeta = uu____1648;
            FStar_Syntax_Syntax.sigattrs = uu____1649;_}::[],uu____1650),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1667 = extract_ctor [] env { dname = l; dtyp = t }  in
          (match uu____1667 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1713),quals) ->
          let uu____1727 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____1727 with
           | (env1,ifams) ->
               let uu____1748 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____1748 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1841 -> failwith "Unexpected signature element"
  
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g  ->
    fun se  ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top
         in
      let uu____1867 =
        (let uu____1870 = FStar_Options.codegen ()  in
         uu____1870 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin))
          ||
          (let uu____1876 =
             FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
               FStar_Parser_Const.plugin_attr
              in
           Prims.op_Negation uu____1876)
         in
      if uu____1867
      then []
      else
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let mk_registration lb =
               let fv =
                 let uu____1897 =
                   let uu____1900 =
                     FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                   uu____1900.FStar_Syntax_Syntax.fv_name  in
                 uu____1897.FStar_Syntax_Syntax.v  in
               let fv_t = lb.FStar_Syntax_Syntax.lbtyp  in
               let ml_name_str =
                 let uu____1905 =
                   let uu____1906 = FStar_Ident.string_of_lid fv  in
                   FStar_Extraction_ML_Syntax.MLC_String uu____1906  in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____1905  in
               let uu____1907 =
                 FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                   g.FStar_Extraction_ML_UEnv.tcenv fv fv_t ml_name_str
                  in
               match uu____1907 with
               | FStar_Pervasives_Native.Some (interp,arity,plugin1) ->
                   let register =
                     if plugin1
                     then "FStar_Tactics_Native.register_plugin"
                     else "FStar_Tactics_Native.register_tactic"  in
                   let h =
                     let uu____1930 =
                       let uu____1931 =
                         let uu____1932 = FStar_Ident.lid_of_str register  in
                         FStar_Extraction_ML_Syntax.mlpath_of_lident
                           uu____1932
                          in
                       FStar_Extraction_ML_Syntax.MLE_Name uu____1931  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top) uu____1930
                      in
                   let arity1 =
                     let uu____1934 =
                       let uu____1935 =
                         let uu____1946 = FStar_Util.string_of_int arity  in
                         (uu____1946, FStar_Pervasives_Native.None)  in
                       FStar_Extraction_ML_Syntax.MLC_Int uu____1935  in
                     FStar_Extraction_ML_Syntax.MLE_Const uu____1934  in
                   let app =
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top)
                       (FStar_Extraction_ML_Syntax.MLE_App
                          (h, [w ml_name_str; w arity1; interp]))
                      in
                   [FStar_Extraction_ML_Syntax.MLM_Top app]
               | FStar_Pervasives_Native.None  -> []  in
             FStar_List.collect mk_registration
               (FStar_Pervasives_Native.snd lbs)
         | uu____1968 -> [])
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1991 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1991);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1998 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____2007 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____2024 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____2062 =
               let uu____2067 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2067 ml_name tysc
                 false false
                in
             match uu____2062 with
             | (g2,mangled_name) ->
                 ((let uu____2075 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify")
                      in
                   if uu____2075
                   then FStar_Util.print1 "Mangled name: %s\n" mangled_name
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.mllb_meta = [];
                       FStar_Extraction_ML_Syntax.print_typ = false
                     }  in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [lb])))))
              in
           let rec extract_fv tm =
             (let uu____2089 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2089
              then
                let uu____2090 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2090
              else ());
             (let uu____2092 =
                let uu____2093 = FStar_Syntax_Subst.compress tm  in
                uu____2093.FStar_Syntax_Syntax.n  in
              match uu____2092 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2101) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  let uu____2108 =
                    let uu____2117 = FStar_Extraction_ML_UEnv.lookup_fv g fv
                       in
                    FStar_All.pipe_left FStar_Util.right uu____2117  in
                  (match uu____2108 with
                   | (uu____2174,uu____2175,tysc,uu____2177) ->
                       let uu____2178 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                          in
                       (uu____2178, tysc))
              | uu____2179 -> failwith "Not an fv")
              in
           let extract_action g1 a =
             (let uu____2205 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____2205
              then
                let uu____2206 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ
                   in
                let uu____2207 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn
                   in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2206
                  uu____2207
              else ());
             (let uu____2209 = FStar_Extraction_ML_UEnv.action_name ed a  in
              match uu____2209 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2225 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun
                       in
                    FStar_Util.Inl uu____2225  in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn),
                        ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                     in
                  let lbs = (false, [lb])  in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                     in
                  let uu____2251 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
                  (match uu____2251 with
                   | (a_let,uu____2263,ty) ->
                       ((let uu____2266 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify")
                            in
                         if uu____2266
                         then
                           let uu____2267 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let
                              in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2267
                         else ());
                        (let uu____2269 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2278,mllb::[]),uu____2280) ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2298 -> failwith "Impossible"  in
                         match uu____2269 with
                         | (exp,tysc) ->
                             ((let uu____2310 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify")
                                  in
                               if uu____2310
                               then
                                 ((let uu____2312 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc)
                                      in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2312);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         x)
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc)))))
              in
           let uu____2316 =
             let uu____2321 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr)
                in
             match uu____2321 with
             | (return_tm,ty_sc) ->
                 let uu____2334 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
                 (match uu____2334 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc)
              in
           (match uu____2316 with
            | (g1,return_decl) ->
                let uu____2353 =
                  let uu____2358 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr)
                     in
                  match uu____2358 with
                  | (bind_tm,ty_sc) ->
                      let uu____2371 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                      (match uu____2371 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc)
                   in
                (match uu____2353 with
                 | (g2,bind_decl) ->
                     let uu____2390 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions
                        in
                     (match uu____2390 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_splice uu____2411 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____2418 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2422,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let uu____2430 =
             let uu____2431 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___70_2435  ->
                       match uu___70_2435 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2436 -> false))
                in
             Prims.op_Negation uu____2431  in
           if uu____2430
           then (g, [])
           else
             (let uu____2446 = FStar_Syntax_Util.arrow_formals t  in
              match uu____2446 with
              | (bs,uu____2466) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None
                     in
                  let uu____2484 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None
                     in
                  extract_typ_abbrev g fv quals attrs uu____2484)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2486) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2502 =
             let uu____2511 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
                in
             match uu____2511 with
             | (tcenv,uu____2535,def_typ) ->
                 let uu____2541 = as_pair def_typ  in (tcenv, uu____2541)
              in
           (match uu____2502 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp
                   in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1
                   in
                let uu____2565 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                extract_typ_abbrev g uu____2565 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2567) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2578 =
             let uu____2585 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let
                    (lbs, FStar_Syntax_Util.exp_false_bool))
                 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng
                in
             FStar_Extraction_ML_Term.term_as_mlexpr g uu____2585  in
           (match uu____2578 with
            | (ml_let,uu____2595,uu____2596) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,bindings),uu____2605) ->
                     let flags1 =
                       FStar_List.choose
                         (fun uu___71_2620  ->
                            match uu___71_2620 with
                            | FStar_Syntax_Syntax.Assumption  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Assumed
                            | FStar_Syntax_Syntax.Private  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.Private
                            | FStar_Syntax_Syntax.NoExtract  ->
                                FStar_Pervasives_Native.Some
                                  FStar_Extraction_ML_Syntax.NoExtract
                            | uu____2623 -> FStar_Pervasives_Native.None)
                         quals
                        in
                     let flags' = extract_metadata attrs  in
                     let uu____2627 =
                       FStar_List.fold_left2
                         (fun uu____2659  ->
                            fun ml_lb  ->
                              fun uu____2661  ->
                                match (uu____2659, uu____2661) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2683;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2685;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2686;
                                                  FStar_Syntax_Syntax.lbattrs
                                                    = uu____2687;
                                                  FStar_Syntax_Syntax.lbpos =
                                                    uu____2688;_})
                                    ->
                                    let lb_lid =
                                      let uu____2714 =
                                        let uu____2717 =
                                          FStar_Util.right lbname  in
                                        uu____2717.FStar_Syntax_Syntax.fv_name
                                         in
                                      uu____2714.FStar_Syntax_Syntax.v  in
                                    let flags'' =
                                      let uu____2721 =
                                        let uu____2722 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____2722.FStar_Syntax_Syntax.n  in
                                      match uu____2721 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (uu____2727,{
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Comp
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____2728;
                                                            FStar_Syntax_Syntax.effect_name
                                                              = e;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = uu____2730;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____2731;
                                                            FStar_Syntax_Syntax.flags
                                                              = uu____2732;_};
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____2733;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____2734;_})
                                          when
                                          let uu____2767 =
                                            FStar_Ident.string_of_lid e  in
                                          uu____2767 =
                                            "FStar.HyperStack.ST.StackInline"
                                          ->
                                          [FStar_Extraction_ML_Syntax.StackInline]
                                      | uu____2768 -> []  in
                                    let meta =
                                      FStar_List.append flags1
                                        (FStar_List.append flags' flags'')
                                       in
                                    let ml_lb1 =
                                      let uu___75_2773 = ml_lb  in
                                      {
                                        FStar_Extraction_ML_Syntax.mllb_name
                                          =
                                          (uu___75_2773.FStar_Extraction_ML_Syntax.mllb_name);
                                        FStar_Extraction_ML_Syntax.mllb_tysc
                                          =
                                          (uu___75_2773.FStar_Extraction_ML_Syntax.mllb_tysc);
                                        FStar_Extraction_ML_Syntax.mllb_add_unit
                                          =
                                          (uu___75_2773.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                        FStar_Extraction_ML_Syntax.mllb_def =
                                          (uu___75_2773.FStar_Extraction_ML_Syntax.mllb_def);
                                        FStar_Extraction_ML_Syntax.mllb_meta
                                          = meta;
                                        FStar_Extraction_ML_Syntax.print_typ
                                          =
                                          (uu___75_2773.FStar_Extraction_ML_Syntax.print_typ)
                                      }  in
                                    let uu____2774 =
                                      let uu____2779 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___72_2784  ->
                                                match uu___72_2784 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2785 -> true
                                                | uu____2790 -> false))
                                         in
                                      if uu____2779
                                      then
                                        let mname =
                                          let uu____2796 =
                                            mangle_projector_lid lb_lid  in
                                          FStar_All.pipe_right uu____2796
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                           in
                                        let uu____2797 =
                                          let uu____2802 =
                                            FStar_Util.right lbname  in
                                          let uu____2803 =
                                            FStar_Util.must
                                              ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                             in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2802 mname uu____2803
                                            ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false
                                           in
                                        match uu____2797 with
                                        | (env1,uu____2809) ->
                                            (env1,
                                              (let uu___76_2811 = ml_lb1  in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   (FStar_Pervasives_Native.snd
                                                      mname);
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___76_2811.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___76_2811.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___76_2811.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.mllb_meta
                                                   =
                                                   (uu___76_2811.FStar_Extraction_ML_Syntax.mllb_meta);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___76_2811.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2815 =
                                           let uu____2816 =
                                             let uu____2821 =
                                               FStar_Util.must
                                                 ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2821
                                               ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2816
                                            in
                                         (uu____2815, ml_lb1))
                                       in
                                    (match uu____2774 with
                                     | (g1,ml_lb2) ->
                                         (g1, (ml_lb2 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs)
                        in
                     (match uu____2627 with
                      | (g1,ml_lbs') ->
                          let uu____2852 =
                            let uu____2855 =
                              let uu____2858 =
                                let uu____2859 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng
                                   in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2859
                                 in
                              [uu____2858;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.rev ml_lbs'))]
                               in
                            let uu____2862 = maybe_register_plugin g1 se  in
                            FStar_List.append uu____2855 uu____2862  in
                          (g1, uu____2852))
                 | uu____2867 ->
                     let uu____2868 =
                       let uu____2869 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let
                          in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2869
                        in
                     failwith uu____2868))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2877,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____2882 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption)
              in
           if uu____2882
           then
             let always_fail =
               let imp =
                 let uu____2893 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____2893 with
                 | ([],t1) ->
                     let b =
                       let uu____2922 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1
                          in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____2922
                        in
                     let uu____2923 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs [b] uu____2923
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____2942 = fail_exp lid t1  in
                     FStar_Syntax_Util.abs bs uu____2942
                       FStar_Pervasives_Native.None
                  in
               let uu___77_2943 = se  in
               let uu____2944 =
                 let uu____2945 =
                   let uu____2952 =
                     let uu____2959 =
                       let uu____2962 =
                         let uu____2963 =
                           let uu____2968 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None
                              in
                           FStar_Util.Inr uu____2968  in
                         {
                           FStar_Syntax_Syntax.lbname = uu____2963;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp;
                           FStar_Syntax_Syntax.lbattrs = [];
                           FStar_Syntax_Syntax.lbpos =
                             (imp.FStar_Syntax_Syntax.pos)
                         }  in
                       [uu____2962]  in
                     (false, uu____2959)  in
                   (uu____2952, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____2945  in
               {
                 FStar_Syntax_Syntax.sigel = uu____2944;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___77_2943.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___77_2943.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___77_2943.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___77_2943.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____2981 = extract_sig g always_fail  in
             (match uu____2981 with
              | (g1,mlm) ->
                  let uu____3000 =
                    FStar_Util.find_map quals
                      (fun uu___73_3005  ->
                         match uu___73_3005 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3009 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____3000 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3017 =
                         let uu____3020 =
                           let uu____3021 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3021  in
                         let uu____3022 =
                           let uu____3025 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____3025]  in
                         uu____3020 :: uu____3022  in
                       (g1, uu____3017)
                   | uu____3028 ->
                       let uu____3031 =
                         FStar_Util.find_map quals
                           (fun uu___74_3037  ->
                              match uu___74_3037 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3041)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3042 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____3031 with
                        | FStar_Pervasives_Native.Some uu____3049 -> (g1, [])
                        | uu____3052 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3061 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____3061 with
            | (ml_main,uu____3075,uu____3076) ->
                let uu____3077 =
                  let uu____3080 =
                    let uu____3081 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3081  in
                  [uu____3080; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____3077))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3084 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3091 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3100 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3103 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t) =
  fun g  ->
    fun m  ->
      let uu____3128 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3128 FStar_Pervasives_Native.fst
  
let (extract' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____3170 = FStar_Options.restore_cmd_line_options true  in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name
          in
       let g1 =
         let uu___78_3173 = g  in
         let uu____3174 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name
            in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3174;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___78_3173.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___78_3173.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___78_3173.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         }  in
       let uu____3175 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations
          in
       match uu____3175 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs  in
           let is_kremlin =
             let uu____3204 = FStar_Options.codegen ()  in
             uu____3204 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
              in
           let uu____3209 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
              in
           if uu____3209
           then
             ((let uu____3217 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                  in
               FStar_Util.print1 "Extracted module %s\n" uu____3217);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))
  
let (extract :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun m  ->
      let uu____3291 = FStar_Options.debug_any ()  in
      if uu____3291
      then
        let msg =
          let uu____3299 =
            FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
          FStar_Util.format1 "Extracting module %s\n" uu____3299  in
        FStar_Util.measure_execution_time msg
          (fun uu____3307  -> extract' g m)
      else extract' g m
  