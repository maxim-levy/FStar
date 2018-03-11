open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }[@@deriving show]
let (__proj__Mkenv__item__env : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__env
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__subst
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env  -> fun tc_const  -> { env; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts,FStar_Syntax_Syntax.eff_decl)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___75_93 = a  in
              let uu____94 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___75_93.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___75_93.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____94
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____102 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____102
             then
               (d "Elaborating extra WP combinators";
                (let uu____104 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____104))
             else ());
            (let rec collect_binders t =
               let uu____116 =
                 let uu____117 =
                   let uu____120 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____120
                    in
                 uu____117.FStar_Syntax_Syntax.n  in
               match uu____116 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____151) -> t1
                     | uu____160 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____163 = collect_binders rest  in
                   FStar_List.append bs uu____163
               | FStar_Syntax_Syntax.Tm_type uu____174 -> []
               | uu____179 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____197 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____197 FStar_Syntax_Util.name_binders
                in
             (let uu____217 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____217
              then
                let uu____218 =
                  let uu____219 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____219  in
                d uu____218
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____245 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____245 with
                | (sigelt,fv) ->
                    ((let uu____253 =
                        let uu____256 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____256
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____253);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____376  ->
                     match uu____376 with
                     | (t,b) ->
                         let uu____387 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____387))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____418 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____418))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____441 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____441)
                 in
              let uu____442 =
                let uu____457 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____479 = f (FStar_Syntax_Syntax.bv_to_name t)
                         in
                      FStar_Syntax_Util.arrow gamma uu____479  in
                    let uu____482 =
                      let uu____483 =
                        let uu____490 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____491 =
                          let uu____494 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____494]  in
                        uu____490 :: uu____491  in
                      FStar_List.append binders uu____483  in
                    FStar_Syntax_Util.abs uu____482 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____499 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____500 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____499, uu____500)  in
                match uu____457 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____534 =
                        let uu____535 =
                          let uu____550 =
                            let uu____557 =
                              FStar_List.map
                                (fun uu____577  ->
                                   match uu____577 with
                                   | (bv,uu____587) ->
                                       let uu____588 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____589 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____588, uu____589)) binders
                               in
                            let uu____590 =
                              let uu____597 =
                                let uu____602 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____603 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____602, uu____603)  in
                              let uu____604 =
                                let uu____611 =
                                  let uu____616 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____616)  in
                                [uu____611]  in
                              uu____597 :: uu____604  in
                            FStar_List.append uu____557 uu____590  in
                          (fv, uu____550)  in
                        FStar_Syntax_Syntax.Tm_app uu____535  in
                      mk1 uu____534  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____442 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____675 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____675
                       in
                    let ret1 =
                      let uu____679 =
                        let uu____680 =
                          let uu____683 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____683  in
                        FStar_Syntax_Util.residual_tot uu____680  in
                      FStar_Pervasives_Native.Some uu____679  in
                    let body =
                      let uu____685 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____685 ret1  in
                    let uu____686 =
                      let uu____687 = mk_all_implicit binders  in
                      let uu____694 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____687 uu____694  in
                    FStar_Syntax_Util.abs uu____686 body ret1  in
                  let c_pure1 =
                    let uu____722 = mk_lid "pure"  in
                    register env1 uu____722 c_pure  in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let l =
                      let uu____727 =
                        let uu____728 =
                          let uu____729 =
                            let uu____736 =
                              let uu____737 =
                                let uu____738 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____738
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____737  in
                            [uu____736]  in
                          let uu____739 =
                            let uu____742 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____742  in
                          FStar_Syntax_Util.arrow uu____729 uu____739  in
                        mk_gctx uu____728  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____727
                       in
                    let r =
                      let uu____744 =
                        let uu____745 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____745  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____744
                       in
                    let ret1 =
                      let uu____749 =
                        let uu____750 =
                          let uu____753 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____753  in
                        FStar_Syntax_Util.residual_tot uu____750  in
                      FStar_Pervasives_Native.Some uu____749  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____761 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____764 =
                          let uu____773 =
                            let uu____776 =
                              let uu____777 =
                                let uu____778 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____778
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____777  in
                            [uu____776]  in
                          FStar_List.append gamma_as_args uu____773  in
                        FStar_Syntax_Util.mk_app uu____761 uu____764  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____781 =
                      let uu____782 = mk_all_implicit binders  in
                      let uu____789 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____782 uu____789  in
                    FStar_Syntax_Util.abs uu____781 outer_body ret1  in
                  let c_app1 =
                    let uu____825 = mk_lid "app"  in
                    register env1 uu____825 c_app  in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____832 =
                        let uu____839 =
                          let uu____840 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____840  in
                        [uu____839]  in
                      let uu____841 =
                        let uu____844 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____844  in
                      FStar_Syntax_Util.arrow uu____832 uu____841  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____847 =
                        let uu____848 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____848  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____847
                       in
                    let ret1 =
                      let uu____852 =
                        let uu____853 =
                          let uu____856 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____856  in
                        FStar_Syntax_Util.residual_tot uu____853  in
                      FStar_Pervasives_Native.Some uu____852  in
                    let uu____857 =
                      let uu____858 = mk_all_implicit binders  in
                      let uu____865 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____858 uu____865  in
                    let uu____900 =
                      let uu____901 =
                        let uu____910 =
                          let uu____913 =
                            let uu____916 =
                              let uu____925 =
                                let uu____928 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____928]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____925
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____916  in
                          let uu____929 =
                            let uu____934 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____934]  in
                          uu____913 :: uu____929  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____910
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____901  in
                    FStar_Syntax_Util.abs uu____857 uu____900 ret1  in
                  let c_lift11 =
                    let uu____938 = mk_lid "lift1"  in
                    register env1 uu____938 c_lift1  in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____946 =
                        let uu____953 =
                          let uu____954 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____954  in
                        let uu____955 =
                          let uu____958 =
                            let uu____959 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.null_binder uu____959  in
                          [uu____958]  in
                        uu____953 :: uu____955  in
                      let uu____960 =
                        let uu____963 = FStar_Syntax_Syntax.bv_to_name t3  in
                        FStar_Syntax_Syntax.mk_GTotal uu____963  in
                      FStar_Syntax_Util.arrow uu____946 uu____960  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____966 =
                        let uu____967 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____967  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____966
                       in
                    let a2 =
                      let uu____969 =
                        let uu____970 = FStar_Syntax_Syntax.bv_to_name t2  in
                        mk_gctx uu____970  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____969
                       in
                    let ret1 =
                      let uu____974 =
                        let uu____975 =
                          let uu____978 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____978  in
                        FStar_Syntax_Util.residual_tot uu____975  in
                      FStar_Pervasives_Native.Some uu____974  in
                    let uu____979 =
                      let uu____980 = mk_all_implicit binders  in
                      let uu____987 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____980 uu____987  in
                    let uu____1030 =
                      let uu____1031 =
                        let uu____1040 =
                          let uu____1043 =
                            let uu____1046 =
                              let uu____1055 =
                                let uu____1058 =
                                  let uu____1061 =
                                    let uu____1070 =
                                      let uu____1073 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1073]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1070
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1061
                                   in
                                let uu____1074 =
                                  let uu____1079 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1079]  in
                                uu____1058 :: uu____1074  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1055
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1046  in
                          let uu____1082 =
                            let uu____1087 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1087]  in
                          uu____1043 :: uu____1082  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1040
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1031  in
                    FStar_Syntax_Util.abs uu____979 uu____1030 ret1  in
                  let c_lift21 =
                    let uu____1091 = mk_lid "lift2"  in
                    register env1 uu____1091 c_lift2  in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1098 =
                        let uu____1105 =
                          let uu____1106 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1106  in
                        [uu____1105]  in
                      let uu____1107 =
                        let uu____1110 =
                          let uu____1111 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1111  in
                        FStar_Syntax_Syntax.mk_Total uu____1110  in
                      FStar_Syntax_Util.arrow uu____1098 uu____1107  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1116 =
                        let uu____1117 =
                          let uu____1120 =
                            let uu____1121 =
                              let uu____1128 =
                                let uu____1129 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1129
                                 in
                              [uu____1128]  in
                            let uu____1130 =
                              let uu____1133 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1133  in
                            FStar_Syntax_Util.arrow uu____1121 uu____1130  in
                          mk_ctx uu____1120  in
                        FStar_Syntax_Util.residual_tot uu____1117  in
                      FStar_Pervasives_Native.Some uu____1116  in
                    let e1 =
                      let uu____1135 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1135
                       in
                    let body =
                      let uu____1137 =
                        let uu____1138 =
                          let uu____1145 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1145]  in
                        FStar_List.append gamma uu____1138  in
                      let uu____1150 =
                        let uu____1151 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1154 =
                          let uu____1163 =
                            let uu____1164 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1164  in
                          let uu____1165 = args_of_binders1 gamma  in
                          uu____1163 :: uu____1165  in
                        FStar_Syntax_Util.mk_app uu____1151 uu____1154  in
                      FStar_Syntax_Util.abs uu____1137 uu____1150 ret1  in
                    let uu____1168 =
                      let uu____1169 = mk_all_implicit binders  in
                      let uu____1176 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1169 uu____1176  in
                    FStar_Syntax_Util.abs uu____1168 body ret1  in
                  let c_push1 =
                    let uu____1208 = mk_lid "push"  in
                    register env1 uu____1208 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1228 =
                        let uu____1229 =
                          let uu____1244 = args_of_binders1 binders  in
                          (c, uu____1244)  in
                        FStar_Syntax_Syntax.Tm_app uu____1229  in
                      mk1 uu____1228
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1254 =
                        let uu____1255 =
                          let uu____1262 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1263 =
                            let uu____1266 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1266]  in
                          uu____1262 :: uu____1263  in
                        let uu____1267 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1255 uu____1267  in
                      FStar_Syntax_Syntax.mk_Total uu____1254  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1271 =
                      let uu____1272 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1272  in
                    let uu____1283 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1285 =
                        let uu____1288 =
                          let uu____1297 =
                            let uu____1300 =
                              let uu____1303 =
                                let uu____1312 =
                                  let uu____1313 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1313  in
                                [uu____1312]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1303  in
                            [uu____1300]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1297
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1288  in
                      FStar_Syntax_Util.ascribe uu____1285
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1271 uu____1283
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1333 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1333 wp_if_then_else  in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1  in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1344 =
                        let uu____1353 =
                          let uu____1356 =
                            let uu____1359 =
                              let uu____1368 =
                                let uu____1371 =
                                  let uu____1374 =
                                    let uu____1383 =
                                      let uu____1384 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1384
                                       in
                                    [uu____1383]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1374
                                   in
                                [uu____1371]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1368
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1359  in
                          let uu____1389 =
                            let uu____1394 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1394]  in
                          uu____1356 :: uu____1389  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1353
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1344  in
                    let uu____1397 =
                      let uu____1398 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1398  in
                    FStar_Syntax_Util.abs uu____1397 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1410 = mk_lid "wp_assert"  in
                    register env1 uu____1410 wp_assert  in
                  let wp_assert2 = mk_generic_app wp_assert1  in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1421 =
                        let uu____1430 =
                          let uu____1433 =
                            let uu____1436 =
                              let uu____1445 =
                                let uu____1448 =
                                  let uu____1451 =
                                    let uu____1460 =
                                      let uu____1461 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1461
                                       in
                                    [uu____1460]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1451
                                   in
                                [uu____1448]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1445
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1436  in
                          let uu____1466 =
                            let uu____1471 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1471]  in
                          uu____1433 :: uu____1466  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1430
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1421  in
                    let uu____1474 =
                      let uu____1475 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1475  in
                    FStar_Syntax_Util.abs uu____1474 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1487 = mk_lid "wp_assume"  in
                    register env1 uu____1487 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1496 =
                        let uu____1503 =
                          let uu____1504 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1504  in
                        [uu____1503]  in
                      let uu____1505 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1496 uu____1505  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1512 =
                        let uu____1521 =
                          let uu____1524 =
                            let uu____1527 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1527  in
                          let uu____1536 =
                            let uu____1541 =
                              let uu____1544 =
                                let uu____1553 =
                                  let uu____1556 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1556]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1553
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1544  in
                            [uu____1541]  in
                          uu____1524 :: uu____1536  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1521
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1512  in
                    let uu____1563 =
                      let uu____1564 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1564  in
                    FStar_Syntax_Util.abs uu____1563 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1576 = mk_lid "wp_close"  in
                    register env1 uu____1576 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____1586 =
                      let uu____1587 =
                        let uu____1588 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1588
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1587  in
                    FStar_Pervasives_Native.Some uu____1586  in
                  let mk_forall1 x body =
                    let uu____1600 =
                      let uu____1603 =
                        let uu____1604 =
                          let uu____1619 =
                            let uu____1622 =
                              let uu____1623 =
                                let uu____1624 =
                                  let uu____1625 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1625]  in
                                FStar_Syntax_Util.abs uu____1624 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1623  in
                            [uu____1622]  in
                          (FStar_Syntax_Util.tforall, uu____1619)  in
                        FStar_Syntax_Syntax.Tm_app uu____1604  in
                      FStar_Syntax_Syntax.mk uu____1603  in
                    uu____1600 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____1635 =
                      let uu____1636 = FStar_Syntax_Subst.compress t  in
                      uu____1636.FStar_Syntax_Syntax.n  in
                    match uu____1635 with
                    | FStar_Syntax_Syntax.Tm_type uu____1639 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1665  ->
                              match uu____1665 with
                              | (b,uu____1671) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1672 -> true  in
                  let rec is_monotonic t =
                    let uu____1677 =
                      let uu____1678 = FStar_Syntax_Subst.compress t  in
                      uu____1678.FStar_Syntax_Syntax.n  in
                    match uu____1677 with
                    | FStar_Syntax_Syntax.Tm_type uu____1681 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1707  ->
                              match uu____1707 with
                              | (b,uu____1713) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1714 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t
                       in
                    let uu____1766 =
                      let uu____1767 = FStar_Syntax_Subst.compress t1  in
                      uu____1767.FStar_Syntax_Syntax.n  in
                    match uu____1766 with
                    | FStar_Syntax_Syntax.Tm_type uu____1770 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1773);
                                      FStar_Syntax_Syntax.pos = uu____1774;
                                      FStar_Syntax_Syntax.vars = uu____1775;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____1813 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1813
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____1816 =
                              let uu____1819 =
                                let uu____1828 =
                                  let uu____1829 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1829  in
                                [uu____1828]  in
                              FStar_Syntax_Util.mk_app x uu____1819  in
                            let uu____1830 =
                              let uu____1833 =
                                let uu____1842 =
                                  let uu____1843 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1843  in
                                [uu____1842]  in
                              FStar_Syntax_Util.mk_app y uu____1833  in
                            mk_rel1 b uu____1816 uu____1830  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____1848 =
                               let uu____1849 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____1852 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1849 uu____1852  in
                             let uu____1855 =
                               let uu____1856 =
                                 let uu____1859 =
                                   let uu____1868 =
                                     let uu____1869 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____1869
                                      in
                                   [uu____1868]  in
                                 FStar_Syntax_Util.mk_app x uu____1859  in
                               let uu____1870 =
                                 let uu____1873 =
                                   let uu____1882 =
                                     let uu____1883 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____1883
                                      in
                                   [uu____1882]  in
                                 FStar_Syntax_Util.mk_app y uu____1873  in
                               mk_rel1 b uu____1856 uu____1870  in
                             FStar_Syntax_Util.mk_imp uu____1848 uu____1855
                              in
                           let uu____1884 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____1884)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1887);
                                      FStar_Syntax_Syntax.pos = uu____1888;
                                      FStar_Syntax_Syntax.vars = uu____1889;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____1927 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1927
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____1930 =
                              let uu____1933 =
                                let uu____1942 =
                                  let uu____1943 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1943  in
                                [uu____1942]  in
                              FStar_Syntax_Util.mk_app x uu____1933  in
                            let uu____1944 =
                              let uu____1947 =
                                let uu____1956 =
                                  let uu____1957 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1957  in
                                [uu____1956]  in
                              FStar_Syntax_Util.mk_app y uu____1947  in
                            mk_rel1 b uu____1930 uu____1944  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____1962 =
                               let uu____1963 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____1966 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1963 uu____1966  in
                             let uu____1969 =
                               let uu____1970 =
                                 let uu____1973 =
                                   let uu____1982 =
                                     let uu____1983 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____1983
                                      in
                                   [uu____1982]  in
                                 FStar_Syntax_Util.mk_app x uu____1973  in
                               let uu____1984 =
                                 let uu____1987 =
                                   let uu____1996 =
                                     let uu____1997 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____1997
                                      in
                                   [uu____1996]  in
                                 FStar_Syntax_Util.mk_app y uu____1987  in
                               mk_rel1 b uu____1970 uu____1984  in
                             FStar_Syntax_Util.mk_imp uu____1962 uu____1969
                              in
                           let uu____1998 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____1998)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___76_2029 = t1  in
                          let uu____2030 =
                            let uu____2031 =
                              let uu____2044 =
                                let uu____2045 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2045  in
                              ([binder], uu____2044)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2031  in
                          {
                            FStar_Syntax_Syntax.n = uu____2030;
                            FStar_Syntax_Syntax.pos =
                              (uu___76_2029.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___76_2029.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2060 ->
                        failwith "unhandled arrow"
                    | uu____2073 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
                  let stronger =
                    let wp1 =
                      FStar_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let wp2 =
                      FStar_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant] env1 t
                         in
                      let uu____2088 =
                        let uu____2089 = FStar_Syntax_Subst.compress t1  in
                        uu____2089.FStar_Syntax_Syntax.n  in
                      match uu____2088 with
                      | FStar_Syntax_Syntax.Tm_type uu____2092 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2115 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____2115
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2130 =
                                let uu____2131 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2131 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____2130
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____2158 =
                            let uu____2165 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2179  ->
                                     match uu____2179 with
                                     | (t2,q) ->
                                         let uu____2186 = project i x  in
                                         let uu____2187 = project i y  in
                                         mk_stronger t2 uu____2186 uu____2187)
                                args
                               in
                            match uu____2165 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____2158 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2214);
                                      FStar_Syntax_Syntax.pos = uu____2215;
                                      FStar_Syntax_Syntax.vars = uu____2216;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2258  ->
                                   match uu____2258 with
                                   | (bv,q) ->
                                       let uu____2265 =
                                         let uu____2266 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2266  in
                                       FStar_Syntax_Syntax.gen_bv uu____2265
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2273 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2273) bvs
                             in
                          let body =
                            let uu____2275 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2276 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2275 uu____2276  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2283);
                                      FStar_Syntax_Syntax.pos = uu____2284;
                                      FStar_Syntax_Syntax.vars = uu____2285;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2327  ->
                                   match uu____2327 with
                                   | (bv,q) ->
                                       let uu____2334 =
                                         let uu____2335 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2335  in
                                       FStar_Syntax_Syntax.gen_bv uu____2334
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2342 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2342) bvs
                             in
                          let body =
                            let uu____2344 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2345 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2344 uu____2345  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2350 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____2352 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____2353 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____2354 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____2352 uu____2353 uu____2354  in
                    let uu____2355 =
                      let uu____2356 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____2356  in
                    FStar_Syntax_Util.abs uu____2355 body ret_tot_type  in
                  let stronger1 =
                    let uu____2384 = mk_lid "stronger"  in
                    register env1 uu____2384 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2390 = FStar_Util.prefix gamma  in
                    match uu____2390 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____2435 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2435
                             in
                          let uu____2438 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____2438 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2448 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____2448  in
                              let guard_free1 =
                                let uu____2458 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____2458  in
                              let pat =
                                let uu____2462 =
                                  let uu____2471 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____2471]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2462
                                 in
                              let pattern_guarded_body =
                                let uu____2475 =
                                  let uu____2476 =
                                    let uu____2483 =
                                      let uu____2484 =
                                        let uu____2495 =
                                          let uu____2498 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____2498]  in
                                        [uu____2495]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2484
                                       in
                                    (body, uu____2483)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____2476  in
                                mk1 uu____2475  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2503 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____2507 =
                            let uu____2508 =
                              let uu____2509 =
                                let uu____2510 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____2513 =
                                  let uu____2522 = args_of_binders1 wp_args
                                     in
                                  let uu____2525 =
                                    let uu____2528 =
                                      let uu____2529 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____2529
                                       in
                                    [uu____2528]  in
                                  FStar_List.append uu____2522 uu____2525  in
                                FStar_Syntax_Util.mk_app uu____2510
                                  uu____2513
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2509  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2508
                             in
                          FStar_Syntax_Util.abs gamma uu____2507
                            ret_gtot_type
                           in
                        let uu____2530 =
                          let uu____2531 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____2531  in
                        FStar_Syntax_Util.abs uu____2530 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____2543 = mk_lid "wp_ite"  in
                    register env1 uu____2543 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2549 = FStar_Util.prefix gamma  in
                    match uu____2549 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____2592 =
                            let uu____2593 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____2596 =
                              let uu____2605 =
                                let uu____2606 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____2606  in
                              [uu____2605]  in
                            FStar_Syntax_Util.mk_app uu____2593 uu____2596
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2592
                           in
                        let uu____2607 =
                          let uu____2608 =
                            let uu____2615 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____2615 gamma  in
                          FStar_List.append binders uu____2608  in
                        FStar_Syntax_Util.abs uu____2607 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____2631 = mk_lid "null_wp"  in
                    register env1 uu____2631 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____2640 =
                        let uu____2649 =
                          let uu____2652 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____2653 =
                            let uu____2656 =
                              let uu____2659 =
                                let uu____2668 =
                                  let uu____2669 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____2669  in
                                [uu____2668]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2659
                               in
                            let uu____2670 =
                              let uu____2675 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____2675]  in
                            uu____2656 :: uu____2670  in
                          uu____2652 :: uu____2653  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2649
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____2640  in
                    let uu____2678 =
                      let uu____2679 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____2679  in
                    FStar_Syntax_Util.abs uu____2678 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____2691 = mk_lid "wp_trivial"  in
                    register env1 uu____2691 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____2696 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____2696
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____2701 =
                      let uu____2704 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____2704  in
                    let uu____2752 =
                      let uu___77_2753 = ed  in
                      let uu____2754 =
                        let uu____2755 = c wp_if_then_else2  in
                        ([], uu____2755)  in
                      let uu____2758 =
                        let uu____2759 = c wp_ite2  in ([], uu____2759)  in
                      let uu____2762 =
                        let uu____2763 = c stronger2  in ([], uu____2763)  in
                      let uu____2766 =
                        let uu____2767 = c wp_close2  in ([], uu____2767)  in
                      let uu____2770 =
                        let uu____2771 = c wp_assert2  in ([], uu____2771)
                         in
                      let uu____2774 =
                        let uu____2775 = c wp_assume2  in ([], uu____2775)
                         in
                      let uu____2778 =
                        let uu____2779 = c null_wp2  in ([], uu____2779)  in
                      let uu____2782 =
                        let uu____2783 = c wp_trivial2  in ([], uu____2783)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___77_2753.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___77_2753.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___77_2753.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___77_2753.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___77_2753.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___77_2753.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___77_2753.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2754;
                        FStar_Syntax_Syntax.ite_wp = uu____2758;
                        FStar_Syntax_Syntax.stronger = uu____2762;
                        FStar_Syntax_Syntax.close_wp = uu____2766;
                        FStar_Syntax_Syntax.assert_p = uu____2770;
                        FStar_Syntax_Syntax.assume_p = uu____2774;
                        FStar_Syntax_Syntax.null_wp = uu____2778;
                        FStar_Syntax_Syntax.trivial = uu____2782;
                        FStar_Syntax_Syntax.repr =
                          (uu___77_2753.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___77_2753.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___77_2753.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___77_2753.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___77_2753.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____2701, uu____2752)))))
  
type env_ = env[@@deriving show]
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___78_2797 = dmff_env  in
      {
        env = env';
        subst = (uu___78_2797.subst);
        tc_const = (uu___78_2797.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____2810 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____2822 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm[@@deriving show]
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___64_2832  ->
    match uu___64_2832 with
    | FStar_Syntax_Syntax.Total (t,uu____2834) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___63_2847  ->
                match uu___63_2847 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2848 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2850 =
          let uu____2851 =
            let uu____2852 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2852
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2851  in
        failwith uu____2850
    | FStar_Syntax_Syntax.GTotal uu____2853 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___65_2864  ->
    match uu___65_2864 with
    | N t ->
        let uu____2866 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____2866
    | M t ->
        let uu____2868 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____2868
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2872,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2874;
                      FStar_Syntax_Syntax.vars = uu____2875;_})
        -> nm_of_comp n2
    | uu____2896 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____2904 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____2904 with | M uu____2905 -> true | N uu____2906 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2910 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____2920 =
        let uu____2927 =
          let uu____2928 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2928  in
        [uu____2927]  in
      let uu____2929 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____2920 uu____2929  in
    let uu____2932 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____2932
  
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        mk1
          (let uu____2969 =
             let uu____2982 =
               let uu____2989 =
                 let uu____2994 =
                   let uu____2995 = star_type' env a  in
                   FStar_Syntax_Syntax.null_bv uu____2995  in
                 let uu____2996 = FStar_Syntax_Syntax.as_implicit false  in
                 (uu____2994, uu____2996)  in
               [uu____2989]  in
             let uu____3005 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
             (uu____2982, uu____3005)  in
           FStar_Syntax_Syntax.Tm_arrow uu____2969)

and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
         in
      let mk_star_to_type1 = mk_star_to_type mk1  in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3033) ->
          let binders1 =
            FStar_List.map
              (fun uu____3069  ->
                 match uu____3069 with
                 | (bv,aqual) ->
                     let uu____3080 =
                       let uu___79_3081 = bv  in
                       let uu____3082 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___79_3081.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___79_3081.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3082
                       }  in
                     (uu____3080, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3085,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3087);
                             FStar_Syntax_Syntax.pos = uu____3088;
                             FStar_Syntax_Syntax.vars = uu____3089;_})
               ->
               let uu____3118 =
                 let uu____3119 =
                   let uu____3132 =
                     let uu____3133 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3133  in
                   (binders1, uu____3132)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3119  in
               mk1 uu____3118
           | uu____3140 ->
               let uu____3141 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3141 with
                | N hn ->
                    let uu____3143 =
                      let uu____3144 =
                        let uu____3157 =
                          let uu____3158 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3158  in
                        (binders1, uu____3157)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3144  in
                    mk1 uu____3143
                | M a ->
                    let uu____3166 =
                      let uu____3167 =
                        let uu____3180 =
                          let uu____3187 =
                            let uu____3194 =
                              let uu____3199 =
                                let uu____3200 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____3200  in
                              let uu____3201 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____3199, uu____3201)  in
                            [uu____3194]  in
                          FStar_List.append binders1 uu____3187  in
                        let uu____3214 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____3180, uu____3214)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3167  in
                    mk1 uu____3166))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3284 = f x  in
                    FStar_Util.string_builder_append strb uu____3284);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3291 = f x1  in
                         FStar_Util.string_builder_append strb uu____3291))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____3293 =
              let uu____3298 =
                let uu____3299 = FStar_Syntax_Print.term_to_string t2  in
                let uu____3300 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3299 uu____3300
                 in
              (FStar_Errors.Warning_DependencyFound, uu____3298)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3293  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3308 =
              let uu____3309 = FStar_Syntax_Subst.compress ty  in
              uu____3309.FStar_Syntax_Syntax.n  in
            match uu____3308 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3330 =
                  let uu____3331 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____3331  in
                if uu____3330
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3357 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____3357 s  in
                       let uu____3360 =
                         let uu____3361 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____3361  in
                       if uu____3360
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____3364 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____3364 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3386  ->
                                  match uu____3386 with
                                  | (bv,uu____3396) ->
                                      (non_dependent_or_raise s
                                         bv.FStar_Syntax_Syntax.sort;
                                       FStar_Util.set_add bv s))
                             FStar_Syntax_Syntax.no_names binders1
                            in
                         let ct = FStar_Syntax_Util.comp_result c1  in
                         (non_dependent_or_raise s ct;
                          (let k = n1 - (FStar_List.length binders1)  in
                           if k > (Prims.parse_int "0")
                           then is_non_dependent_arrow ct k
                           else true))
                   with | Not_found  -> false)
            | uu____3410 ->
                ((let uu____3412 =
                    let uu____3417 =
                      let uu____3418 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3418
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3417)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3412);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____3423 =
              let uu____3424 = FStar_Syntax_Subst.compress head2  in
              uu____3424.FStar_Syntax_Syntax.n  in
            match uu____3423 with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                (((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.option_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.either_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq2_lid))
                  ||
                  (let uu____3429 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____3429)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3431 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____3431 with
                 | ((uu____3440,ty),uu____3442) ->
                     let uu____3447 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____3447
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1
                          in
                       let uu____3455 =
                         let uu____3456 = FStar_Syntax_Subst.compress res  in
                         uu____3456.FStar_Syntax_Syntax.n  in
                       (match uu____3455 with
                        | FStar_Syntax_Syntax.Tm_app uu____3459 -> true
                        | uu____3474 ->
                            ((let uu____3476 =
                                let uu____3481 =
                                  let uu____3482 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3482
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3481)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3476);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3484 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3485 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3487) ->
                is_valid_application t2
            | uu____3492 -> false  in
          let uu____3493 = is_valid_application head1  in
          if uu____3493
          then
            let uu____3494 =
              let uu____3495 =
                let uu____3510 =
                  FStar_List.map
                    (fun uu____3531  ->
                       match uu____3531 with
                       | (t2,qual) ->
                           let uu____3548 = star_type' env t2  in
                           (uu____3548, qual)) args
                   in
                (head1, uu____3510)  in
              FStar_Syntax_Syntax.Tm_app uu____3495  in
            mk1 uu____3494
          else
            (let uu____3558 =
               let uu____3563 =
                 let uu____3564 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3564
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____3563)  in
             FStar_Errors.raise_err uu____3558)
      | FStar_Syntax_Syntax.Tm_bvar uu____3565 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3566 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3567 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3568 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3592 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____3592 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___82_3600 = env  in
                 let uu____3601 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____3601;
                   subst = (uu___82_3600.subst);
                   tc_const = (uu___82_3600.tc_const)
                 }  in
               let repr2 = star_type' env1 repr1  in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort  in
          let subst1 = [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x1)]
             in
          let t3 = FStar_Syntax_Subst.subst subst1 t2  in
          let t4 = star_type' env t3  in
          let subst2 = [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))]
             in
          let t5 = FStar_Syntax_Subst.subst subst2 t4  in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___83_3621 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___83_3621.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___83_3621.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3628 =
            let uu____3629 =
              let uu____3636 = star_type' env t2  in (uu____3636, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____3629  in
          mk1 uu____3628
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3684 =
            let uu____3685 =
              let uu____3712 = star_type' env e  in
              let uu____3713 =
                let uu____3728 =
                  let uu____3735 = star_type' env t2  in
                  FStar_Util.Inl uu____3735  in
                (uu____3728, FStar_Pervasives_Native.None)  in
              (uu____3712, uu____3713, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3685  in
          mk1 uu____3684
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3813 =
            let uu____3814 =
              let uu____3841 = star_type' env e  in
              let uu____3842 =
                let uu____3857 =
                  let uu____3864 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____3864  in
                (uu____3857, FStar_Pervasives_Native.None)  in
              (uu____3841, uu____3842, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3814  in
          mk1 uu____3813
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____3895,(uu____3896,FStar_Pervasives_Native.Some uu____3897),uu____3898)
          ->
          let uu____3947 =
            let uu____3952 =
              let uu____3953 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____3953
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3952)  in
          FStar_Errors.raise_err uu____3947
      | FStar_Syntax_Syntax.Tm_refine uu____3954 ->
          let uu____3961 =
            let uu____3966 =
              let uu____3967 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____3967
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3966)  in
          FStar_Errors.raise_err uu____3961
      | FStar_Syntax_Syntax.Tm_uinst uu____3968 ->
          let uu____3975 =
            let uu____3980 =
              let uu____3981 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____3981
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3980)  in
          FStar_Errors.raise_err uu____3975
      | FStar_Syntax_Syntax.Tm_constant uu____3982 ->
          let uu____3983 =
            let uu____3988 =
              let uu____3989 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____3989
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3988)  in
          FStar_Errors.raise_err uu____3983
      | FStar_Syntax_Syntax.Tm_match uu____3990 ->
          let uu____4013 =
            let uu____4018 =
              let uu____4019 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4019
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4018)  in
          FStar_Errors.raise_err uu____4013
      | FStar_Syntax_Syntax.Tm_let uu____4020 ->
          let uu____4033 =
            let uu____4038 =
              let uu____4039 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4039
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4038)  in
          FStar_Errors.raise_err uu____4033
      | FStar_Syntax_Syntax.Tm_uvar uu____4040 ->
          let uu____4057 =
            let uu____4062 =
              let uu____4063 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4063
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4062)  in
          FStar_Errors.raise_err uu____4057
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4064 =
            let uu____4069 =
              let uu____4070 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4070
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4069)  in
          FStar_Errors.raise_err uu____4064
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4072 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____4072
      | FStar_Syntax_Syntax.Tm_delayed uu____4075 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___67_4104  ->
    match uu___67_4104 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___66_4111  ->
                match uu___66_4111 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4112 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____4116 =
      let uu____4117 = FStar_Syntax_Subst.compress t  in
      uu____4117.FStar_Syntax_Syntax.n  in
    match uu____4116 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4143 =
            let uu____4144 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____4144  in
          is_C uu____4143  in
        if r
        then
          ((let uu____4160 =
              let uu____4161 =
                FStar_List.for_all
                  (fun uu____4169  ->
                     match uu____4169 with | (h,uu____4175) -> is_C h) args
                 in
              Prims.op_Negation uu____4161  in
            if uu____4160 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4179 =
              let uu____4180 =
                FStar_List.for_all
                  (fun uu____4189  ->
                     match uu____4189 with
                     | (h,uu____4195) ->
                         let uu____4196 = is_C h  in
                         Prims.op_Negation uu____4196) args
                 in
              Prims.op_Negation uu____4180  in
            if uu____4179 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4216 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____4216 with
         | M t1 ->
             ((let uu____4219 = is_C t1  in
               if uu____4219 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4223) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4229) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4235,uu____4236) -> is_C t1
    | uu____4277 -> false
  
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
           in
        let p_type = mk_star_to_type mk1 env t  in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type
           in
        let body =
          let uu____4300 =
            let uu____4301 =
              let uu____4316 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____4317 =
                let uu____4324 =
                  let uu____4329 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____4329)  in
                [uu____4324]  in
              (uu____4316, uu____4317)  in
            FStar_Syntax_Syntax.Tm_app uu____4301  in
          mk1 uu____4300  in
        let uu____4344 =
          let uu____4345 = FStar_Syntax_Syntax.mk_binder p  in [uu____4345]
           in
        FStar_Syntax_Util.abs uu____4344 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___68_4348  ->
    match uu___68_4348 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4349 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm ->
        (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____4524 =
          match uu____4524 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4551 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4553 =
                       let uu____4554 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____4554  in
                     Prims.op_Negation uu____4553)
                   in
                if uu____4551
                then
                  let uu____4555 =
                    let uu____4560 =
                      let uu____4561 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____4562 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____4563 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4561 uu____4562 uu____4563
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4560)  in
                  FStar_Errors.raise_err uu____4555
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4580 = mk_return env t1 s_e  in
                     ((M t1), uu____4580, u_e)))
               | (M t1,N t2) ->
                   let uu____4583 =
                     let uu____4588 =
                       let uu____4589 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____4590 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____4591 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4589 uu____4590 uu____4591
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4588)
                      in
                   FStar_Errors.raise_err uu____4583)
           in
        let ensure_m env1 e2 =
          let strip_m uu___69_4632 =
            match uu___69_4632 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4648 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____4668 =
                let uu____4673 =
                  let uu____4674 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4674
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____4673)  in
              FStar_Errors.raise_error uu____4668 e2.FStar_Syntax_Syntax.pos
          | M uu____4681 ->
              let uu____4682 = check env1 e2 context_nm  in
              strip_m uu____4682
           in
        let uu____4689 =
          let uu____4690 = FStar_Syntax_Subst.compress e  in
          uu____4690.FStar_Syntax_Syntax.n  in
        match uu____4689 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4699 ->
            let uu____4700 = infer env e  in return_if uu____4700
        | FStar_Syntax_Syntax.Tm_name uu____4707 ->
            let uu____4708 = infer env e  in return_if uu____4708
        | FStar_Syntax_Syntax.Tm_fvar uu____4715 ->
            let uu____4716 = infer env e  in return_if uu____4716
        | FStar_Syntax_Syntax.Tm_abs uu____4723 ->
            let uu____4740 = infer env e  in return_if uu____4740
        | FStar_Syntax_Syntax.Tm_constant uu____4747 ->
            let uu____4748 = infer env e  in return_if uu____4748
        | FStar_Syntax_Syntax.Tm_app uu____4755 ->
            let uu____4770 = infer env e  in return_if uu____4770
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____4778 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____4778 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4840) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4846) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4852,uu____4853) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____4894 ->
            let uu____4907 =
              let uu____4908 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____4908  in
            failwith uu____4907
        | FStar_Syntax_Syntax.Tm_type uu____4915 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____4922 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____4941 ->
            let uu____4948 =
              let uu____4949 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____4949  in
            failwith uu____4948
        | FStar_Syntax_Syntax.Tm_uvar uu____4956 ->
            let uu____4973 =
              let uu____4974 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____4974  in
            failwith uu____4973
        | FStar_Syntax_Syntax.Tm_delayed uu____4981 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____5012 =
              let uu____5013 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5013  in
            failwith uu____5012

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos
         in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env
         in
      let uu____5037 =
        let uu____5038 = FStar_Syntax_Subst.compress e  in
        uu____5038.FStar_Syntax_Syntax.n  in
      match uu____5037 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5056 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____5056
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5099;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5100;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5106 =
                  let uu___84_5107 = rc  in
                  let uu____5108 =
                    let uu____5113 =
                      let uu____5114 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____5114  in
                    FStar_Pervasives_Native.Some uu____5113  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___84_5107.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5108;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___84_5107.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____5106
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___85_5124 = env  in
            let uu____5125 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____5125;
              subst = (uu___85_5124.subst);
              tc_const = (uu___85_5124.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____5145  ->
                 match uu____5145 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___86_5158 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___86_5158.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___86_5158.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____5159 =
            FStar_List.fold_left
              (fun uu____5188  ->
                 fun uu____5189  ->
                   match (uu____5188, uu____5189) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____5237 = is_C c  in
                       if uu____5237
                       then
                         let xw =
                           let uu____5245 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5245
                            in
                         let x =
                           let uu___87_5247 = bv  in
                           let uu____5248 =
                             let uu____5251 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____5251  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___87_5247.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___87_5247.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5248
                           }  in
                         let env3 =
                           let uu___88_5253 = env2  in
                           let uu____5254 =
                             let uu____5257 =
                               let uu____5258 =
                                 let uu____5265 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____5265)  in
                               FStar_Syntax_Syntax.NT uu____5258  in
                             uu____5257 :: (env2.subst)  in
                           {
                             env = (uu___88_5253.env);
                             subst = uu____5254;
                             tc_const = (uu___88_5253.tc_const)
                           }  in
                         let uu____5266 =
                           let uu____5269 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____5270 =
                             let uu____5273 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____5273 :: acc  in
                           uu____5269 :: uu____5270  in
                         (env3, uu____5266)
                       else
                         (let x =
                            let uu___89_5278 = bv  in
                            let uu____5279 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___89_5278.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___89_5278.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5279
                            }  in
                          let uu____5282 =
                            let uu____5285 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____5285 :: acc  in
                          (env2, uu____5282))) (env1, []) binders1
             in
          (match uu____5159 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____5305 =
                 let check_what =
                   let uu____5323 = is_monadic rc_opt1  in
                   if uu____5323 then check_m else check_n  in
                 let uu____5335 = check_what env2 body1  in
                 match uu____5335 with
                 | (t,s_body,u_body) ->
                     let uu____5351 =
                       let uu____5352 =
                         let uu____5353 = is_monadic rc_opt1  in
                         if uu____5353 then M t else N t  in
                       comp_of_nm uu____5352  in
                     (uu____5351, s_body, u_body)
                  in
               (match uu____5305 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp  in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None  ->
                               let rc1 =
                                 let uu____5378 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___70_5382  ->
                                           match uu___70_5382 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5383 -> false))
                                    in
                                 if uu____5378
                                 then
                                   let uu____5384 =
                                     FStar_List.filter
                                       (fun uu___71_5388  ->
                                          match uu___71_5388 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5389 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5384
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5398 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___72_5402  ->
                                         match uu___72_5402 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5403 -> false))
                                  in
                               if uu____5398
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___73_5410  ->
                                        match uu___73_5410 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5411 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____5412 =
                                   let uu____5413 =
                                     let uu____5418 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____5418
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5413 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____5412
                               else
                                 (let uu____5420 =
                                    let uu___90_5421 = rc  in
                                    let uu____5422 =
                                      let uu____5427 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____5427
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___90_5421.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5422;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___90_5421.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____5420))
                       in
                    let uu____5428 =
                      let comp1 =
                        let uu____5438 = is_monadic rc_opt1  in
                        let uu____5439 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5438 uu____5439
                         in
                      let uu____5440 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____5440,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____5428 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____5482 =
                             let uu____5483 =
                               let uu____5500 =
                                 let uu____5503 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____5503 s_rc_opt  in
                               (s_binders1, s_body1, uu____5500)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5483  in
                           mk1 uu____5482  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____5513 =
                             let uu____5514 =
                               let uu____5531 =
                                 let uu____5534 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____5534 u_rc_opt  in
                               (u_binders2, u_body2, uu____5531)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5514  in
                           mk1 uu____5513  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5544;_};
            FStar_Syntax_Syntax.fv_delta = uu____5545;
            FStar_Syntax_Syntax.fv_qual = uu____5546;_}
          ->
          let uu____5549 =
            let uu____5554 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5554  in
          (match uu____5549 with
           | (uu____5585,t) ->
               let uu____5587 =
                 let uu____5588 = normalize1 t  in N uu____5588  in
               (uu____5587, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5589;
             FStar_Syntax_Syntax.vars = uu____5590;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5657 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5657 with
           | (unary_op,uu____5679) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5738;
             FStar_Syntax_Syntax.vars = uu____5739;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5819 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5819 with
           | (unary_op,uu____5841) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5906;
             FStar_Syntax_Syntax.vars = uu____5907;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____5949 = infer env a  in
          (match uu____5949 with
           | (t,s,u) ->
               let uu____5965 = FStar_Syntax_Util.head_and_args e  in
               (match uu____5965 with
                | (head1,uu____5987) ->
                    let uu____6008 =
                      let uu____6009 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____6009  in
                    let uu____6010 =
                      let uu____6013 =
                        let uu____6014 =
                          let uu____6029 =
                            let uu____6032 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6032]  in
                          (head1, uu____6029)  in
                        FStar_Syntax_Syntax.Tm_app uu____6014  in
                      mk1 uu____6013  in
                    let uu____6037 =
                      let uu____6040 =
                        let uu____6041 =
                          let uu____6056 =
                            let uu____6059 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6059]  in
                          (head1, uu____6056)  in
                        FStar_Syntax_Syntax.Tm_app uu____6041  in
                      mk1 uu____6040  in
                    (uu____6008, uu____6010, uu____6037)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6068;
             FStar_Syntax_Syntax.vars = uu____6069;_},(a1,uu____6071)::a2::[])
          ->
          let uu____6117 = infer env a1  in
          (match uu____6117 with
           | (t,s,u) ->
               let uu____6133 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6133 with
                | (head1,uu____6155) ->
                    let uu____6176 =
                      let uu____6179 =
                        let uu____6180 =
                          let uu____6195 =
                            let uu____6198 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6198; a2]  in
                          (head1, uu____6195)  in
                        FStar_Syntax_Syntax.Tm_app uu____6180  in
                      mk1 uu____6179  in
                    let uu____6215 =
                      let uu____6218 =
                        let uu____6219 =
                          let uu____6234 =
                            let uu____6237 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6237; a2]  in
                          (head1, uu____6234)  in
                        FStar_Syntax_Syntax.Tm_app uu____6219  in
                      mk1 uu____6218  in
                    (t, uu____6176, uu____6215)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6258;
             FStar_Syntax_Syntax.vars = uu____6259;_},uu____6260)
          ->
          let uu____6285 =
            let uu____6290 =
              let uu____6291 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6291
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6290)  in
          FStar_Errors.raise_error uu____6285 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6298;
             FStar_Syntax_Syntax.vars = uu____6299;_},uu____6300)
          ->
          let uu____6325 =
            let uu____6330 =
              let uu____6331 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6331
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6330)  in
          FStar_Errors.raise_error uu____6325 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6360 = check_n env head1  in
          (match uu____6360 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6380 =
                   let uu____6381 = FStar_Syntax_Subst.compress t  in
                   uu____6381.FStar_Syntax_Syntax.n  in
                 match uu____6380 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6384 -> true
                 | uu____6397 -> false  in
               let rec flatten1 t =
                 let uu____6414 =
                   let uu____6415 = FStar_Syntax_Subst.compress t  in
                   uu____6415.FStar_Syntax_Syntax.n  in
                 match uu____6414 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6432);
                                FStar_Syntax_Syntax.pos = uu____6433;
                                FStar_Syntax_Syntax.vars = uu____6434;_})
                     when is_arrow t1 ->
                     let uu____6463 = flatten1 t1  in
                     (match uu____6463 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6545,uu____6546)
                     -> flatten1 e1
                 | uu____6587 ->
                     let uu____6588 =
                       let uu____6593 =
                         let uu____6594 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6594
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____6593)  in
                     FStar_Errors.raise_err uu____6588
                  in
               let uu____6607 = flatten1 t_head  in
               (match uu____6607 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6667 =
                          let uu____6672 =
                            let uu____6673 = FStar_Util.string_of_int n1  in
                            let uu____6680 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____6691 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6673 uu____6680 uu____6691
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____6672)
                           in
                        FStar_Errors.raise_err uu____6667)
                     else ();
                     (let uu____6699 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____6699 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6740 args1 =
                            match uu____6740 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____6814 =
                                       let uu____6815 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____6815.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____6814
                                 | (binders3,[]) ->
                                     let uu____6845 =
                                       let uu____6846 =
                                         let uu____6849 =
                                           let uu____6850 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6850
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____6849
                                          in
                                       uu____6846.FStar_Syntax_Syntax.n  in
                                     (match uu____6845 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____6875 =
                                            let uu____6876 =
                                              let uu____6877 =
                                                let uu____6890 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____6890)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____6877
                                               in
                                            mk1 uu____6876  in
                                          N uu____6875
                                      | uu____6897 -> failwith "wat?")
                                 | ([],uu____6898::uu____6899) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____6939)::binders3,(arg,uu____6942)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____6995 = FStar_List.splitAt n' binders1  in
                          (match uu____6995 with
                           | (binders2,uu____7027) ->
                               let uu____7052 =
                                 let uu____7073 =
                                   FStar_List.map2
                                     (fun uu____7127  ->
                                        fun uu____7128  ->
                                          match (uu____7127, uu____7128) with
                                          | ((bv,uu____7166),(arg,q)) ->
                                              let uu____7183 =
                                                let uu____7184 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____7184.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____7183 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7203 ->
                                                   let uu____7204 =
                                                     let uu____7209 =
                                                       star_type' env arg  in
                                                     (uu____7209, q)  in
                                                   (uu____7204, [(arg, q)])
                                               | uu____7236 ->
                                                   let uu____7237 =
                                                     check_n env arg  in
                                                   (match uu____7237 with
                                                    | (uu____7260,s_arg,u_arg)
                                                        ->
                                                        let uu____7263 =
                                                          let uu____7270 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____7270
                                                          then
                                                            let uu____7277 =
                                                              let uu____7282
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____7282, q)
                                                               in
                                                            [uu____7277;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____7263))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____7073  in
                               (match uu____7052 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____7381 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____7390 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____7381, uu____7390)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7458) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7464) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7470,uu____7471) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7513 = let uu____7514 = env.tc_const c  in N uu____7514
             in
          (uu____7513, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7515 ->
          let uu____7528 =
            let uu____7529 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7529  in
          failwith uu____7528
      | FStar_Syntax_Syntax.Tm_type uu____7536 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7543 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7562 ->
          let uu____7569 =
            let uu____7570 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7570  in
          failwith uu____7569
      | FStar_Syntax_Syntax.Tm_uvar uu____7577 ->
          let uu____7594 =
            let uu____7595 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7595  in
          failwith uu____7594
      | FStar_Syntax_Syntax.Tm_delayed uu____7602 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7633 =
            let uu____7634 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7634  in
          failwith uu____7633

and (mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____7679 = check_n env e0  in
          match uu____7679 with
          | (uu____7692,s_e0,u_e0) ->
              let uu____7695 =
                let uu____7724 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7785 = FStar_Syntax_Subst.open_branch b  in
                       match uu____7785 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___91_7827 = env  in
                             let uu____7828 =
                               let uu____7829 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7829
                                in
                             {
                               env = uu____7828;
                               subst = (uu___91_7827.subst);
                               tc_const = (uu___91_7827.tc_const)
                             }  in
                           let uu____7832 = f env1 body  in
                           (match uu____7832 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____7904 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____7724  in
              (match uu____7695 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____8006 = FStar_List.hd nms  in
                     match uu____8006 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___74_8012  ->
                          match uu___74_8012 with
                          | M uu____8013 -> true
                          | uu____8014 -> false) nms
                      in
                   let uu____8015 =
                     let uu____8052 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8142  ->
                              match uu____8142 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8319 =
                                         check env original_body (M t2)  in
                                       (match uu____8319 with
                                        | (uu____8356,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8395,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____8052  in
                   (match uu____8015 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____8579  ->
                                 match uu____8579 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8630 =
                                         let uu____8631 =
                                           let uu____8646 =
                                             let uu____8653 =
                                               let uu____8658 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____8659 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____8658, uu____8659)  in
                                             [uu____8653]  in
                                           (s_body, uu____8646)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8631
                                          in
                                       mk1 uu____8630  in
                                     (pat, guard, s_body1)) s_branches
                             in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1
                             in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches
                             in
                          let s_e =
                            let uu____8691 =
                              let uu____8692 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____8692]  in
                            let uu____8693 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____8691 uu____8693
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____8699 =
                              let uu____8706 =
                                let uu____8707 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8707
                                 in
                              [uu____8706]  in
                            let uu____8708 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____8699 uu____8708  in
                          let uu____8711 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____8750 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____8711, uu____8750)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches
                              in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches
                              in
                           let t1_star = t1  in
                           let uu____8767 =
                             let uu____8770 =
                               let uu____8771 =
                                 let uu____8798 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____8798,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8771  in
                             mk1 uu____8770  in
                           let uu____8835 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____8767, uu____8835))))

and (mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
                 FStar_Pervasives_Native.tuple3)
            ->
            (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                e2.FStar_Syntax_Syntax.pos
               in
            let e1 = binding.FStar_Syntax_Syntax.lbdef  in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname  in
            let x_binders =
              let uu____8882 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____8882]  in
            let uu____8883 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____8883 with
            | (x_binders1,e21) ->
                let uu____8896 = infer env e1  in
                (match uu____8896 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____8913 = is_C t1  in
                       if uu____8913
                       then
                         let uu___92_8914 = binding  in
                         let uu____8915 =
                           let uu____8918 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____8918  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___92_8914.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___92_8914.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____8915;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___92_8914.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___92_8914.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___92_8914.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___92_8914.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___93_8921 = env  in
                       let uu____8922 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___94_8924 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___94_8924.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___94_8924.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____8922;
                         subst = (uu___93_8921.subst);
                         tc_const = (uu___93_8921.tc_const)
                       }  in
                     let uu____8925 = proceed env1 e21  in
                     (match uu____8925 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___95_8942 = binding  in
                            let uu____8943 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___95_8942.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___95_8942.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____8943;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___95_8942.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___95_8942.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___95_8942.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___95_8942.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____8946 =
                            let uu____8949 =
                              let uu____8950 =
                                let uu____8963 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___96_8973 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___96_8973.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___96_8973.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___96_8973.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___96_8973.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___96_8973.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___96_8973.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____8963)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____8950  in
                            mk1 uu____8949  in
                          let uu____8974 =
                            let uu____8977 =
                              let uu____8978 =
                                let uu____8991 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___97_9001 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___97_9001.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___97_9001.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___97_9001.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___97_9001.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___97_9001.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___97_9001.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____8991)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____8978  in
                            mk1 uu____8977  in
                          (nm_rec, uu____8946, uu____8974))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___98_9010 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___98_9010.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___98_9010.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___98_9010.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___98_9010.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___98_9010.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___99_9012 = env  in
                       let uu____9013 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___100_9015 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___100_9015.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___100_9015.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9013;
                         subst = (uu___99_9012.subst);
                         tc_const = (uu___99_9012.tc_const)
                       }  in
                     let uu____9016 = ensure_m env1 e21  in
                     (match uu____9016 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____9039 =
                              let uu____9040 =
                                let uu____9055 =
                                  let uu____9062 =
                                    let uu____9067 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____9068 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9067, uu____9068)  in
                                  [uu____9062]  in
                                (s_e2, uu____9055)  in
                              FStar_Syntax_Syntax.Tm_app uu____9040  in
                            mk1 uu____9039  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____9087 =
                              let uu____9088 =
                                let uu____9103 =
                                  let uu____9110 =
                                    let uu____9115 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____9115)  in
                                  [uu____9110]  in
                                (s_e1, uu____9103)  in
                              FStar_Syntax_Syntax.Tm_app uu____9088  in
                            mk1 uu____9087  in
                          let uu____9130 =
                            let uu____9131 =
                              let uu____9132 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____9132]  in
                            FStar_Syntax_Util.abs uu____9131 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____9133 =
                            let uu____9136 =
                              let uu____9137 =
                                let uu____9150 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___101_9160 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___101_9160.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___101_9160.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___101_9160.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___101_9160.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___101_9160.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___101_9160.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9150)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9137  in
                            mk1 uu____9136  in
                          ((M t2), uu____9130, uu____9133)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9172 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____9172  in
      let uu____9173 = check env e mn  in
      match uu____9173 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9189 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9211 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____9211  in
      let uu____9212 = check env e mn  in
      match uu____9212 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9228 -> failwith "[check_m]: impossible"

and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and (mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp) =
  fun t  ->
    FStar_Syntax_Syntax.mk_Comp
      {
        FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
        FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.monadic_lid;
        FStar_Syntax_Syntax.result_typ = t;
        FStar_Syntax_Syntax.effect_args = [];
        FStar_Syntax_Syntax.flags =
          [FStar_Syntax_Syntax.CPS; FStar_Syntax_Syntax.TOTAL]
      }

and (type_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun t  -> FStar_Syntax_Util.comp_result t

and (trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____9258 =
           let uu____9259 = is_C c  in Prims.op_Negation uu____9259  in
         if uu____9258 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____9267 =
           let uu____9268 = FStar_Syntax_Subst.compress c  in
           uu____9268.FStar_Syntax_Syntax.n  in
         match uu____9267 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9293 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____9293 with
              | (wp_head,wp_args) ->
                  ((let uu____9331 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9345 =
                           let uu____9346 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9346
                            in
                         Prims.op_Negation uu____9345)
                       in
                    if uu____9331 then failwith "mismatch" else ());
                   (let uu____9354 =
                      let uu____9355 =
                        let uu____9370 =
                          FStar_List.map2
                            (fun uu____9398  ->
                               fun uu____9399  ->
                                 match (uu____9398, uu____9399) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9436 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____9436
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____9439 =
                                           let uu____9444 =
                                             let uu____9445 =
                                               print_implicit q  in
                                             let uu____9446 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %b %b\n"
                                               uu____9445 uu____9446
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____9444)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____9439)
                                      else ();
                                      (let uu____9448 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____9448, q)))) args wp_args
                           in
                        (head1, uu____9370)  in
                      FStar_Syntax_Syntax.Tm_app uu____9355  in
                    mk1 uu____9354)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____9482 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____9482 with
              | (binders_orig,comp1) ->
                  let uu____9489 =
                    let uu____9504 =
                      FStar_List.map
                        (fun uu____9538  ->
                           match uu____9538 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____9558 = is_C h  in
                               if uu____9558
                               then
                                 let w' =
                                   let uu____9570 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9570
                                    in
                                 let uu____9571 =
                                   let uu____9578 =
                                     let uu____9585 =
                                       let uu____9590 =
                                         let uu____9591 =
                                           let uu____9592 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____9592  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9591
                                          in
                                       (uu____9590, q)  in
                                     [uu____9585]  in
                                   (w', q) :: uu____9578  in
                                 (w', uu____9571)
                               else
                                 (let x =
                                    let uu____9613 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9613
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____9504  in
                  (match uu____9489 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____9668 =
                           let uu____9671 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9671
                            in
                         FStar_Syntax_Subst.subst_comp uu____9668 comp1  in
                       let app =
                         let uu____9675 =
                           let uu____9676 =
                             let uu____9691 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9706 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____9707 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9706, uu____9707)) bvs
                                in
                             (wp, uu____9691)  in
                           FStar_Syntax_Syntax.Tm_app uu____9676  in
                         mk1 uu____9675  in
                       let comp3 =
                         let uu____9715 = type_of_comp comp2  in
                         let uu____9716 = is_monadic_comp comp2  in
                         trans_G env uu____9715 uu____9716 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9718,uu____9719) ->
             trans_F_ env e wp
         | uu____9760 -> failwith "impossible trans_F_")

and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          if is_monadic1
          then
            let uu____9765 =
              let uu____9766 = star_type' env h  in
              let uu____9769 =
                let uu____9778 =
                  let uu____9783 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____9783)  in
                [uu____9778]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9766;
                FStar_Syntax_Syntax.effect_args = uu____9769;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____9765
          else
            (let uu____9793 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____9793)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.Delta_constant;
    FStar_TypeChecker_Normalize.NoDeltaSteps;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____9804 = n env.env t  in star_type' env uu____9804
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____9819 = n env.env t  in check_n env uu____9819
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____9829 = n env.env c  in
        let uu____9830 = n env.env wp  in trans_F_ env uu____9829 uu____9830
  