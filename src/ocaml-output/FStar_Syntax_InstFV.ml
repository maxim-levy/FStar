open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list
let mk :
  'Auu____15 'Auu____16 .
    'Auu____15 FStar_Syntax_Syntax.syntax ->
      'Auu____16 -> 'Auu____16 FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      FStar_Syntax_Syntax.mk s FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
  
let rec (inst :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let mk1 = mk t1  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____141 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____164 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____165 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____178 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____191 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____192 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____193 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____194 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____201 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____208 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____235 =
            let uu____236 =
              let uu____253 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____253)  in
            FStar_Syntax_Syntax.Tm_abs uu____236  in
          mk1 uu____235
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___92_303 = bv  in
            let uu____304 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___92_303.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___92_303.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____304
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____330 =
            let uu____331 =
              let uu____346 = inst s t2  in
              let uu____347 = inst_args s args  in (uu____346, uu____347)  in
            FStar_Syntax_Syntax.Tm_app uu____331  in
          mk1 uu____330
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____475  ->
                    match uu____475 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____513 = inst s w  in
                              FStar_Pervasives_Native.Some uu____513
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____519 =
            let uu____520 = let uu____543 = inst s t2  in (uu____543, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____520  in
          mk1 uu____519
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____634 =
            match uu____634 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____696 = inst s t2  in FStar_Util.Inl uu____696
                  | FStar_Util.Inr c ->
                      let uu____704 = inst_comp s c  in
                      FStar_Util.Inr uu____704
                   in
                (annot1, topt1)
             in
          let uu____717 =
            let uu____718 =
              let uu____745 = inst s t11  in
              let uu____746 = inst_asc asc  in (uu____745, uu____746, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____718  in
          mk1 uu____717
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____804 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___93_818 = lb  in
                      let uu____819 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____820 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___93_818.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___93_818.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____819;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___93_818.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____820;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___93_818.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___93_818.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____804)  in
          let uu____825 =
            let uu____826 = let uu____839 = inst s t2  in (lbs1, uu____839)
               in
            FStar_Syntax_Syntax.Tm_let uu____826  in
          mk1 uu____825
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____864 =
            let uu____865 =
              let uu____872 = inst s t2  in
              let uu____873 =
                let uu____874 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____874  in
              (uu____872, uu____873)  in
            FStar_Syntax_Syntax.Tm_meta uu____865  in
          mk1 uu____864
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____934 =
            let uu____935 =
              let uu____942 = inst s t2  in
              let uu____943 =
                let uu____944 = let uu____951 = inst s t'  in (m, uu____951)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____944  in
              (uu____942, uu____943)  in
            FStar_Syntax_Syntax.Tm_meta uu____935  in
          mk1 uu____934
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____962 =
            let uu____963 = let uu____970 = inst s t2  in (uu____970, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____963  in
          mk1 uu____962

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____997  ->
              match uu____997 with
              | (x,imp) ->
                  let uu____1008 =
                    let uu___94_1009 = x  in
                    let uu____1010 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___94_1009.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___94_1009.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1010
                    }  in
                  (uu____1008, imp)))

and (inst_args :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1051  ->
              match uu____1051 with
              | (a,imp) -> let uu____1062 = inst s a  in (uu____1062, imp)))

and (inst_comp :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uopt) ->
          let uu____1083 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1083 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1094 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1094 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___95_1097 = ct  in
            let uu____1098 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1099 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1108 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___91_1118  ->
                      match uu___91_1118 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1122 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1122
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___95_1097.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___95_1097.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1098;
              FStar_Syntax_Syntax.effect_args = uu____1099;
              FStar_Syntax_Syntax.flags = uu____1108
            }  in
          FStar_Syntax_Syntax.mk_Comp ct1

and (inst_lcomp_opt :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____1135 =
            let uu___96_1136 = rc  in
            let uu____1137 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___96_1136.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1137;
              FStar_Syntax_Syntax.residual_flags =
                (uu___96_1136.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1135

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1160 ->
          let inst_fv t1 fv =
            let uu____1172 =
              FStar_Util.find_opt
                (fun uu____1186  ->
                   match uu____1186 with
                   | (x,uu____1192) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1172 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1197,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  