open Prims
let (embed_bv :
  FStar_Range.range -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun bv  ->
      FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_binder
        FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some rng)
  
let (embed_binder :
  FStar_Range.range -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun b  ->
      FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder
        FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some rng)
  
let (embed_term :
  FStar_Range.range -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      let qi = { FStar_Syntax_Syntax.qopen = false }  in
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_meta
           (FStar_Syntax_Syntax.tun,
             (FStar_Syntax_Syntax.Meta_quoted (t, qi))))
        FStar_Pervasives_Native.None rng
  
let (embed_aqualv :
  FStar_Range.range ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun q  ->
      let r =
        match q with
        | FStar_Reflection_Data.Q_Explicit  ->
            FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.t
        | FStar_Reflection_Data.Q_Implicit  ->
            FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.t
         in
      let uu___51_39 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___51_39.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___51_39.FStar_Syntax_Syntax.vars)
      }
  
let (embed_binders :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun l  ->
      let uu____49 =
        FStar_Syntax_Embeddings.embed_list embed_binder
          FStar_Reflection_Data.fstar_refl_binder
         in
      uu____49 rng l
  
let (embed_fvar :
  FStar_Range.range -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun fv  ->
      FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv
        FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some rng)
  
let (embed_comp :
  FStar_Range.range -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp
        FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some rng)
  
let (embed_env :
  FStar_Range.range -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun e  ->
      FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env
        FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some rng)
  
let (embed_const :
  FStar_Range.range ->
    FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun c  ->
      let r =
        match c with
        | FStar_Reflection_Data.C_Unit  ->
            FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.t
        | FStar_Reflection_Data.C_True  ->
            FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.t
        | FStar_Reflection_Data.C_False  ->
            FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.t
        | FStar_Reflection_Data.C_Int i ->
            let uu____95 =
              let uu____96 =
                let uu____97 =
                  let uu____98 =
                    let uu____99 = FStar_BigInt.string_of_big_int i  in
                    FStar_Syntax_Util.exp_int uu____99  in
                  FStar_Syntax_Syntax.as_arg uu____98  in
                [uu____97]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t
                uu____96
               in
            uu____95 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Reflection_Data.C_String s ->
            let uu____103 =
              let uu____104 =
                let uu____105 =
                  let uu____106 = FStar_Syntax_Embeddings.embed_string rng s
                     in
                  FStar_Syntax_Syntax.as_arg uu____106  in
                [uu____105]  in
              FStar_Syntax_Syntax.mk_Tm_app
                FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t
                uu____104
               in
            uu____103 FStar_Pervasives_Native.None FStar_Range.dummyRange
         in
      let uu___52_109 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___52_109.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___52_109.FStar_Syntax_Syntax.vars)
      }
  
let rec (embed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedder) =
  fun rng  ->
    fun p  ->
      match p with
      | FStar_Reflection_Data.Pat_Constant c ->
          let uu____118 =
            let uu____119 =
              let uu____120 =
                let uu____121 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____121  in
              [uu____120]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t
              uu____119
             in
          uu____118 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
          let uu____130 =
            let uu____131 =
              let uu____132 =
                let uu____133 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____133  in
              let uu____134 =
                let uu____137 =
                  let uu____138 =
                    let uu____139 =
                      FStar_Syntax_Embeddings.embed_list embed_pattern
                        FStar_Reflection_Data.fstar_refl_pattern
                       in
                    uu____139 rng ps  in
                  FStar_Syntax_Syntax.as_arg uu____138  in
                [uu____137]  in
              uu____132 :: uu____134  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t
              uu____131
             in
          uu____130 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Var bv ->
          let uu____150 =
            let uu____151 =
              let uu____152 =
                let uu____153 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____153  in
              [uu____152]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t
              uu____151
             in
          uu____150 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Pat_Wild bv ->
          let uu____157 =
            let uu____158 =
              let uu____159 =
                let uu____160 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____160  in
              [uu____159]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t
              uu____158
             in
          uu____157 FStar_Pervasives_Native.None rng
  
let (embed_branch :
  FStar_Range.range ->
    FStar_Reflection_Data.branch -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun br  ->
      let uu____172 =
        FStar_Syntax_Embeddings.embed_pair embed_pattern
          FStar_Reflection_Data.fstar_refl_pattern embed_term
          FStar_Syntax_Syntax.t_term
         in
      uu____172 rng br
  
let (embed_argv :
  FStar_Range.range -> FStar_Reflection_Data.argv -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun aq  ->
      let uu____191 =
        FStar_Syntax_Embeddings.embed_pair embed_term
          FStar_Syntax_Syntax.t_term embed_aqualv
          FStar_Reflection_Data.fstar_refl_aqualv
         in
      uu____191 rng aq
  
let (embed_term_view :
  FStar_Range.range ->
    FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun t  ->
      match t with
      | FStar_Reflection_Data.Tv_FVar fv ->
          let uu____211 =
            let uu____212 =
              let uu____213 =
                let uu____214 = embed_fvar rng fv  in
                FStar_Syntax_Syntax.as_arg uu____214  in
              [uu____213]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t
              uu____212
             in
          uu____211 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_BVar fv ->
          let uu____218 =
            let uu____219 =
              let uu____220 =
                let uu____221 = embed_bv rng fv  in
                FStar_Syntax_Syntax.as_arg uu____221  in
              [uu____220]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t
              uu____219
             in
          uu____218 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Var bv ->
          let uu____225 =
            let uu____226 =
              let uu____227 =
                let uu____228 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____228  in
              [uu____227]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t
              uu____226
             in
          uu____225 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_App (hd1,a) ->
          let uu____233 =
            let uu____234 =
              let uu____235 =
                let uu____236 = embed_term rng hd1  in
                FStar_Syntax_Syntax.as_arg uu____236  in
              let uu____237 =
                let uu____240 =
                  let uu____241 = embed_argv rng a  in
                  FStar_Syntax_Syntax.as_arg uu____241  in
                [uu____240]  in
              uu____235 :: uu____237  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t
              uu____234
             in
          uu____233 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Abs (b,t1) ->
          let uu____246 =
            let uu____247 =
              let uu____248 =
                let uu____249 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____249  in
              let uu____250 =
                let uu____253 =
                  let uu____254 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____254  in
                [uu____253]  in
              uu____248 :: uu____250  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t
              uu____247
             in
          uu____246 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Arrow (b,c) ->
          let uu____259 =
            let uu____260 =
              let uu____261 =
                let uu____262 = embed_binder rng b  in
                FStar_Syntax_Syntax.as_arg uu____262  in
              let uu____263 =
                let uu____266 =
                  let uu____267 = embed_comp rng c  in
                  FStar_Syntax_Syntax.as_arg uu____267  in
                [uu____266]  in
              uu____261 :: uu____263  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t
              uu____260
             in
          uu____259 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Type u ->
          let uu____271 =
            let uu____272 =
              let uu____273 =
                let uu____274 = FStar_Syntax_Embeddings.embed_unit rng ()  in
                FStar_Syntax_Syntax.as_arg uu____274  in
              [uu____273]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t
              uu____272
             in
          uu____271 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
          let uu____279 =
            let uu____280 =
              let uu____281 =
                let uu____282 = embed_bv rng bv  in
                FStar_Syntax_Syntax.as_arg uu____282  in
              let uu____283 =
                let uu____286 =
                  let uu____287 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____287  in
                [uu____286]  in
              uu____281 :: uu____283  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t
              uu____280
             in
          uu____279 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Const c ->
          let uu____291 =
            let uu____292 =
              let uu____293 =
                let uu____294 = embed_const rng c  in
                FStar_Syntax_Syntax.as_arg uu____294  in
              [uu____293]  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t
              uu____292
             in
          uu____291 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
          let uu____299 =
            let uu____300 =
              let uu____301 =
                let uu____302 = FStar_Syntax_Embeddings.embed_int rng u  in
                FStar_Syntax_Syntax.as_arg uu____302  in
              let uu____303 =
                let uu____306 =
                  let uu____307 = embed_term rng t1  in
                  FStar_Syntax_Syntax.as_arg uu____307  in
                [uu____306]  in
              uu____301 :: uu____303  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t
              uu____300
             in
          uu____299 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Let (r,b,t1,t2) ->
          let uu____314 =
            let uu____315 =
              let uu____316 =
                let uu____317 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____317  in
              let uu____318 =
                let uu____321 =
                  let uu____322 = embed_bv rng b  in
                  FStar_Syntax_Syntax.as_arg uu____322  in
                let uu____323 =
                  let uu____326 =
                    let uu____327 = embed_term rng t1  in
                    FStar_Syntax_Syntax.as_arg uu____327  in
                  let uu____328 =
                    let uu____331 =
                      let uu____332 = embed_term rng t2  in
                      FStar_Syntax_Syntax.as_arg uu____332  in
                    [uu____331]  in
                  uu____326 :: uu____328  in
                uu____321 :: uu____323  in
              uu____316 :: uu____318  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t
              uu____315
             in
          uu____314 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Match (t1,brs) ->
          let uu____341 =
            let uu____342 =
              let uu____343 =
                let uu____344 = embed_term rng t1  in
                FStar_Syntax_Syntax.as_arg uu____344  in
              let uu____345 =
                let uu____348 =
                  let uu____349 =
                    let uu____350 =
                      FStar_Syntax_Embeddings.embed_list embed_branch
                        FStar_Reflection_Data.fstar_refl_branch
                       in
                    uu____350 rng brs  in
                  FStar_Syntax_Syntax.as_arg uu____349  in
                [uu____348]  in
              uu____343 :: uu____345  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t
              uu____342
             in
          uu____341 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Tv_Unknown  ->
          let uu___53_360 =
            FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___53_360.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___53_360.FStar_Syntax_Syntax.vars)
          }
  
let (embed_bv_view :
  FStar_Range.range ->
    FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun bvv  ->
      let uu____370 =
        let uu____371 =
          let uu____372 =
            let uu____373 =
              FStar_Syntax_Embeddings.embed_string rng
                bvv.FStar_Reflection_Data.bv_ppname
               in
            FStar_Syntax_Syntax.as_arg uu____373  in
          let uu____374 =
            let uu____377 =
              let uu____378 =
                FStar_Syntax_Embeddings.embed_int rng
                  bvv.FStar_Reflection_Data.bv_index
                 in
              FStar_Syntax_Syntax.as_arg uu____378  in
            let uu____379 =
              let uu____382 =
                let uu____383 =
                  embed_term rng bvv.FStar_Reflection_Data.bv_sort  in
                FStar_Syntax_Syntax.as_arg uu____383  in
              [uu____382]  in
            uu____377 :: uu____379  in
          uu____372 :: uu____374  in
        FStar_Syntax_Syntax.mk_Tm_app
          FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____371
         in
      uu____370 FStar_Pervasives_Native.None rng
  
let (embed_comp_view :
  FStar_Range.range ->
    FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun cv  ->
      match cv with
      | FStar_Reflection_Data.C_Total (t,md) ->
          let uu____401 =
            let uu____402 =
              let uu____403 =
                let uu____404 = embed_term rng t  in
                FStar_Syntax_Syntax.as_arg uu____404  in
              let uu____405 =
                let uu____408 =
                  let uu____409 =
                    let uu____410 =
                      FStar_Syntax_Embeddings.embed_option embed_term
                        FStar_Syntax_Syntax.t_term
                       in
                    uu____410 rng md  in
                  FStar_Syntax_Syntax.as_arg uu____409  in
                [uu____408]  in
              uu____403 :: uu____405  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t
              uu____402
             in
          uu____401 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Lemma (pre,post) ->
          let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
          let uu____425 =
            let uu____426 =
              let uu____427 =
                let uu____428 = embed_term rng pre  in
                FStar_Syntax_Syntax.as_arg uu____428  in
              let uu____429 =
                let uu____432 =
                  let uu____433 = embed_term rng post1  in
                  FStar_Syntax_Syntax.as_arg uu____433  in
                [uu____432]  in
              uu____427 :: uu____429  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t
              uu____426
             in
          uu____425 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.C_Unknown  ->
          let uu___54_436 =
            FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___54_436.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___54_436.FStar_Syntax_Syntax.vars)
          }
  
let (embed_order :
  FStar_Range.range -> FStar_Order.order -> FStar_Syntax_Syntax.term) =
  fun rng  ->
    fun o  ->
      let r =
        match o with
        | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
        | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
        | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt  in
      let uu___55_447 = r  in
      {
        FStar_Syntax_Syntax.n = (uu___55_447.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___55_447.FStar_Syntax_Syntax.vars)
      }
  
let (embed_sigelt :
  FStar_Range.range -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun se  ->
      FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt
        FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some rng)
  
let (embed_sigelt_view :
  FStar_Range.range ->
    FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term)
  =
  fun rng  ->
    fun sev  ->
      match sev with
      | FStar_Reflection_Data.Sg_Let (r,fv,ty,t) ->
          let uu____470 =
            let uu____471 =
              let uu____472 =
                let uu____473 = FStar_Syntax_Embeddings.embed_bool rng r  in
                FStar_Syntax_Syntax.as_arg uu____473  in
              let uu____474 =
                let uu____477 =
                  let uu____478 = embed_fvar rng fv  in
                  FStar_Syntax_Syntax.as_arg uu____478  in
                let uu____479 =
                  let uu____482 =
                    let uu____483 = embed_term rng ty  in
                    FStar_Syntax_Syntax.as_arg uu____483  in
                  let uu____484 =
                    let uu____487 =
                      let uu____488 = embed_term rng t  in
                      FStar_Syntax_Syntax.as_arg uu____488  in
                    [uu____487]  in
                  uu____482 :: uu____484  in
                uu____477 :: uu____479  in
              uu____472 :: uu____474  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t
              uu____471
             in
          uu____470 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Constructor (nm,ty) ->
          let uu____493 =
            let uu____494 =
              let uu____495 =
                let uu____496 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____496  in
              let uu____497 =
                let uu____500 =
                  let uu____501 = embed_term rng ty  in
                  FStar_Syntax_Syntax.as_arg uu____501  in
                [uu____500]  in
              uu____495 :: uu____497  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t
              uu____494
             in
          uu____493 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
          let uu____516 =
            let uu____517 =
              let uu____518 =
                let uu____519 =
                  FStar_Syntax_Embeddings.embed_string_list rng nm  in
                FStar_Syntax_Syntax.as_arg uu____519  in
              let uu____520 =
                let uu____523 =
                  let uu____524 = embed_binders rng bs  in
                  FStar_Syntax_Syntax.as_arg uu____524  in
                let uu____525 =
                  let uu____528 =
                    let uu____529 = embed_term rng t  in
                    FStar_Syntax_Syntax.as_arg uu____529  in
                  let uu____530 =
                    let uu____533 =
                      let uu____534 =
                        let uu____535 =
                          let uu____542 =
                            FStar_Syntax_Syntax.t_list_of
                              FStar_Syntax_Syntax.t_string
                             in
                          FStar_Syntax_Embeddings.embed_list
                            FStar_Syntax_Embeddings.embed_string_list
                            uu____542
                           in
                        uu____535 rng dcs  in
                      FStar_Syntax_Syntax.as_arg uu____534  in
                    [uu____533]  in
                  uu____528 :: uu____530  in
                uu____523 :: uu____525  in
              uu____518 :: uu____520  in
            FStar_Syntax_Syntax.mk_Tm_app
              FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t
              uu____517
             in
          uu____516 FStar_Pervasives_Native.None rng
      | FStar_Reflection_Data.Unk  ->
          let uu___56_550 =
            FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t  in
          {
            FStar_Syntax_Syntax.n = (uu___56_550.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = rng;
            FStar_Syntax_Syntax.vars = (uu___56_550.FStar_Syntax_Syntax.vars)
          }
  
let (unembed_bv :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____560 =
      let uu____561 = FStar_Syntax_Subst.compress t  in
      uu____561.FStar_Syntax_Syntax.n  in
    match uu____560 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_bv ->
        let uu____567 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____567
    | uu____568 ->
        ((let uu____570 =
            let uu____575 =
              let uu____576 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded bv: %s" uu____576  in
            (FStar_Errors.Warning_NotEmbedded, uu____575)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____570);
         FStar_Pervasives_Native.None)
  
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____586 =
      let uu____587 = FStar_Syntax_Subst.compress t  in
      uu____587.FStar_Syntax_Syntax.n  in
    match uu____586 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____593 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____593
    | uu____594 ->
        ((let uu____596 =
            let uu____601 =
              let uu____602 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded binder: %s" uu____602  in
            (FStar_Errors.Warning_NotEmbedded, uu____601)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____596);
         FStar_Pervasives_Native.None)
  
let rec (unembed_term :
  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unmeta_safe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____613;
           FStar_Syntax_Syntax.pos = uu____614;
           FStar_Syntax_Syntax.vars = uu____615;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> FStar_Pervasives_Native.Some qt
    | uu____632 ->
        ((let uu____634 =
            let uu____639 =
              let uu____640 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Not an embedded term: %s" uu____640  in
            (FStar_Errors.Warning_NotEmbedded, uu____639)  in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____634);
         FStar_Pervasives_Native.None)
  
let (unembed_aqualv :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.aqualv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____651 = FStar_Syntax_Util.head_and_args t1  in
    match uu____651 with
    | (hd1,args) ->
        let uu____690 =
          let uu____703 =
            let uu____704 = FStar_Syntax_Util.un_uinst hd1  in
            uu____704.FStar_Syntax_Syntax.n  in
          (uu____703, args)  in
        (match uu____690 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Q_Implicit
         | uu____747 ->
             ((let uu____761 =
                 let uu____766 =
                   let uu____767 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded aqualv: %s" uu____767
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____766)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____761);
              FStar_Pervasives_Native.None))
  
let (unembed_binders :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____775 = FStar_Syntax_Embeddings.unembed_list unembed_binder  in
    uu____775 t
  
let (unembed_fvar :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____791 =
      let uu____792 = FStar_Syntax_Subst.compress t  in
      uu____792.FStar_Syntax_Syntax.n  in
    match uu____791 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_fvar ->
        let uu____798 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____798
    | uu____799 ->
        ((let uu____801 =
            let uu____806 =
              let uu____807 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded fvar: %s" uu____807  in
            (FStar_Errors.Warning_NotEmbedded, uu____806)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____801);
         FStar_Pervasives_Native.None)
  
let (unembed_comp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____817 =
      let uu____818 = FStar_Syntax_Subst.compress t  in
      uu____818.FStar_Syntax_Syntax.n  in
    match uu____817 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_comp ->
        let uu____824 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____824
    | uu____825 ->
        ((let uu____827 =
            let uu____832 =
              let uu____833 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded comp: %s" uu____833  in
            (FStar_Errors.Warning_NotEmbedded, uu____832)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____827);
         FStar_Pervasives_Native.None)
  
let (unembed_env :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____843 =
      let uu____844 = FStar_Syntax_Subst.compress t  in
      uu____844.FStar_Syntax_Syntax.n  in
    match uu____843 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_env ->
        let uu____850 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____850
    | uu____851 ->
        ((let uu____853 =
            let uu____858 =
              let uu____859 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded env: %s" uu____859  in
            (FStar_Errors.Warning_NotEmbedded, uu____858)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____853);
         FStar_Pervasives_Native.None)
  
let (unembed_const :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.vconst FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____870 = FStar_Syntax_Util.head_and_args t1  in
    match uu____870 with
    | (hd1,args) ->
        let uu____909 =
          let uu____922 =
            let uu____923 = FStar_Syntax_Util.un_uinst hd1  in
            uu____923.FStar_Syntax_Syntax.n  in
          (uu____922, args)  in
        (match uu____909 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____983)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid
             ->
             let uu____1008 = FStar_Syntax_Embeddings.unembed_int i  in
             FStar_Util.bind_opt uu____1008
               (fun i1  ->
                  FStar_All.pipe_left
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                    (FStar_Reflection_Data.C_Int i1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1017)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid
             ->
             let uu____1042 = FStar_Syntax_Embeddings.unembed_string s  in
             FStar_Util.bind_opt uu____1042
               (fun s1  ->
                  FStar_All.pipe_left
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                    (FStar_Reflection_Data.C_String s1))
         | uu____1049 ->
             ((let uu____1063 =
                 let uu____1068 =
                   let uu____1069 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded vconst: %s" uu____1069
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1068)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1063);
              FStar_Pervasives_Native.None))
  
let rec (unembed_pattern :
  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.unembedder) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1078 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1078 with
    | (hd1,args) ->
        let uu____1117 =
          let uu____1130 =
            let uu____1131 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1131.FStar_Syntax_Syntax.n  in
          (uu____1130, args)  in
        (match uu____1117 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1146)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid
             ->
             let uu____1171 = unembed_const c  in
             FStar_Util.bind_opt uu____1171
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                    (FStar_Reflection_Data.Pat_Constant c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1180)::(ps,uu____1182)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid
             ->
             let uu____1217 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1217
               (fun f1  ->
                  let uu____1223 =
                    let uu____1228 =
                      FStar_Syntax_Embeddings.unembed_list unembed_pattern
                       in
                    uu____1228 ps  in
                  FStar_Util.bind_opt uu____1223
                    (fun ps1  ->
                       FStar_All.pipe_left
                         (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                         (FStar_Reflection_Data.Pat_Cons (f1, ps1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1247)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid
             ->
             let uu____1272 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1272
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_Pervasives_Native.Some _0_44)
                    (FStar_Reflection_Data.Pat_Var bv1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(bv,uu____1281)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid
             ->
             let uu____1306 = unembed_bv bv  in
             FStar_Util.bind_opt uu____1306
               (fun bv1  ->
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                    (FStar_Reflection_Data.Pat_Wild bv1))
         | uu____1313 ->
             ((let uu____1327 =
                 let uu____1332 =
                   let uu____1333 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded pattern: %s"
                     uu____1333
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____1332)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1327);
              FStar_Pervasives_Native.None))
  
let (unembed_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_pair unembed_pattern unembed_term 
let (unembed_argv :
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Embeddings.unembedder)
  = FStar_Syntax_Embeddings.unembed_pair unembed_term unembed_aqualv 
let (unembed_term_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1364 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1364 with
    | (hd1,args) ->
        let uu____1403 =
          let uu____1416 =
            let uu____1417 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1417.FStar_Syntax_Syntax.n  in
          (uu____1416, args)  in
        (match uu____1403 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1432)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid
             ->
             let uu____1457 = unembed_bv b  in
             FStar_Util.bind_opt uu____1457
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                    (FStar_Reflection_Data.Tv_Var b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1466)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid
             ->
             let uu____1491 = unembed_bv b  in
             FStar_Util.bind_opt uu____1491
               (fun b1  ->
                  FStar_All.pipe_left
                    (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                    (FStar_Reflection_Data.Tv_BVar b1))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____1500)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid
             ->
             let uu____1525 = unembed_fvar f  in
             FStar_Util.bind_opt uu____1525
               (fun f1  ->
                  FStar_All.pipe_left
                    (fun _0_48  -> FStar_Pervasives_Native.Some _0_48)
                    (FStar_Reflection_Data.Tv_FVar f1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1534)::(r,uu____1536)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid
             ->
             let uu____1571 = unembed_term l  in
             FStar_Util.bind_opt uu____1571
               (fun l1  ->
                  let uu____1577 = unembed_argv r  in
                  FStar_Util.bind_opt uu____1577
                    (fun r1  ->
                       FStar_All.pipe_left
                         (fun _0_49  -> FStar_Pervasives_Native.Some _0_49)
                         (FStar_Reflection_Data.Tv_App (l1, r1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1602)::(t2,uu____1604)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid
             ->
             let uu____1639 = unembed_binder b  in
             FStar_Util.bind_opt uu____1639
               (fun b1  ->
                  let uu____1645 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1645
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_50  -> FStar_Pervasives_Native.Some _0_50)
                         (FStar_Reflection_Data.Tv_Abs (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1654)::(t2,uu____1656)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid
             ->
             let uu____1691 = unembed_binder b  in
             FStar_Util.bind_opt uu____1691
               (fun b1  ->
                  let uu____1697 = unembed_comp t2  in
                  FStar_Util.bind_opt uu____1697
                    (fun c  ->
                       FStar_All.pipe_left
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                         (FStar_Reflection_Data.Tv_Arrow (b1, c))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1706)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid
             ->
             let uu____1731 = FStar_Syntax_Embeddings.unembed_unit u  in
             FStar_Util.bind_opt uu____1731
               (fun u1  ->
                  FStar_All.pipe_left
                    (fun _0_52  -> FStar_Pervasives_Native.Some _0_52)
                    (FStar_Reflection_Data.Tv_Type ()))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1740)::(t2,uu____1742)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid
             ->
             let uu____1777 = unembed_bv b  in
             FStar_Util.bind_opt uu____1777
               (fun b1  ->
                  let uu____1783 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1783
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_53  -> FStar_Pervasives_Native.Some _0_53)
                         (FStar_Reflection_Data.Tv_Refine (b1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1792)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid
             ->
             let uu____1817 = unembed_const c  in
             FStar_Util.bind_opt uu____1817
               (fun c1  ->
                  FStar_All.pipe_left
                    (fun _0_54  -> FStar_Pervasives_Native.Some _0_54)
                    (FStar_Reflection_Data.Tv_Const c1))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1826)::(t2,uu____1828)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid
             ->
             let uu____1863 = FStar_Syntax_Embeddings.unembed_int u  in
             FStar_Util.bind_opt uu____1863
               (fun u1  ->
                  let uu____1869 = unembed_term t2  in
                  FStar_Util.bind_opt uu____1869
                    (fun t3  ->
                       FStar_All.pipe_left
                         (fun _0_55  -> FStar_Pervasives_Native.Some _0_55)
                         (FStar_Reflection_Data.Tv_Uvar (u1, t3))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____1878)::(b,uu____1880)::(t11,uu____1882)::(t2,uu____1884)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid
             ->
             let uu____1939 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____1939
               (fun r1  ->
                  let uu____1945 = unembed_bv b  in
                  FStar_Util.bind_opt uu____1945
                    (fun b1  ->
                       let uu____1951 = unembed_term t11  in
                       FStar_Util.bind_opt uu____1951
                         (fun t12  ->
                            let uu____1957 = unembed_term t2  in
                            FStar_Util.bind_opt uu____1957
                              (fun t21  ->
                                 FStar_All.pipe_left
                                   (fun _0_56  ->
                                      FStar_Pervasives_Native.Some _0_56)
                                   (FStar_Reflection_Data.Tv_Let
                                      (r1, b1, t12, t21))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1966)::(brs,uu____1968)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid
             ->
             let uu____2003 = unembed_term t2  in
             FStar_Util.bind_opt uu____2003
               (fun t3  ->
                  let uu____2009 =
                    let uu____2018 =
                      FStar_Syntax_Embeddings.unembed_list unembed_branch  in
                    uu____2018 brs  in
                  FStar_Util.bind_opt uu____2009
                    (fun brs1  ->
                       FStar_All.pipe_left
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                         (FStar_Reflection_Data.Tv_Match (t3, brs1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_58  -> FStar_Pervasives_Native.Some _0_58)
               FStar_Reflection_Data.Tv_Unknown
         | uu____2072 ->
             ((let uu____2086 =
                 let uu____2091 =
                   let uu____2092 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded term_view: %s"
                     uu____2092
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2091)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2086);
              FStar_Pervasives_Native.None))
  
let (unembed_bv_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.bv_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2103 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2103 with
    | (hd1,args) ->
        let uu____2142 =
          let uu____2155 =
            let uu____2156 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2156.FStar_Syntax_Syntax.n  in
          (uu____2155, args)  in
        (match uu____2142 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2171)::(idx,uu____2173)::(s,uu____2175)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid
             ->
             let uu____2220 = FStar_Syntax_Embeddings.unembed_string nm  in
             FStar_Util.bind_opt uu____2220
               (fun nm1  ->
                  let uu____2226 = FStar_Syntax_Embeddings.unembed_int idx
                     in
                  FStar_Util.bind_opt uu____2226
                    (fun idx1  ->
                       let uu____2232 = unembed_term s  in
                       FStar_Util.bind_opt uu____2232
                         (fun s1  ->
                            FStar_All.pipe_left
                              (fun _0_59  ->
                                 FStar_Pervasives_Native.Some _0_59)
                              {
                                FStar_Reflection_Data.bv_ppname = nm1;
                                FStar_Reflection_Data.bv_index = idx1;
                                FStar_Reflection_Data.bv_sort = s1
                              })))
         | uu____2239 ->
             ((let uu____2253 =
                 let uu____2258 =
                   let uu____2259 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded bv_view: %s"
                     uu____2259
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2258)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2253);
              FStar_Pervasives_Native.None))
  
let (unembed_comp_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.comp_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2270 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2270 with
    | (hd1,args) ->
        let uu____2309 =
          let uu____2322 =
            let uu____2323 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2323.FStar_Syntax_Syntax.n  in
          (uu____2322, args)  in
        (match uu____2309 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2338)::(md,uu____2340)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid
             ->
             let uu____2375 = unembed_term t2  in
             FStar_Util.bind_opt uu____2375
               (fun t3  ->
                  let uu____2381 =
                    let uu____2386 =
                      FStar_Syntax_Embeddings.unembed_option unembed_term  in
                    uu____2386 md  in
                  FStar_Util.bind_opt uu____2381
                    (fun md1  ->
                       FStar_All.pipe_left
                         (fun _0_60  -> FStar_Pervasives_Native.Some _0_60)
                         (FStar_Reflection_Data.C_Total (t3, md1))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____2405)::(post,uu____2407)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid
             ->
             let uu____2442 = unembed_term pre  in
             FStar_Util.bind_opt uu____2442
               (fun pre1  ->
                  let uu____2448 = unembed_term post  in
                  FStar_Util.bind_opt uu____2448
                    (fun post1  ->
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_Pervasives_Native.Some _0_61)
                         (FStar_Reflection_Data.C_Lemma (pre1, post1))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid
             ->
             FStar_All.pipe_left
               (fun _0_62  -> FStar_Pervasives_Native.Some _0_62)
               FStar_Reflection_Data.C_Unknown
         | uu____2472 ->
             ((let uu____2486 =
                 let uu____2491 =
                   let uu____2492 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded comp_view: %s"
                     uu____2492
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2491)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2486);
              FStar_Pervasives_Native.None))
  
let (unembed_order :
  FStar_Syntax_Syntax.term ->
    FStar_Order.order FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2503 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2503 with
    | (hd1,args) ->
        let uu____2542 =
          let uu____2555 =
            let uu____2556 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2556.FStar_Syntax_Syntax.n  in
          (uu____2555, args)  in
        (match uu____2542 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Pervasives_Native.Some FStar_Order.Gt
         | uu____2614 ->
             ((let uu____2628 =
                 let uu____2633 =
                   let uu____2634 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded order: %s" uu____2634
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2633)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2628);
              FStar_Pervasives_Native.None))
  
let (unembed_sigelt :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2644 =
      let uu____2645 = FStar_Syntax_Subst.compress t  in
      uu____2645.FStar_Syntax_Syntax.n  in
    match uu____2644 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_sigelt ->
        let uu____2651 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____2651
    | uu____2652 ->
        ((let uu____2654 =
            let uu____2659 =
              let uu____2660 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format1 "Not an embedded sigelt: %s" uu____2660  in
            (FStar_Errors.Warning_NotEmbedded, uu____2659)  in
          FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2654);
         FStar_Pervasives_Native.None)
  
let (unembed_sigelt_view :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.sigelt_view FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2671 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2671 with
    | (hd1,args) ->
        let uu____2710 =
          let uu____2723 =
            let uu____2724 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2724.FStar_Syntax_Syntax.n  in
          (uu____2723, args)  in
        (match uu____2710 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____2739)::(bs,uu____2741)::(t2,uu____2743)::(dcs,uu____2745)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid
             ->
             let uu____2800 = FStar_Syntax_Embeddings.unembed_string_list nm
                in
             FStar_Util.bind_opt uu____2800
               (fun nm1  ->
                  let uu____2812 = unembed_binders bs  in
                  FStar_Util.bind_opt uu____2812
                    (fun bs1  ->
                       let uu____2818 = unembed_term t2  in
                       FStar_Util.bind_opt uu____2818
                         (fun t3  ->
                            let uu____2824 =
                              let uu____2831 =
                                let uu____2838 =
                                  FStar_Syntax_Embeddings.unembed_list
                                    FStar_Syntax_Embeddings.unembed_string
                                   in
                                FStar_Syntax_Embeddings.unembed_list
                                  uu____2838
                                 in
                              uu____2831 dcs  in
                            FStar_Util.bind_opt uu____2824
                              (fun dcs1  ->
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_Pervasives_Native.Some _0_63)
                                   (FStar_Reflection_Data.Sg_Inductive
                                      (nm1, bs1, t3, dcs1))))))
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(r,uu____2871)::(fvar1,uu____2873)::(ty,uu____2875)::(t2,uu____2877)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid
             ->
             let uu____2932 = FStar_Syntax_Embeddings.unembed_bool r  in
             FStar_Util.bind_opt uu____2932
               (fun r1  ->
                  let uu____2938 = unembed_fvar fvar1  in
                  FStar_Util.bind_opt uu____2938
                    (fun fvar2  ->
                       let uu____2944 = unembed_term ty  in
                       FStar_Util.bind_opt uu____2944
                         (fun ty1  ->
                            let uu____2950 = unembed_term t2  in
                            FStar_Util.bind_opt uu____2950
                              (fun t3  ->
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_Pervasives_Native.Some _0_64)
                                   (FStar_Reflection_Data.Sg_Let
                                      (r1, fvar2, ty1, t3))))))
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid
             -> FStar_Pervasives_Native.Some FStar_Reflection_Data.Unk
         | uu____2972 ->
             ((let uu____2986 =
                 let uu____2991 =
                   let uu____2992 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.format1 "Not an embedded sigelt_view: %s"
                     uu____2992
                    in
                 (FStar_Errors.Warning_NotEmbedded, uu____2991)  in
               FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____2986);
              FStar_Pervasives_Native.None))
  
let (unfold_lazy_bv :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_binder :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_fvar :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  ->
    let fv = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
    let uu____3003 =
      let uu____3004 =
        let uu____3005 =
          let uu____3006 =
            let uu____3007 = FStar_Reflection_Basic.inspect_fv fv  in
            let uu____3010 =
              FStar_Syntax_Embeddings.embed_list
                FStar_Syntax_Embeddings.embed_string
                FStar_Syntax_Syntax.t_string
               in
            uu____3010 i.FStar_Syntax_Syntax.rng uu____3007  in
          FStar_Syntax_Syntax.as_arg uu____3006  in
        [uu____3005]  in
      FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv
        uu____3004
       in
    uu____3003 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng
  
let (unfold_lazy_comp :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_env :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 
let (unfold_lazy_sigelt :
  FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term) =
  fun i  -> FStar_Syntax_Util.exp_unit 