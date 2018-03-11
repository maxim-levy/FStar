open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
  | Exclude of step 
  | Weak 
  | HNF 
  | Primops 
  | Eager_unfolding 
  | Inlining 
  | NoDeltaSteps 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
  | UnfoldAttr of FStar_Syntax_Syntax.attribute 
  | UnfoldTac 
  | PureSubtermsWithinComputations 
  | Simplify 
  | EraseUniverses 
  | AllowUnboundUniverses 
  | Reify 
  | CompressUvars 
  | NoFullNorm 
  | CheckNoUvars 
  | Unmeta 
  | Unascribe [@@deriving show]
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Beta  -> true | uu____22 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____26 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____30 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____46 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____50 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____54 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____62 -> false
  
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____66 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____71 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____85 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____103 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____118 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____122 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____126 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____130 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____138 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____142 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____146 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____150 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____154 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____162 'Auu____163 .
    ('Auu____162 -> 'Auu____163) ->
      'Auu____163 ->
        'Auu____162 FStar_Pervasives_Native.option -> 'Auu____163
  =
  fun f  ->
    fun d  ->
      fun uu___75_180  ->
        match uu___75_180 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> d
  
type fsteps =
  {
  beta: Prims.bool ;
  iota: Prims.bool ;
  zeta: Prims.bool ;
  weak: Prims.bool ;
  hnf: Prims.bool ;
  primops: Prims.bool ;
  no_delta_steps: Prims.bool ;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
  unfold_attr:
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option ;
  unfold_tac: Prims.bool ;
  pure_subterms_within_computations: Prims.bool ;
  simplify: Prims.bool ;
  erase_universes: Prims.bool ;
  allow_unbound_universes: Prims.bool ;
  reify_: Prims.bool ;
  compress_uvars: Prims.bool ;
  no_full_norm: Prims.bool ;
  check_no_uvars: Prims.bool ;
  unmeta: Prims.bool ;
  unascribe: Prims.bool }[@@deriving show]
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__iota
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__zeta
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__weak
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__hnf
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__primops
  
let (__proj__Mkfsteps__item__no_delta_steps : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_delta_steps
  
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_until
  
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_only
  
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_tac
  
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} ->
        __fname__pure_subterms_within_computations
  
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__simplify
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__erase_universes
  
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__allow_unbound_universes
  
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__reify_
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__compress_uvars
  
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__check_no_uvars
  
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unmeta
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unascribe
  
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    no_delta_steps = false;
    unfold_until = FStar_Pervasives_Native.None;
    unfold_only = FStar_Pervasives_Native.None;
    unfold_attr = FStar_Pervasives_Native.None;
    unfold_tac = false;
    pure_subterms_within_computations = false;
    simplify = false;
    erase_universes = false;
    allow_unbound_universes = false;
    reify_ = false;
    compress_uvars = false;
    no_full_norm = false;
    check_no_uvars = false;
    unmeta = false;
    unascribe = false
  } 
let (fstep_add_one : step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      let add_opt x uu___76_1038 =
        match uu___76_1038 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___94_1058 = fs  in
          {
            beta = true;
            iota = (uu___94_1058.iota);
            zeta = (uu___94_1058.zeta);
            weak = (uu___94_1058.weak);
            hnf = (uu___94_1058.hnf);
            primops = (uu___94_1058.primops);
            no_delta_steps = (uu___94_1058.no_delta_steps);
            unfold_until = (uu___94_1058.unfold_until);
            unfold_only = (uu___94_1058.unfold_only);
            unfold_attr = (uu___94_1058.unfold_attr);
            unfold_tac = (uu___94_1058.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_1058.pure_subterms_within_computations);
            simplify = (uu___94_1058.simplify);
            erase_universes = (uu___94_1058.erase_universes);
            allow_unbound_universes = (uu___94_1058.allow_unbound_universes);
            reify_ = (uu___94_1058.reify_);
            compress_uvars = (uu___94_1058.compress_uvars);
            no_full_norm = (uu___94_1058.no_full_norm);
            check_no_uvars = (uu___94_1058.check_no_uvars);
            unmeta = (uu___94_1058.unmeta);
            unascribe = (uu___94_1058.unascribe)
          }
      | Iota  ->
          let uu___95_1059 = fs  in
          {
            beta = (uu___95_1059.beta);
            iota = true;
            zeta = (uu___95_1059.zeta);
            weak = (uu___95_1059.weak);
            hnf = (uu___95_1059.hnf);
            primops = (uu___95_1059.primops);
            no_delta_steps = (uu___95_1059.no_delta_steps);
            unfold_until = (uu___95_1059.unfold_until);
            unfold_only = (uu___95_1059.unfold_only);
            unfold_attr = (uu___95_1059.unfold_attr);
            unfold_tac = (uu___95_1059.unfold_tac);
            pure_subterms_within_computations =
              (uu___95_1059.pure_subterms_within_computations);
            simplify = (uu___95_1059.simplify);
            erase_universes = (uu___95_1059.erase_universes);
            allow_unbound_universes = (uu___95_1059.allow_unbound_universes);
            reify_ = (uu___95_1059.reify_);
            compress_uvars = (uu___95_1059.compress_uvars);
            no_full_norm = (uu___95_1059.no_full_norm);
            check_no_uvars = (uu___95_1059.check_no_uvars);
            unmeta = (uu___95_1059.unmeta);
            unascribe = (uu___95_1059.unascribe)
          }
      | Zeta  ->
          let uu___96_1060 = fs  in
          {
            beta = (uu___96_1060.beta);
            iota = (uu___96_1060.iota);
            zeta = true;
            weak = (uu___96_1060.weak);
            hnf = (uu___96_1060.hnf);
            primops = (uu___96_1060.primops);
            no_delta_steps = (uu___96_1060.no_delta_steps);
            unfold_until = (uu___96_1060.unfold_until);
            unfold_only = (uu___96_1060.unfold_only);
            unfold_attr = (uu___96_1060.unfold_attr);
            unfold_tac = (uu___96_1060.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1060.pure_subterms_within_computations);
            simplify = (uu___96_1060.simplify);
            erase_universes = (uu___96_1060.erase_universes);
            allow_unbound_universes = (uu___96_1060.allow_unbound_universes);
            reify_ = (uu___96_1060.reify_);
            compress_uvars = (uu___96_1060.compress_uvars);
            no_full_norm = (uu___96_1060.no_full_norm);
            check_no_uvars = (uu___96_1060.check_no_uvars);
            unmeta = (uu___96_1060.unmeta);
            unascribe = (uu___96_1060.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___97_1061 = fs  in
          {
            beta = false;
            iota = (uu___97_1061.iota);
            zeta = (uu___97_1061.zeta);
            weak = (uu___97_1061.weak);
            hnf = (uu___97_1061.hnf);
            primops = (uu___97_1061.primops);
            no_delta_steps = (uu___97_1061.no_delta_steps);
            unfold_until = (uu___97_1061.unfold_until);
            unfold_only = (uu___97_1061.unfold_only);
            unfold_attr = (uu___97_1061.unfold_attr);
            unfold_tac = (uu___97_1061.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1061.pure_subterms_within_computations);
            simplify = (uu___97_1061.simplify);
            erase_universes = (uu___97_1061.erase_universes);
            allow_unbound_universes = (uu___97_1061.allow_unbound_universes);
            reify_ = (uu___97_1061.reify_);
            compress_uvars = (uu___97_1061.compress_uvars);
            no_full_norm = (uu___97_1061.no_full_norm);
            check_no_uvars = (uu___97_1061.check_no_uvars);
            unmeta = (uu___97_1061.unmeta);
            unascribe = (uu___97_1061.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___98_1062 = fs  in
          {
            beta = (uu___98_1062.beta);
            iota = false;
            zeta = (uu___98_1062.zeta);
            weak = (uu___98_1062.weak);
            hnf = (uu___98_1062.hnf);
            primops = (uu___98_1062.primops);
            no_delta_steps = (uu___98_1062.no_delta_steps);
            unfold_until = (uu___98_1062.unfold_until);
            unfold_only = (uu___98_1062.unfold_only);
            unfold_attr = (uu___98_1062.unfold_attr);
            unfold_tac = (uu___98_1062.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1062.pure_subterms_within_computations);
            simplify = (uu___98_1062.simplify);
            erase_universes = (uu___98_1062.erase_universes);
            allow_unbound_universes = (uu___98_1062.allow_unbound_universes);
            reify_ = (uu___98_1062.reify_);
            compress_uvars = (uu___98_1062.compress_uvars);
            no_full_norm = (uu___98_1062.no_full_norm);
            check_no_uvars = (uu___98_1062.check_no_uvars);
            unmeta = (uu___98_1062.unmeta);
            unascribe = (uu___98_1062.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___99_1063 = fs  in
          {
            beta = (uu___99_1063.beta);
            iota = (uu___99_1063.iota);
            zeta = false;
            weak = (uu___99_1063.weak);
            hnf = (uu___99_1063.hnf);
            primops = (uu___99_1063.primops);
            no_delta_steps = (uu___99_1063.no_delta_steps);
            unfold_until = (uu___99_1063.unfold_until);
            unfold_only = (uu___99_1063.unfold_only);
            unfold_attr = (uu___99_1063.unfold_attr);
            unfold_tac = (uu___99_1063.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1063.pure_subterms_within_computations);
            simplify = (uu___99_1063.simplify);
            erase_universes = (uu___99_1063.erase_universes);
            allow_unbound_universes = (uu___99_1063.allow_unbound_universes);
            reify_ = (uu___99_1063.reify_);
            compress_uvars = (uu___99_1063.compress_uvars);
            no_full_norm = (uu___99_1063.no_full_norm);
            check_no_uvars = (uu___99_1063.check_no_uvars);
            unmeta = (uu___99_1063.unmeta);
            unascribe = (uu___99_1063.unascribe)
          }
      | Exclude uu____1064 -> failwith "Bad exclude"
      | Weak  ->
          let uu___100_1065 = fs  in
          {
            beta = (uu___100_1065.beta);
            iota = (uu___100_1065.iota);
            zeta = (uu___100_1065.zeta);
            weak = true;
            hnf = (uu___100_1065.hnf);
            primops = (uu___100_1065.primops);
            no_delta_steps = (uu___100_1065.no_delta_steps);
            unfold_until = (uu___100_1065.unfold_until);
            unfold_only = (uu___100_1065.unfold_only);
            unfold_attr = (uu___100_1065.unfold_attr);
            unfold_tac = (uu___100_1065.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1065.pure_subterms_within_computations);
            simplify = (uu___100_1065.simplify);
            erase_universes = (uu___100_1065.erase_universes);
            allow_unbound_universes = (uu___100_1065.allow_unbound_universes);
            reify_ = (uu___100_1065.reify_);
            compress_uvars = (uu___100_1065.compress_uvars);
            no_full_norm = (uu___100_1065.no_full_norm);
            check_no_uvars = (uu___100_1065.check_no_uvars);
            unmeta = (uu___100_1065.unmeta);
            unascribe = (uu___100_1065.unascribe)
          }
      | HNF  ->
          let uu___101_1066 = fs  in
          {
            beta = (uu___101_1066.beta);
            iota = (uu___101_1066.iota);
            zeta = (uu___101_1066.zeta);
            weak = (uu___101_1066.weak);
            hnf = true;
            primops = (uu___101_1066.primops);
            no_delta_steps = (uu___101_1066.no_delta_steps);
            unfold_until = (uu___101_1066.unfold_until);
            unfold_only = (uu___101_1066.unfold_only);
            unfold_attr = (uu___101_1066.unfold_attr);
            unfold_tac = (uu___101_1066.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1066.pure_subterms_within_computations);
            simplify = (uu___101_1066.simplify);
            erase_universes = (uu___101_1066.erase_universes);
            allow_unbound_universes = (uu___101_1066.allow_unbound_universes);
            reify_ = (uu___101_1066.reify_);
            compress_uvars = (uu___101_1066.compress_uvars);
            no_full_norm = (uu___101_1066.no_full_norm);
            check_no_uvars = (uu___101_1066.check_no_uvars);
            unmeta = (uu___101_1066.unmeta);
            unascribe = (uu___101_1066.unascribe)
          }
      | Primops  ->
          let uu___102_1067 = fs  in
          {
            beta = (uu___102_1067.beta);
            iota = (uu___102_1067.iota);
            zeta = (uu___102_1067.zeta);
            weak = (uu___102_1067.weak);
            hnf = (uu___102_1067.hnf);
            primops = true;
            no_delta_steps = (uu___102_1067.no_delta_steps);
            unfold_until = (uu___102_1067.unfold_until);
            unfold_only = (uu___102_1067.unfold_only);
            unfold_attr = (uu___102_1067.unfold_attr);
            unfold_tac = (uu___102_1067.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1067.pure_subterms_within_computations);
            simplify = (uu___102_1067.simplify);
            erase_universes = (uu___102_1067.erase_universes);
            allow_unbound_universes = (uu___102_1067.allow_unbound_universes);
            reify_ = (uu___102_1067.reify_);
            compress_uvars = (uu___102_1067.compress_uvars);
            no_full_norm = (uu___102_1067.no_full_norm);
            check_no_uvars = (uu___102_1067.check_no_uvars);
            unmeta = (uu___102_1067.unmeta);
            unascribe = (uu___102_1067.unascribe)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | NoDeltaSteps  ->
          let uu___103_1068 = fs  in
          {
            beta = (uu___103_1068.beta);
            iota = (uu___103_1068.iota);
            zeta = (uu___103_1068.zeta);
            weak = (uu___103_1068.weak);
            hnf = (uu___103_1068.hnf);
            primops = (uu___103_1068.primops);
            no_delta_steps = true;
            unfold_until = (uu___103_1068.unfold_until);
            unfold_only = (uu___103_1068.unfold_only);
            unfold_attr = (uu___103_1068.unfold_attr);
            unfold_tac = (uu___103_1068.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1068.pure_subterms_within_computations);
            simplify = (uu___103_1068.simplify);
            erase_universes = (uu___103_1068.erase_universes);
            allow_unbound_universes = (uu___103_1068.allow_unbound_universes);
            reify_ = (uu___103_1068.reify_);
            compress_uvars = (uu___103_1068.compress_uvars);
            no_full_norm = (uu___103_1068.no_full_norm);
            check_no_uvars = (uu___103_1068.check_no_uvars);
            unmeta = (uu___103_1068.unmeta);
            unascribe = (uu___103_1068.unascribe)
          }
      | UnfoldUntil d ->
          let uu___104_1070 = fs  in
          {
            beta = (uu___104_1070.beta);
            iota = (uu___104_1070.iota);
            zeta = (uu___104_1070.zeta);
            weak = (uu___104_1070.weak);
            hnf = (uu___104_1070.hnf);
            primops = (uu___104_1070.primops);
            no_delta_steps = (uu___104_1070.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___104_1070.unfold_only);
            unfold_attr = (uu___104_1070.unfold_attr);
            unfold_tac = (uu___104_1070.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1070.pure_subterms_within_computations);
            simplify = (uu___104_1070.simplify);
            erase_universes = (uu___104_1070.erase_universes);
            allow_unbound_universes = (uu___104_1070.allow_unbound_universes);
            reify_ = (uu___104_1070.reify_);
            compress_uvars = (uu___104_1070.compress_uvars);
            no_full_norm = (uu___104_1070.no_full_norm);
            check_no_uvars = (uu___104_1070.check_no_uvars);
            unmeta = (uu___104_1070.unmeta);
            unascribe = (uu___104_1070.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___105_1074 = fs  in
          {
            beta = (uu___105_1074.beta);
            iota = (uu___105_1074.iota);
            zeta = (uu___105_1074.zeta);
            weak = (uu___105_1074.weak);
            hnf = (uu___105_1074.hnf);
            primops = (uu___105_1074.primops);
            no_delta_steps = (uu___105_1074.no_delta_steps);
            unfold_until = (uu___105_1074.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___105_1074.unfold_attr);
            unfold_tac = (uu___105_1074.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1074.pure_subterms_within_computations);
            simplify = (uu___105_1074.simplify);
            erase_universes = (uu___105_1074.erase_universes);
            allow_unbound_universes = (uu___105_1074.allow_unbound_universes);
            reify_ = (uu___105_1074.reify_);
            compress_uvars = (uu___105_1074.compress_uvars);
            no_full_norm = (uu___105_1074.no_full_norm);
            check_no_uvars = (uu___105_1074.check_no_uvars);
            unmeta = (uu___105_1074.unmeta);
            unascribe = (uu___105_1074.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___106_1078 = fs  in
          {
            beta = (uu___106_1078.beta);
            iota = (uu___106_1078.iota);
            zeta = (uu___106_1078.zeta);
            weak = (uu___106_1078.weak);
            hnf = (uu___106_1078.hnf);
            primops = (uu___106_1078.primops);
            no_delta_steps = (uu___106_1078.no_delta_steps);
            unfold_until = (uu___106_1078.unfold_until);
            unfold_only = (uu___106_1078.unfold_only);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___106_1078.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1078.pure_subterms_within_computations);
            simplify = (uu___106_1078.simplify);
            erase_universes = (uu___106_1078.erase_universes);
            allow_unbound_universes = (uu___106_1078.allow_unbound_universes);
            reify_ = (uu___106_1078.reify_);
            compress_uvars = (uu___106_1078.compress_uvars);
            no_full_norm = (uu___106_1078.no_full_norm);
            check_no_uvars = (uu___106_1078.check_no_uvars);
            unmeta = (uu___106_1078.unmeta);
            unascribe = (uu___106_1078.unascribe)
          }
      | UnfoldTac  ->
          let uu___107_1079 = fs  in
          {
            beta = (uu___107_1079.beta);
            iota = (uu___107_1079.iota);
            zeta = (uu___107_1079.zeta);
            weak = (uu___107_1079.weak);
            hnf = (uu___107_1079.hnf);
            primops = (uu___107_1079.primops);
            no_delta_steps = (uu___107_1079.no_delta_steps);
            unfold_until = (uu___107_1079.unfold_until);
            unfold_only = (uu___107_1079.unfold_only);
            unfold_attr = (uu___107_1079.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___107_1079.pure_subterms_within_computations);
            simplify = (uu___107_1079.simplify);
            erase_universes = (uu___107_1079.erase_universes);
            allow_unbound_universes = (uu___107_1079.allow_unbound_universes);
            reify_ = (uu___107_1079.reify_);
            compress_uvars = (uu___107_1079.compress_uvars);
            no_full_norm = (uu___107_1079.no_full_norm);
            check_no_uvars = (uu___107_1079.check_no_uvars);
            unmeta = (uu___107_1079.unmeta);
            unascribe = (uu___107_1079.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___108_1080 = fs  in
          {
            beta = (uu___108_1080.beta);
            iota = (uu___108_1080.iota);
            zeta = (uu___108_1080.zeta);
            weak = (uu___108_1080.weak);
            hnf = (uu___108_1080.hnf);
            primops = (uu___108_1080.primops);
            no_delta_steps = (uu___108_1080.no_delta_steps);
            unfold_until = (uu___108_1080.unfold_until);
            unfold_only = (uu___108_1080.unfold_only);
            unfold_attr = (uu___108_1080.unfold_attr);
            unfold_tac = (uu___108_1080.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___108_1080.simplify);
            erase_universes = (uu___108_1080.erase_universes);
            allow_unbound_universes = (uu___108_1080.allow_unbound_universes);
            reify_ = (uu___108_1080.reify_);
            compress_uvars = (uu___108_1080.compress_uvars);
            no_full_norm = (uu___108_1080.no_full_norm);
            check_no_uvars = (uu___108_1080.check_no_uvars);
            unmeta = (uu___108_1080.unmeta);
            unascribe = (uu___108_1080.unascribe)
          }
      | Simplify  ->
          let uu___109_1081 = fs  in
          {
            beta = (uu___109_1081.beta);
            iota = (uu___109_1081.iota);
            zeta = (uu___109_1081.zeta);
            weak = (uu___109_1081.weak);
            hnf = (uu___109_1081.hnf);
            primops = (uu___109_1081.primops);
            no_delta_steps = (uu___109_1081.no_delta_steps);
            unfold_until = (uu___109_1081.unfold_until);
            unfold_only = (uu___109_1081.unfold_only);
            unfold_attr = (uu___109_1081.unfold_attr);
            unfold_tac = (uu___109_1081.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1081.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___109_1081.erase_universes);
            allow_unbound_universes = (uu___109_1081.allow_unbound_universes);
            reify_ = (uu___109_1081.reify_);
            compress_uvars = (uu___109_1081.compress_uvars);
            no_full_norm = (uu___109_1081.no_full_norm);
            check_no_uvars = (uu___109_1081.check_no_uvars);
            unmeta = (uu___109_1081.unmeta);
            unascribe = (uu___109_1081.unascribe)
          }
      | EraseUniverses  ->
          let uu___110_1082 = fs  in
          {
            beta = (uu___110_1082.beta);
            iota = (uu___110_1082.iota);
            zeta = (uu___110_1082.zeta);
            weak = (uu___110_1082.weak);
            hnf = (uu___110_1082.hnf);
            primops = (uu___110_1082.primops);
            no_delta_steps = (uu___110_1082.no_delta_steps);
            unfold_until = (uu___110_1082.unfold_until);
            unfold_only = (uu___110_1082.unfold_only);
            unfold_attr = (uu___110_1082.unfold_attr);
            unfold_tac = (uu___110_1082.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_1082.pure_subterms_within_computations);
            simplify = (uu___110_1082.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___110_1082.allow_unbound_universes);
            reify_ = (uu___110_1082.reify_);
            compress_uvars = (uu___110_1082.compress_uvars);
            no_full_norm = (uu___110_1082.no_full_norm);
            check_no_uvars = (uu___110_1082.check_no_uvars);
            unmeta = (uu___110_1082.unmeta);
            unascribe = (uu___110_1082.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___111_1083 = fs  in
          {
            beta = (uu___111_1083.beta);
            iota = (uu___111_1083.iota);
            zeta = (uu___111_1083.zeta);
            weak = (uu___111_1083.weak);
            hnf = (uu___111_1083.hnf);
            primops = (uu___111_1083.primops);
            no_delta_steps = (uu___111_1083.no_delta_steps);
            unfold_until = (uu___111_1083.unfold_until);
            unfold_only = (uu___111_1083.unfold_only);
            unfold_attr = (uu___111_1083.unfold_attr);
            unfold_tac = (uu___111_1083.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1083.pure_subterms_within_computations);
            simplify = (uu___111_1083.simplify);
            erase_universes = (uu___111_1083.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___111_1083.reify_);
            compress_uvars = (uu___111_1083.compress_uvars);
            no_full_norm = (uu___111_1083.no_full_norm);
            check_no_uvars = (uu___111_1083.check_no_uvars);
            unmeta = (uu___111_1083.unmeta);
            unascribe = (uu___111_1083.unascribe)
          }
      | Reify  ->
          let uu___112_1084 = fs  in
          {
            beta = (uu___112_1084.beta);
            iota = (uu___112_1084.iota);
            zeta = (uu___112_1084.zeta);
            weak = (uu___112_1084.weak);
            hnf = (uu___112_1084.hnf);
            primops = (uu___112_1084.primops);
            no_delta_steps = (uu___112_1084.no_delta_steps);
            unfold_until = (uu___112_1084.unfold_until);
            unfold_only = (uu___112_1084.unfold_only);
            unfold_attr = (uu___112_1084.unfold_attr);
            unfold_tac = (uu___112_1084.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1084.pure_subterms_within_computations);
            simplify = (uu___112_1084.simplify);
            erase_universes = (uu___112_1084.erase_universes);
            allow_unbound_universes = (uu___112_1084.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___112_1084.compress_uvars);
            no_full_norm = (uu___112_1084.no_full_norm);
            check_no_uvars = (uu___112_1084.check_no_uvars);
            unmeta = (uu___112_1084.unmeta);
            unascribe = (uu___112_1084.unascribe)
          }
      | CompressUvars  ->
          let uu___113_1085 = fs  in
          {
            beta = (uu___113_1085.beta);
            iota = (uu___113_1085.iota);
            zeta = (uu___113_1085.zeta);
            weak = (uu___113_1085.weak);
            hnf = (uu___113_1085.hnf);
            primops = (uu___113_1085.primops);
            no_delta_steps = (uu___113_1085.no_delta_steps);
            unfold_until = (uu___113_1085.unfold_until);
            unfold_only = (uu___113_1085.unfold_only);
            unfold_attr = (uu___113_1085.unfold_attr);
            unfold_tac = (uu___113_1085.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1085.pure_subterms_within_computations);
            simplify = (uu___113_1085.simplify);
            erase_universes = (uu___113_1085.erase_universes);
            allow_unbound_universes = (uu___113_1085.allow_unbound_universes);
            reify_ = (uu___113_1085.reify_);
            compress_uvars = true;
            no_full_norm = (uu___113_1085.no_full_norm);
            check_no_uvars = (uu___113_1085.check_no_uvars);
            unmeta = (uu___113_1085.unmeta);
            unascribe = (uu___113_1085.unascribe)
          }
      | NoFullNorm  ->
          let uu___114_1086 = fs  in
          {
            beta = (uu___114_1086.beta);
            iota = (uu___114_1086.iota);
            zeta = (uu___114_1086.zeta);
            weak = (uu___114_1086.weak);
            hnf = (uu___114_1086.hnf);
            primops = (uu___114_1086.primops);
            no_delta_steps = (uu___114_1086.no_delta_steps);
            unfold_until = (uu___114_1086.unfold_until);
            unfold_only = (uu___114_1086.unfold_only);
            unfold_attr = (uu___114_1086.unfold_attr);
            unfold_tac = (uu___114_1086.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1086.pure_subterms_within_computations);
            simplify = (uu___114_1086.simplify);
            erase_universes = (uu___114_1086.erase_universes);
            allow_unbound_universes = (uu___114_1086.allow_unbound_universes);
            reify_ = (uu___114_1086.reify_);
            compress_uvars = (uu___114_1086.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___114_1086.check_no_uvars);
            unmeta = (uu___114_1086.unmeta);
            unascribe = (uu___114_1086.unascribe)
          }
      | CheckNoUvars  ->
          let uu___115_1087 = fs  in
          {
            beta = (uu___115_1087.beta);
            iota = (uu___115_1087.iota);
            zeta = (uu___115_1087.zeta);
            weak = (uu___115_1087.weak);
            hnf = (uu___115_1087.hnf);
            primops = (uu___115_1087.primops);
            no_delta_steps = (uu___115_1087.no_delta_steps);
            unfold_until = (uu___115_1087.unfold_until);
            unfold_only = (uu___115_1087.unfold_only);
            unfold_attr = (uu___115_1087.unfold_attr);
            unfold_tac = (uu___115_1087.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1087.pure_subterms_within_computations);
            simplify = (uu___115_1087.simplify);
            erase_universes = (uu___115_1087.erase_universes);
            allow_unbound_universes = (uu___115_1087.allow_unbound_universes);
            reify_ = (uu___115_1087.reify_);
            compress_uvars = (uu___115_1087.compress_uvars);
            no_full_norm = (uu___115_1087.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___115_1087.unmeta);
            unascribe = (uu___115_1087.unascribe)
          }
      | Unmeta  ->
          let uu___116_1088 = fs  in
          {
            beta = (uu___116_1088.beta);
            iota = (uu___116_1088.iota);
            zeta = (uu___116_1088.zeta);
            weak = (uu___116_1088.weak);
            hnf = (uu___116_1088.hnf);
            primops = (uu___116_1088.primops);
            no_delta_steps = (uu___116_1088.no_delta_steps);
            unfold_until = (uu___116_1088.unfold_until);
            unfold_only = (uu___116_1088.unfold_only);
            unfold_attr = (uu___116_1088.unfold_attr);
            unfold_tac = (uu___116_1088.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1088.pure_subterms_within_computations);
            simplify = (uu___116_1088.simplify);
            erase_universes = (uu___116_1088.erase_universes);
            allow_unbound_universes = (uu___116_1088.allow_unbound_universes);
            reify_ = (uu___116_1088.reify_);
            compress_uvars = (uu___116_1088.compress_uvars);
            no_full_norm = (uu___116_1088.no_full_norm);
            check_no_uvars = (uu___116_1088.check_no_uvars);
            unmeta = true;
            unascribe = (uu___116_1088.unascribe)
          }
      | Unascribe  ->
          let uu___117_1089 = fs  in
          {
            beta = (uu___117_1089.beta);
            iota = (uu___117_1089.iota);
            zeta = (uu___117_1089.zeta);
            weak = (uu___117_1089.weak);
            hnf = (uu___117_1089.hnf);
            primops = (uu___117_1089.primops);
            no_delta_steps = (uu___117_1089.no_delta_steps);
            unfold_until = (uu___117_1089.unfold_until);
            unfold_only = (uu___117_1089.unfold_only);
            unfold_attr = (uu___117_1089.unfold_attr);
            unfold_tac = (uu___117_1089.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1089.pure_subterms_within_computations);
            simplify = (uu___117_1089.simplify);
            erase_universes = (uu___117_1089.erase_universes);
            allow_unbound_universes = (uu___117_1089.allow_unbound_universes);
            reify_ = (uu___117_1089.reify_);
            compress_uvars = (uu___117_1089.compress_uvars);
            no_full_norm = (uu___117_1089.no_full_norm);
            check_no_uvars = (uu___117_1089.check_no_uvars);
            unmeta = (uu___117_1089.unmeta);
            unascribe = true
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1128  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    }[@@deriving show]
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__auto_reflect
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
  
let (__proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
  
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy [@@deriving show]
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____1371 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1473 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1484 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___77_1503  ->
    match uu___77_1503 with
    | Clos (uu____1504,t,uu____1506,uu____1507) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1552 -> "Univ"
    | Dummy  -> "dummy"
  
type debug_switches =
  {
  gen: Prims.bool ;
  primop: Prims.bool ;
  b380: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }[@@deriving show]
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__print_normalized
  
type cfg =
  {
  steps: fsteps ;
  tcenv: FStar_TypeChecker_Env.env ;
  debug: debug_switches ;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list ;
  primitive_steps: primitive_step FStar_Util.psmap ;
  strong: Prims.bool ;
  memoize_lazy: Prims.bool ;
  normalize_pure_lets: Prims.bool }[@@deriving show]
let (__proj__Mkcfg__item__steps : cfg -> fsteps) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
  
let (__proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
  
let (__proj__Mkcfg__item__debug : cfg -> debug_switches) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__debug
  
let (__proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
  
let (__proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
  
let (__proj__Mkcfg__item__strong : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
  
let (__proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
  
let (__proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__normalize_pure_lets
  
let (add_steps :
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap)
  =
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             FStar_Util.psmap_add m1 (FStar_Ident.text_of_lid p.name) p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____1814 = FStar_Util.psmap_empty ()  in add_steps uu____1814 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      FStar_Util.psmap_try_find cfg.primitive_steps
        (FStar_Ident.text_of_lid
           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
  
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo 
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5 
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Cfg of cfg 
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____1966 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2002 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2038 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2107 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2149 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2205 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2245 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2277 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2313 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2329 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2354 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2354 with | (hd1,uu____2368) -> hd1
  
let mk :
  'Auu____2388 .
    'Auu____2388 ->
      FStar_Range.range -> 'Auu____2388 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2442 = FStar_ST.op_Bang r  in
          match uu____2442 with
          | FStar_Pervasives_Native.Some uu____2490 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2544 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2544 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___78_2551  ->
    match uu___78_2551 with
    | Arg (c,uu____2553,uu____2554) ->
        let uu____2555 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2555
    | MemoLazy uu____2556 -> "MemoLazy"
    | Abs (uu____2563,bs,uu____2565,uu____2566,uu____2567) ->
        let uu____2572 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2572
    | UnivArgs uu____2577 -> "UnivArgs"
    | Match uu____2584 -> "Match"
    | App (uu____2591,t,uu____2593,uu____2594) ->
        let uu____2595 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2595
    | Meta (m,uu____2597) -> "Meta"
    | Let uu____2598 -> "Let"
    | Cfg uu____2607 -> "Cfg"
    | Debug (t,uu____2609) ->
        let uu____2610 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2610
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2618 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2618 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2649 . 'Auu____2649 Prims.list -> Prims.bool =
  fun uu___79_2655  ->
    match uu___79_2655 with | [] -> true | uu____2658 -> false
  
let lookup_bvar :
  'Auu____2665 'Auu____2666 .
    ('Auu____2665,'Auu____2666) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2666
  =
  fun env  ->
    fun x  ->
      try
        let uu____2690 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2690
      with
      | uu____2703 ->
          let uu____2704 =
            let uu____2705 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2705  in
          failwith uu____2704
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
  
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____2742 =
            FStar_List.fold_left
              (fun uu____2768  ->
                 fun u1  ->
                   match uu____2768 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2793 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2793 with
                        | (k_u,n1) ->
                            let uu____2808 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2808
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2742 with
          | (uu____2826,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2851 =
                   let uu____2852 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2852  in
                 match uu____2851 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2870 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2878 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2884 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2893 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2902 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2909 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2909 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2926 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2926 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2934 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2942 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2942 with
                                  | (uu____2947,m) -> n1 <= m))
                           in
                        if uu____2934 then rest1 else us1
                    | uu____2952 -> us1)
               | uu____2957 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2961 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2961
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2965 = aux u  in
           match uu____2965 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____3069  ->
             let uu____3070 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3071 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3070
               uu____3071);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3078 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3080 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3105 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3106 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3107 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3108 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3109 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3126 =
                      let uu____3127 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3128 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3127 uu____3128
                       in
                    failwith uu____3126
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3131 =
                    let uu____3132 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3132  in
                  mk uu____3131 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3139 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3139
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3141 = lookup_bvar env x  in
                  (match uu____3141 with
                   | Univ uu____3144 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3147,uu____3148) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3260 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3260 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3288 =
                         let uu____3289 =
                           let uu____3306 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3306)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3289  in
                       mk uu____3288 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3337 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3337 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3379 =
                    let uu____3390 =
                      let uu____3397 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3397]  in
                    closures_as_binders_delayed cfg env uu____3390  in
                  (match uu____3379 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3415 =
                         let uu____3416 =
                           let uu____3423 =
                             let uu____3424 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3424
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3423, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3416  in
                       mk uu____3415 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3515 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3515
                    | FStar_Util.Inr c ->
                        let uu____3529 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3529
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3545 =
                    let uu____3546 =
                      let uu____3573 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3573, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3546  in
                  mk uu____3545 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3624 =
                    let uu____3625 =
                      let uu____3632 = closure_as_term_delayed cfg env t'  in
                      let uu____3635 =
                        let uu____3636 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3636  in
                      (uu____3632, uu____3635)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3625  in
                  mk uu____3624 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3696 =
                    let uu____3697 =
                      let uu____3704 = closure_as_term_delayed cfg env t'  in
                      let uu____3707 =
                        let uu____3708 =
                          let uu____3715 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3715)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3708  in
                      (uu____3704, uu____3707)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3697  in
                  mk uu____3696 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3734 =
                    let uu____3735 =
                      let uu____3742 = closure_as_term_delayed cfg env t'  in
                      let uu____3745 =
                        let uu____3746 =
                          let uu____3755 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3755)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3746  in
                      (uu____3742, uu____3745)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3735  in
                  mk uu____3734 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_quoted (t'',qi)) ->
                  if qi.FStar_Syntax_Syntax.qopen
                  then
                    let uu____3773 =
                      let uu____3774 =
                        let uu____3781 = closure_as_term_delayed cfg env t'
                           in
                        let uu____3784 =
                          let uu____3785 =
                            let uu____3792 =
                              closure_as_term_delayed cfg env t''  in
                            (uu____3792, qi)  in
                          FStar_Syntax_Syntax.Meta_quoted uu____3785  in
                        (uu____3781, uu____3784)  in
                      FStar_Syntax_Syntax.Tm_meta uu____3774  in
                    mk uu____3773 t1.FStar_Syntax_Syntax.pos
                  else
                    (let uu____3800 =
                       let uu____3801 =
                         let uu____3808 = closure_as_term_delayed cfg env t'
                            in
                         (uu____3808,
                           (FStar_Syntax_Syntax.Meta_quoted (t'', qi)))
                          in
                       FStar_Syntax_Syntax.Tm_meta uu____3801  in
                     mk uu____3800 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3821 =
                    let uu____3822 =
                      let uu____3829 = closure_as_term_delayed cfg env t'  in
                      (uu____3829, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3822  in
                  mk uu____3821 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3869  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3888 =
                    let uu____3899 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3899
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3918 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___122_3930 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___122_3930.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___122_3930.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3918))
                     in
                  (match uu____3888 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___123_3946 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___123_3946.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___123_3946.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___123_3946.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___123_3946.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3957,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4016  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4041 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4041
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4061  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4083 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4083
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___124_4095 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_4095.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_4095.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___125_4096 = lb  in
                    let uu____4097 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_4096.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_4096.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4097;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___125_4096.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___125_4096.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4127  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4216 =
                    match uu____4216 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4271 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4292 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4352  ->
                                        fun uu____4353  ->
                                          match (uu____4352, uu____4353) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4444 =
                                                norm_pat env3 p1  in
                                              (match uu____4444 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4292 with
                               | (pats1,env3) ->
                                   ((let uu___126_4526 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___126_4526.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___127_4545 = x  in
                                let uu____4546 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___127_4545.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___127_4545.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4546
                                }  in
                              ((let uu___128_4560 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___128_4560.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___129_4571 = x  in
                                let uu____4572 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4571.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4571.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4572
                                }  in
                              ((let uu___130_4586 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4586.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___131_4602 = x  in
                                let uu____4603 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4602.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4602.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4603
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___132_4610 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4610.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4613 = norm_pat env1 pat  in
                        (match uu____4613 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4642 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4642
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4648 =
                    let uu____4649 =
                      let uu____4672 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4672)  in
                    FStar_Syntax_Syntax.Tm_match uu____4649  in
                  mk uu____4648 t1.FStar_Syntax_Syntax.pos))

and (closure_as_term_delayed :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> t
        | uu____4758 -> closure_as_term cfg env t

and (closures_as_args_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> args
        | uu____4784 ->
            FStar_List.map
              (fun uu____4801  ->
                 match uu____4801 with
                 | (x,imp) ->
                     let uu____4820 = closure_as_term_delayed cfg env x  in
                     (uu____4820, imp)) args

and (closures_as_binders_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____4834 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4883  ->
                  fun uu____4884  ->
                    match (uu____4883, uu____4884) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___133_4954 = b  in
                          let uu____4955 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___133_4954.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___133_4954.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4955
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4834 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and (close_comp :
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> c
        | uu____5048 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5061 = closure_as_term_delayed cfg env t  in
                 let uu____5062 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5061 uu____5062
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5075 = closure_as_term_delayed cfg env t  in
                 let uu____5076 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5075 uu____5076
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___80_5102  ->
                           match uu___80_5102 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5106 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5106
                           | f -> f))
                    in
                 let uu____5110 =
                   let uu___134_5111 = c1  in
                   let uu____5112 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5112;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___134_5111.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5110)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___81_5122  ->
            match uu___81_5122 with
            | FStar_Syntax_Syntax.DECREASES uu____5123 -> false
            | uu____5126 -> true))

and (close_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___82_5144  ->
                      match uu___82_5144 with
                      | FStar_Syntax_Syntax.DECREASES uu____5145 -> false
                      | uu____5148 -> true))
               in
            let rc1 =
              let uu___135_5150 = rc  in
              let uu____5151 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___135_5150.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5151;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5158 -> lopt

let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe
     in
  let arg_as_list a u a =
    let uu____5243 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5243  in
  let arg_as_bounded_int uu____5271 =
    match uu____5271 with
    | (a,uu____5283) ->
        let uu____5290 =
          let uu____5291 = FStar_Syntax_Subst.compress a  in
          uu____5291.FStar_Syntax_Syntax.n  in
        (match uu____5290 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5301;
                FStar_Syntax_Syntax.vars = uu____5302;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5304;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5305;_},uu____5306)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5353 =
               let uu____5358 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5358)  in
             FStar_Pervasives_Native.Some uu____5353
         | uu____5363 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5403 = f a  in FStar_Pervasives_Native.Some uu____5403
    | uu____5404 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5452 = f a0 a1  in FStar_Pervasives_Native.Some uu____5452
    | uu____5453 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5495 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5495)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5544 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5544)) a423 a424 a425 a426 a427
     in
  let as_primitive_step is_strong uu____5571 =
    match uu____5571 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          auto_reflect = FStar_Pervasives_Native.None;
          strong_reduction_ok = is_strong;
          requires_binder_substitution = false;
          interpretation = f
        }
     in
  let unary_int_op f =
    unary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5619 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5619)) a429 a430)
     in
  let binary_int_op f =
    binary_op () (fun a431  -> (Obj.magic arg_as_int) a431)
      (fun a432  ->
         fun a433  ->
           fun a434  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5647 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5647)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5668 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5668)) a436
             a437)
     in
  let binary_bool_op f =
    binary_op () (fun a438  -> (Obj.magic arg_as_bool) a438)
      (fun a439  ->
         fun a440  ->
           fun a441  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5696 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5696)) a439
               a440 a441)
     in
  let binary_string_op f =
    binary_op () (fun a442  -> (Obj.magic arg_as_string) a442)
      (fun a443  ->
         fun a444  ->
           fun a445  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5724 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5724))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5832 =
          let uu____5841 = as_a a  in
          let uu____5844 = as_b b  in (uu____5841, uu____5844)  in
        (match uu____5832 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5859 =
               let uu____5860 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5860  in
             FStar_Pervasives_Native.Some uu____5859
         | uu____5861 -> FStar_Pervasives_Native.None)
    | uu____5870 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5884 =
        let uu____5885 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5885  in
      mk uu____5884 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5895 =
      let uu____5898 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5898  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5895  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5930 =
      let uu____5931 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5931  in
    FStar_Syntax_Embeddings.embed_int rng uu____5930  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5949 = arg_as_string a1  in
        (match uu____5949 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5955 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5955 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5968 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5968
              | uu____5969 -> FStar_Pervasives_Native.None)
         | uu____5974 -> FStar_Pervasives_Native.None)
    | uu____5977 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5987 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5987  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6016 =
          let uu____6037 = arg_as_string fn  in
          let uu____6040 = arg_as_int from_line  in
          let uu____6043 = arg_as_int from_col  in
          let uu____6046 = arg_as_int to_line  in
          let uu____6049 = arg_as_int to_col  in
          (uu____6037, uu____6040, uu____6043, uu____6046, uu____6049)  in
        (match uu____6016 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6080 =
                 let uu____6081 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6082 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6081 uu____6082  in
               let uu____6083 =
                 let uu____6084 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6085 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6084 uu____6085  in
               FStar_Range.mk_range fn1 uu____6080 uu____6083  in
             let uu____6086 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6086
         | uu____6087 -> FStar_Pervasives_Native.None)
    | uu____6108 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6135)::(a1,uu____6137)::(a2,uu____6139)::[] ->
        let uu____6176 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6176 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6189 -> FStar_Pervasives_Native.None)
    | uu____6190 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6217)::[] ->
        let uu____6226 = FStar_Syntax_Embeddings.unembed_range_safe a1  in
        (match uu____6226 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6232 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6232
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6233 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6257 =
      let uu____6272 =
        let uu____6287 =
          let uu____6302 =
            let uu____6317 =
              let uu____6332 =
                let uu____6347 =
                  let uu____6362 =
                    let uu____6377 =
                      let uu____6392 =
                        let uu____6407 =
                          let uu____6422 =
                            let uu____6437 =
                              let uu____6452 =
                                let uu____6467 =
                                  let uu____6482 =
                                    let uu____6497 =
                                      let uu____6512 =
                                        let uu____6527 =
                                          let uu____6542 =
                                            let uu____6557 =
                                              let uu____6572 =
                                                let uu____6585 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6585,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a446  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a446)
                                                     (fun a447  ->
                                                        fun a448  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a447 a448)))
                                                 in
                                              let uu____6592 =
                                                let uu____6607 =
                                                  let uu____6620 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6620,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a449  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a449)
                                                       (fun a450  ->
                                                          fun a451  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a450 a451)))
                                                   in
                                                let uu____6627 =
                                                  let uu____6642 =
                                                    let uu____6657 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6657,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6666 =
                                                    let uu____6683 =
                                                      let uu____6698 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6698,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____6683]  in
                                                  uu____6642 :: uu____6666
                                                   in
                                                uu____6607 :: uu____6627  in
                                              uu____6572 :: uu____6592  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6557
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6542
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a452  ->
                                                (Obj.magic arg_as_string)
                                                  a452)
                                             (fun a453  ->
                                                fun a454  ->
                                                  fun a455  ->
                                                    (Obj.magic
                                                       string_compare') a453
                                                      a454 a455)))
                                          :: uu____6527
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456  ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457  ->
                                              fun a458  ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____6512
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459  ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460  ->
                                            fun a461  ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____6497
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a462  ->
                                          (Obj.magic arg_as_int) a462)
                                       (fun a463  ->
                                          (Obj.magic arg_as_char) a463)
                                       (fun a464  ->
                                          fun a465  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a464 a465)
                                       (fun a466  ->
                                          fun a467  ->
                                            fun a468  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____6889 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6889 y)) a466
                                                a467 a468)))
                                    :: uu____6482
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6467
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6452
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6437
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6422
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6407
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6392
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a469  -> (Obj.magic arg_as_int) a469)
                         (fun a470  ->
                            fun a471  ->
                              fun a472  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7056 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7056)) a470 a471 a472)))
                      :: uu____6377
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473  -> (Obj.magic arg_as_int) a473)
                       (fun a474  ->
                          fun a475  ->
                            fun a476  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7082 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7082)) a474 a475 a476)))
                    :: uu____6362
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477  -> (Obj.magic arg_as_int) a477)
                     (fun a478  ->
                        fun a479  ->
                          fun a480  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7108 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7108)) a478 a479 a480)))
                  :: uu____6347
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481  -> (Obj.magic arg_as_int) a481)
                   (fun a482  ->
                      fun a483  ->
                        fun a484  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7134 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7134)) a482 a483 a484)))
                :: uu____6332
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6317
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6302
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6287
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6272
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6257
     in
  let weak_ops =
    let uu____7273 =
      let uu____7292 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7292, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7273]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7376 =
        let uu____7377 =
          let uu____7378 = FStar_Syntax_Syntax.as_arg c  in [uu____7378]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7377  in
      uu____7376 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7428 =
                let uu____7441 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7441, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7457  ->
                                    fun uu____7458  ->
                                      match (uu____7457, uu____7458) with
                                      | ((int_to_t1,x),(uu____7477,y)) ->
                                          let uu____7487 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7487)) a486 a487 a488)))
                 in
              let uu____7488 =
                let uu____7503 =
                  let uu____7516 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7516, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7532  ->
                                      fun uu____7533  ->
                                        match (uu____7532, uu____7533) with
                                        | ((int_to_t1,x),(uu____7552,y)) ->
                                            let uu____7562 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7562)) a490 a491 a492)))
                   in
                let uu____7563 =
                  let uu____7578 =
                    let uu____7591 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7591, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7607  ->
                                        fun uu____7608  ->
                                          match (uu____7607, uu____7608) with
                                          | ((int_to_t1,x),(uu____7627,y)) ->
                                              let uu____7637 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7637)) a494 a495 a496)))
                     in
                  let uu____7638 =
                    let uu____7653 =
                      let uu____7666 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7666, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7678  ->
                                        match uu____7678 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7653]  in
                  uu____7578 :: uu____7638  in
                uu____7503 :: uu____7563  in
              uu____7428 :: uu____7488))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7792 =
                let uu____7805 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7805, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7821  ->
                                    fun uu____7822  ->
                                      match (uu____7821, uu____7822) with
                                      | ((int_to_t1,x),(uu____7841,y)) ->
                                          let uu____7851 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7851)) a501 a502 a503)))
                 in
              let uu____7852 =
                let uu____7867 =
                  let uu____7880 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7880, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7896  ->
                                      fun uu____7897  ->
                                        match (uu____7896, uu____7897) with
                                        | ((int_to_t1,x),(uu____7916,y)) ->
                                            let uu____7926 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7926)) a505 a506 a507)))
                   in
                [uu____7867]  in
              uu____7792 :: uu____7852))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops  in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
  
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____8038)::(a1,uu____8040)::(a2,uu____8042)::[] ->
        let uu____8079 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8079 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8085 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8085.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8085.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8089 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8089.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8089.FStar_Syntax_Syntax.vars)
                })
         | uu____8090 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8092)::uu____8093::(a1,uu____8095)::(a2,uu____8097)::[] ->
        let uu____8146 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8146 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8152 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8152.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8152.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8156 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8156.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8156.FStar_Syntax_Syntax.vars)
                })
         | uu____8157 -> FStar_Pervasives_Native.None)
    | uu____8158 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.unembedder
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8210 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8210 with
    | FStar_Pervasives_Native.Some f -> f t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8257 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8257) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8317  ->
           fun subst1  ->
             match uu____8317 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8358,uu____8359)) ->
                      let uu____8418 = b  in
                      (match uu____8418 with
                       | (bv,uu____8426) ->
                           let uu____8427 =
                             let uu____8428 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8428  in
                           if uu____8427
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8433 = unembed_binder term1  in
                              match uu____8433 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8440 =
                                      let uu___138_8441 = bv  in
                                      let uu____8442 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___138_8441.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___138_8441.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8442
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8440
                                     in
                                  let b_for_x =
                                    let uu____8446 =
                                      let uu____8453 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8453)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8446  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___83_8462  ->
                                         match uu___83_8462 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8463,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8465;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8466;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8475 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8476 -> subst1)) env []
  
let reduce_primops :
  'Auu____8493 'Auu____8494 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8493) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8494 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8536 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8536 with
             | (head1,args) ->
                 let uu____8573 =
                   let uu____8574 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8574.FStar_Syntax_Syntax.n  in
                 (match uu____8573 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8578 = find_prim_step cfg fv  in
                      (match uu____8578 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8593  ->
                                   let uu____8594 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8595 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8602 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8594 uu____8595 uu____8602);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8607  ->
                                   let uu____8608 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8608);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8611  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8613 =
                                 prim_step.interpretation psc args  in
                               match uu____8613 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8619  ->
                                         let uu____8620 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8620);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8626  ->
                                         let uu____8627 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8628 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8627 uu____8628);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8629 ->
                           (log_primops cfg
                              (fun uu____8633  ->
                                 let uu____8634 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8634);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8638  ->
                            let uu____8639 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8639);
                       (match args with
                        | (a1,uu____8641)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8658 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8670  ->
                            let uu____8671 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8671);
                       (match args with
                        | (t,uu____8673)::(r,uu____8675)::[] ->
                            let uu____8702 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8702 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___139_8706 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___139_8706.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___139_8706.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8709 -> tm))
                  | uu____8718 -> tm))
  
let reduce_equality :
  'Auu____8723 'Auu____8724 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8723) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8724 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___140_8762 = cfg  in
         {
           steps =
             (let uu___141_8765 = default_steps  in
              {
                beta = (uu___141_8765.beta);
                iota = (uu___141_8765.iota);
                zeta = (uu___141_8765.zeta);
                weak = (uu___141_8765.weak);
                hnf = (uu___141_8765.hnf);
                primops = true;
                no_delta_steps = (uu___141_8765.no_delta_steps);
                unfold_until = (uu___141_8765.unfold_until);
                unfold_only = (uu___141_8765.unfold_only);
                unfold_attr = (uu___141_8765.unfold_attr);
                unfold_tac = (uu___141_8765.unfold_tac);
                pure_subterms_within_computations =
                  (uu___141_8765.pure_subterms_within_computations);
                simplify = (uu___141_8765.simplify);
                erase_universes = (uu___141_8765.erase_universes);
                allow_unbound_universes =
                  (uu___141_8765.allow_unbound_universes);
                reify_ = (uu___141_8765.reify_);
                compress_uvars = (uu___141_8765.compress_uvars);
                no_full_norm = (uu___141_8765.no_full_norm);
                check_no_uvars = (uu___141_8765.check_no_uvars);
                unmeta = (uu___141_8765.unmeta);
                unascribe = (uu___141_8765.unascribe)
              });
           tcenv = (uu___140_8762.tcenv);
           debug = (uu___140_8762.debug);
           delta_level = (uu___140_8762.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___140_8762.strong);
           memoize_lazy = (uu___140_8762.memoize_lazy);
           normalize_pure_lets = (uu___140_8762.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____8772 'Auu____8773 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8772) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8773 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____8815 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____8815
          then tm1
          else
            (let w t =
               let uu___142_8827 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___142_8827.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___142_8827.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8843;
                      FStar_Syntax_Syntax.vars = uu____8844;_},uu____8845)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8856;
                      FStar_Syntax_Syntax.vars = uu____8857;_},uu____8858)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8868 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____8873 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____8873
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8894 =
                 match uu____8894 with
                 | (t1,q) ->
                     let uu____8907 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____8907 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8935 -> (t1, q))
                  in
               let uu____8944 = FStar_Syntax_Util.head_and_args t  in
               match uu____8944 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg)  in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____9041;
                         FStar_Syntax_Syntax.vars = uu____9042;_},uu____9043);
                    FStar_Syntax_Syntax.pos = uu____9044;
                    FStar_Syntax_Syntax.vars = uu____9045;_},args)
                 ->
                 let uu____9079 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____9079
                 then
                   let uu____9080 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____9080 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9135)::
                        (uu____9136,(arg,uu____9138))::[] ->
                        maybe_auto_squash arg
                    | (uu____9203,(arg,uu____9205))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9206)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9271)::uu____9272::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9335::(FStar_Pervasives_Native.Some (false
                                   ),uu____9336)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9399 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9415 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9415
                    then
                      let uu____9416 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9416 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9471)::uu____9472::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9535::(FStar_Pervasives_Native.Some (true
                                     ),uu____9536)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9599)::
                          (uu____9600,(arg,uu____9602))::[] ->
                          maybe_auto_squash arg
                      | (uu____9667,(arg,uu____9669))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9670)::[]
                          -> maybe_auto_squash arg
                      | uu____9735 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9751 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9751
                       then
                         let uu____9752 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9752 with
                         | uu____9807::(FStar_Pervasives_Native.Some (true
                                        ),uu____9808)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9871)::uu____9872::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9935)::
                             (uu____9936,(arg,uu____9938))::[] ->
                             maybe_auto_squash arg
                         | (uu____10003,(p,uu____10005))::(uu____10006,
                                                           (q,uu____10008))::[]
                             ->
                             let uu____10073 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____10073
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10075 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10091 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.iff_lid
                             in
                          if uu____10091
                          then
                            let uu____10092 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____10092 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10147)::(FStar_Pervasives_Native.Some
                                                (true ),uu____10148)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10213)::(FStar_Pervasives_Native.Some
                                                (false ),uu____10214)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10279)::(FStar_Pervasives_Native.Some
                                                (false ),uu____10280)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10345)::(FStar_Pervasives_Native.Some
                                                (true ),uu____10346)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (uu____10411,(arg,uu____10413))::(FStar_Pervasives_Native.Some
                                                                (true
                                                                ),uu____10414)::[]
                                -> maybe_auto_squash arg
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10479)::(uu____10480,(arg,uu____10482))::[]
                                -> maybe_auto_squash arg
                            | (uu____10547,(p,uu____10549))::(uu____10550,
                                                              (q,uu____10552))::[]
                                ->
                                let uu____10617 =
                                  FStar_Syntax_Util.term_eq p q  in
                                (if uu____10617
                                 then w FStar_Syntax_Util.t_true
                                 else squashed_head_un_auto_squash_args tm1)
                            | uu____10619 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10635 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.not_lid
                                in
                             if uu____10635
                             then
                               let uu____10636 =
                                 FStar_All.pipe_right args
                                   (FStar_List.map simplify1)
                                  in
                               match uu____10636 with
                               | (FStar_Pervasives_Native.Some (true
                                  ),uu____10691)::[] ->
                                   w FStar_Syntax_Util.t_false
                               | (FStar_Pervasives_Native.Some (false
                                  ),uu____10730)::[] ->
                                   w FStar_Syntax_Util.t_true
                               | uu____10769 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu____10785 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.forall_lid
                                   in
                                if uu____10785
                                then
                                  match args with
                                  | (t,uu____10787)::[] ->
                                      let uu____10804 =
                                        let uu____10805 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10805.FStar_Syntax_Syntax.n  in
                                      (match uu____10804 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10808::[],body,uu____10810)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____10837 -> tm1)
                                       | uu____10840 -> tm1)
                                  | (uu____10841,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10842))::(t,uu____10844)::[] ->
                                      let uu____10883 =
                                        let uu____10884 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10884.FStar_Syntax_Syntax.n  in
                                      (match uu____10883 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10887::[],body,uu____10889)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____10916 -> tm1)
                                       | uu____10919 -> tm1)
                                  | uu____10920 -> tm1
                                else
                                  (let uu____10930 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.exists_lid
                                      in
                                   if uu____10930
                                   then
                                     match args with
                                     | (t,uu____10932)::[] ->
                                         let uu____10949 =
                                           let uu____10950 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10950.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____10949 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____10953::[],body,uu____10955)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____10982 -> tm1)
                                          | uu____10985 -> tm1)
                                     | (uu____10986,FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit
                                        uu____10987))::(t,uu____10989)::[] ->
                                         let uu____11028 =
                                           let uu____11029 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____11029.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____11028 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____11032::[],body,uu____11034)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____11061 -> tm1)
                                          | uu____11064 -> tm1)
                                     | uu____11065 -> tm1
                                   else
                                     (let uu____11075 =
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.b2t_lid
                                         in
                                      if uu____11075
                                      then
                                        match args with
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (true
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____11076;
                                             FStar_Syntax_Syntax.vars =
                                               uu____11077;_},uu____11078)::[]
                                            -> w FStar_Syntax_Util.t_true
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (false
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____11099;
                                             FStar_Syntax_Syntax.vars =
                                               uu____11100;_},uu____11101)::[]
                                            -> w FStar_Syntax_Util.t_false
                                        | uu____11122 -> tm1
                                      else
                                        (let uu____11132 =
                                           FStar_Syntax_Util.is_auto_squash
                                             tm1
                                            in
                                         match uu____11132 with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.U_zero ,t)
                                             when
                                             FStar_Syntax_Util.is_sub_singleton
                                               t
                                             -> t
                                         | uu____11152 ->
                                             reduce_equality cfg env stack
                                               tm1))))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____11162;
                    FStar_Syntax_Syntax.vars = uu____11163;_},args)
                 ->
                 let uu____11189 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____11189
                 then
                   let uu____11190 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____11190 with
                    | (FStar_Pervasives_Native.Some (true ),uu____11245)::
                        (uu____11246,(arg,uu____11248))::[] ->
                        maybe_auto_squash arg
                    | (uu____11313,(arg,uu____11315))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____11316)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____11381)::uu____11382::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____11445::(FStar_Pervasives_Native.Some (false
                                    ),uu____11446)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____11509 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____11525 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____11525
                    then
                      let uu____11526 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____11526 with
                      | (FStar_Pervasives_Native.Some (true ),uu____11581)::uu____11582::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____11645::(FStar_Pervasives_Native.Some (true
                                      ),uu____11646)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____11709)::
                          (uu____11710,(arg,uu____11712))::[] ->
                          maybe_auto_squash arg
                      | (uu____11777,(arg,uu____11779))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____11780)::[]
                          -> maybe_auto_squash arg
                      | uu____11845 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11861 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____11861
                       then
                         let uu____11862 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____11862 with
                         | uu____11917::(FStar_Pervasives_Native.Some (true
                                         ),uu____11918)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11981)::uu____11982::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____12045)::
                             (uu____12046,(arg,uu____12048))::[] ->
                             maybe_auto_squash arg
                         | (uu____12113,(p,uu____12115))::(uu____12116,
                                                           (q,uu____12118))::[]
                             ->
                             let uu____12183 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____12183
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____12185 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____12201 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.iff_lid
                             in
                          if uu____12201
                          then
                            let uu____12202 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____12202 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12257)::(FStar_Pervasives_Native.Some
                                                (true ),uu____12258)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____12323)::(FStar_Pervasives_Native.Some
                                                (false ),uu____12324)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12389)::(FStar_Pervasives_Native.Some
                                                (false ),uu____12390)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____12455)::(FStar_Pervasives_Native.Some
                                                (true ),uu____12456)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (uu____12521,(arg,uu____12523))::(FStar_Pervasives_Native.Some
                                                                (true
                                                                ),uu____12524)::[]
                                -> maybe_auto_squash arg
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12589)::(uu____12590,(arg,uu____12592))::[]
                                -> maybe_auto_squash arg
                            | (uu____12657,(p,uu____12659))::(uu____12660,
                                                              (q,uu____12662))::[]
                                ->
                                let uu____12727 =
                                  FStar_Syntax_Util.term_eq p q  in
                                (if uu____12727
                                 then w FStar_Syntax_Util.t_true
                                 else squashed_head_un_auto_squash_args tm1)
                            | uu____12729 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____12745 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.not_lid
                                in
                             if uu____12745
                             then
                               let uu____12746 =
                                 FStar_All.pipe_right args
                                   (FStar_List.map simplify1)
                                  in
                               match uu____12746 with
                               | (FStar_Pervasives_Native.Some (true
                                  ),uu____12801)::[] ->
                                   w FStar_Syntax_Util.t_false
                               | (FStar_Pervasives_Native.Some (false
                                  ),uu____12840)::[] ->
                                   w FStar_Syntax_Util.t_true
                               | uu____12879 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu____12895 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.forall_lid
                                   in
                                if uu____12895
                                then
                                  match args with
                                  | (t,uu____12897)::[] ->
                                      let uu____12914 =
                                        let uu____12915 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____12915.FStar_Syntax_Syntax.n  in
                                      (match uu____12914 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____12918::[],body,uu____12920)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____12947 -> tm1)
                                       | uu____12950 -> tm1)
                                  | (uu____12951,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____12952))::(t,uu____12954)::[] ->
                                      let uu____12993 =
                                        let uu____12994 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____12994.FStar_Syntax_Syntax.n  in
                                      (match uu____12993 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____12997::[],body,uu____12999)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____13026 -> tm1)
                                       | uu____13029 -> tm1)
                                  | uu____13030 -> tm1
                                else
                                  (let uu____13040 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.exists_lid
                                      in
                                   if uu____13040
                                   then
                                     match args with
                                     | (t,uu____13042)::[] ->
                                         let uu____13059 =
                                           let uu____13060 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____13060.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____13059 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____13063::[],body,uu____13065)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____13092 -> tm1)
                                          | uu____13095 -> tm1)
                                     | (uu____13096,FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit
                                        uu____13097))::(t,uu____13099)::[] ->
                                         let uu____13138 =
                                           let uu____13139 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____13139.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____13138 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____13142::[],body,uu____13144)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____13171 -> tm1)
                                          | uu____13174 -> tm1)
                                     | uu____13175 -> tm1
                                   else
                                     (let uu____13185 =
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.b2t_lid
                                         in
                                      if uu____13185
                                      then
                                        match args with
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (true
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____13186;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13187;_},uu____13188)::[]
                                            -> w FStar_Syntax_Util.t_true
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (false
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____13209;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13210;_},uu____13211)::[]
                                            -> w FStar_Syntax_Util.t_false
                                        | uu____13232 -> tm1
                                      else
                                        (let uu____13242 =
                                           FStar_Syntax_Util.is_auto_squash
                                             tm1
                                            in
                                         match uu____13242 with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.U_zero ,t)
                                             when
                                             FStar_Syntax_Util.is_sub_singleton
                                               t
                                             -> t
                                         | uu____13262 ->
                                             reduce_equality cfg env stack
                                               tm1))))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____13277 -> tm1)
  
let maybe_simplify :
  'Auu____13284 'Auu____13285 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____13284) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____13285 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____13328 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13329 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____13328
               uu____13329)
          else ();
          tm'
  
let is_norm_request :
  'Auu____13335 .
    FStar_Syntax_Syntax.term -> 'Auu____13335 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____13348 =
        let uu____13355 =
          let uu____13356 = FStar_Syntax_Util.un_uinst hd1  in
          uu____13356.FStar_Syntax_Syntax.n  in
        (uu____13355, args)  in
      match uu____13348 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____13362::uu____13363::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____13367::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____13372::uu____13373::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____13376 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___84_13387  ->
    match uu___84_13387 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____13393 =
          let uu____13396 =
            let uu____13397 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____13397  in
          [uu____13396]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____13393
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____13413 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____13413) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____13466 =
            let uu____13469 =
              let uu____13472 =
                let uu____13477 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____13477 s  in
              FStar_All.pipe_right uu____13472 FStar_Util.must  in
            FStar_All.pipe_right uu____13469 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____13466
        with | uu____13505 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____13516::(tm,uu____13518)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____13547)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____13568)::uu____13569::(tm,uu____13571)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____13608 =
            let uu____13613 = full_norm steps  in parse_steps uu____13613  in
          (match uu____13608 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____13652 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___85_13669  ->
    match uu___85_13669 with
    | (App
        (uu____13672,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____13673;
                       FStar_Syntax_Syntax.vars = uu____13674;_},uu____13675,uu____13676))::uu____13677
        -> true
    | uu____13688 -> false
  
let firstn :
  'Auu____13694 .
    Prims.int ->
      'Auu____13694 Prims.list ->
        ('Auu____13694 Prims.list,'Auu____13694 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify : cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____13730,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____13731;
                         FStar_Syntax_Syntax.vars = uu____13732;_},uu____13733,uu____13734))::uu____13735
          -> (cfg.steps).reify_
      | uu____13746 -> false
  
let rec (norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            if (cfg.debug).norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____13890 ->
                   let uu____13915 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13915
               | uu____13916 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13924  ->
               let uu____13925 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13926 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13927 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13934 =
                 let uu____13935 =
                   let uu____13938 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13938
                    in
                 stack_to_string uu____13935  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13925 uu____13926 uu____13927 uu____13934);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____13961 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____13962 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____13963 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13964;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____13965;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13968;
                 FStar_Syntax_Syntax.fv_delta = uu____13969;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13970;
                 FStar_Syntax_Syntax.fv_delta = uu____13971;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13972);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_meta
               (t0,FStar_Syntax_Syntax.Meta_quoted (t11,qi)) ->
               let t01 = closure_as_term cfg env t0  in
               let t12 =
                 if qi.FStar_Syntax_Syntax.qopen
                 then closure_as_term cfg env t11
                 else t11  in
               let t2 =
                 let uu___145_13996 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_meta
                        (t01, (FStar_Syntax_Syntax.Meta_quoted (t12, qi))));
                   FStar_Syntax_Syntax.pos =
                     (uu___145_13996.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___145_13996.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___146_14026 = cfg  in
                 {
                   steps =
                     (let uu___147_14029 = cfg.steps  in
                      {
                        beta = (uu___147_14029.beta);
                        iota = (uu___147_14029.iota);
                        zeta = (uu___147_14029.zeta);
                        weak = (uu___147_14029.weak);
                        hnf = (uu___147_14029.hnf);
                        primops = (uu___147_14029.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___147_14029.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___147_14029.unfold_attr);
                        unfold_tac = (uu___147_14029.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___147_14029.pure_subterms_within_computations);
                        simplify = (uu___147_14029.simplify);
                        erase_universes = (uu___147_14029.erase_universes);
                        allow_unbound_universes =
                          (uu___147_14029.allow_unbound_universes);
                        reify_ = (uu___147_14029.reify_);
                        compress_uvars = (uu___147_14029.compress_uvars);
                        no_full_norm = (uu___147_14029.no_full_norm);
                        check_no_uvars = (uu___147_14029.check_no_uvars);
                        unmeta = (uu___147_14029.unmeta);
                        unascribe = (uu___147_14029.unascribe)
                      });
                   tcenv = (uu___146_14026.tcenv);
                   debug = (uu___146_14026.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___146_14026.primitive_steps);
                   strong = (uu___146_14026.strong);
                   memoize_lazy = (uu___146_14026.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____14032 = get_norm_request (norm cfg' env []) args  in
               (match uu____14032 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____14063  ->
                              fun stack1  ->
                                match uu____14063 with
                                | (a,aq) ->
                                    let uu____14075 =
                                      let uu____14076 =
                                        let uu____14083 =
                                          let uu____14084 =
                                            let uu____14115 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____14115, false)  in
                                          Clos uu____14084  in
                                        (uu____14083, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____14076  in
                                    uu____14075 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14199  ->
                          let uu____14200 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14200);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14222 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___86_14227  ->
                                match uu___86_14227 with
                                | UnfoldUntil uu____14228 -> true
                                | UnfoldOnly uu____14229 -> true
                                | uu____14232 -> false))
                         in
                      if uu____14222
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___148_14237 = cfg  in
                      let uu____14238 = to_fsteps s  in
                      {
                        steps = uu____14238;
                        tcenv = (uu___148_14237.tcenv);
                        debug = (uu___148_14237.debug);
                        delta_level;
                        primitive_steps = (uu___148_14237.primitive_steps);
                        strong = (uu___148_14237.strong);
                        memoize_lazy = (uu___148_14237.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14247 =
                          let uu____14248 =
                            let uu____14253 = FStar_Util.now ()  in
                            (t1, uu____14253)  in
                          Debug uu____14248  in
                        uu____14247 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14257 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14257
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14266 =
                      let uu____14273 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14273, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14266  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14283 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14283  in
               let uu____14284 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____14284
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____14290  ->
                       let uu____14291 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____14292 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____14291 uu____14292);
                  if b
                  then
                    (let uu____14293 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____14293 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____14301 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____14301) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___87_14307  ->
                               match uu___87_14307 with
                               | FStar_TypeChecker_Env.UnfoldTac  -> false
                               | FStar_TypeChecker_Env.NoDelta  -> false
                               | FStar_TypeChecker_Env.Inlining  -> true
                               | FStar_TypeChecker_Env.Eager_unfolding_only 
                                   -> true
                               | FStar_TypeChecker_Env.Unfold l ->
                                   FStar_TypeChecker_Common.delta_depth_greater_than
                                     fv.FStar_Syntax_Syntax.fv_delta l)))
                     in
                  let should_delta1 =
                    should_delta &&
                      (let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                       ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                          (let uu____14317 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____14317))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____14336) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____14371,uu____14372) -> false)))
                     in
                  log cfg
                    (fun uu____14394  ->
                       let uu____14395 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____14396 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14397 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____14395
                         uu____14396 uu____14397);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14400 = lookup_bvar env x  in
               (match uu____14400 with
                | Univ uu____14403 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14452 = FStar_ST.op_Bang r  in
                      (match uu____14452 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14570  ->
                                 let uu____14571 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14572 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14571
                                   uu____14572);
                            (let uu____14573 =
                               let uu____14574 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____14574.FStar_Syntax_Syntax.n  in
                             match uu____14573 with
                             | FStar_Syntax_Syntax.Tm_abs uu____14577 ->
                                 norm cfg env2 stack t'
                             | uu____14594 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14664)::uu____14665 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____14674)::uu____14675 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____14685,uu____14686))::stack_rest ->
                    (match c with
                     | Univ uu____14690 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14699 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14720  ->
                                    let uu____14721 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14721);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14761  ->
                                    let uu____14762 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14762);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____14840  ->
                          let uu____14841 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14841);
                     norm cfg env stack1 t1)
                | (Debug uu____14842)::uu____14843 ->
                    if (cfg.steps).weak
                    then
                      let uu____14850 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14850
                    else
                      (let uu____14852 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14852 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14894  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____14931 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14931)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_14936 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_14936.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_14936.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14937 -> lopt  in
                           (log cfg
                              (fun uu____14943  ->
                                 let uu____14944 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14944);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_14953 = cfg  in
                               {
                                 steps = (uu___150_14953.steps);
                                 tcenv = (uu___150_14953.tcenv);
                                 debug = (uu___150_14953.debug);
                                 delta_level = (uu___150_14953.delta_level);
                                 primitive_steps =
                                   (uu___150_14953.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_14953.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_14953.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14964)::uu____14965 ->
                    if (cfg.steps).weak
                    then
                      let uu____14972 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14972
                    else
                      (let uu____14974 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14974 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15016  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____15053 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15053)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15058 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15058.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15058.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15059 -> lopt  in
                           (log cfg
                              (fun uu____15065  ->
                                 let uu____15066 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15066);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15075 = cfg  in
                               {
                                 steps = (uu___150_15075.steps);
                                 tcenv = (uu___150_15075.tcenv);
                                 debug = (uu___150_15075.debug);
                                 delta_level = (uu___150_15075.delta_level);
                                 primitive_steps =
                                   (uu___150_15075.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15075.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15075.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____15086)::uu____15087 ->
                    if (cfg.steps).weak
                    then
                      let uu____15098 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15098
                    else
                      (let uu____15100 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15100 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15142  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____15179 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15179)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15184 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15184.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15184.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15185 -> lopt  in
                           (log cfg
                              (fun uu____15191  ->
                                 let uu____15192 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15192);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15201 = cfg  in
                               {
                                 steps = (uu___150_15201.steps);
                                 tcenv = (uu___150_15201.tcenv);
                                 debug = (uu___150_15201.debug);
                                 delta_level = (uu___150_15201.delta_level);
                                 primitive_steps =
                                   (uu___150_15201.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15201.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15201.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15212)::uu____15213 ->
                    if (cfg.steps).weak
                    then
                      let uu____15224 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15224
                    else
                      (let uu____15226 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15226 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15268  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____15305 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15305)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15310 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15310.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15310.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15311 -> lopt  in
                           (log cfg
                              (fun uu____15317  ->
                                 let uu____15318 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15318);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15327 = cfg  in
                               {
                                 steps = (uu___150_15327.steps);
                                 tcenv = (uu___150_15327.tcenv);
                                 debug = (uu___150_15327.debug);
                                 delta_level = (uu___150_15327.delta_level);
                                 primitive_steps =
                                   (uu___150_15327.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15327.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15327.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15338)::uu____15339 ->
                    if (cfg.steps).weak
                    then
                      let uu____15354 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15354
                    else
                      (let uu____15356 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15356 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15398  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____15435 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15435)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15440 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15440.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15440.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15441 -> lopt  in
                           (log cfg
                              (fun uu____15447  ->
                                 let uu____15448 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15448);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15457 = cfg  in
                               {
                                 steps = (uu___150_15457.steps);
                                 tcenv = (uu___150_15457.tcenv);
                                 debug = (uu___150_15457.debug);
                                 delta_level = (uu___150_15457.delta_level);
                                 primitive_steps =
                                   (uu___150_15457.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15457.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15457.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____15468 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15468
                    else
                      (let uu____15470 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15470 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15512  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if (cfg.steps).check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____15549 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15549)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15554 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15554.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15554.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15555 -> lopt  in
                           (log cfg
                              (fun uu____15561  ->
                                 let uu____15562 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15562);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15571 = cfg  in
                               {
                                 steps = (uu___150_15571.steps);
                                 tcenv = (uu___150_15571.tcenv);
                                 debug = (uu___150_15571.debug);
                                 delta_level = (uu___150_15571.delta_level);
                                 primitive_steps =
                                   (uu___150_15571.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15571.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15571.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____15620  ->
                         fun stack1  ->
                           match uu____15620 with
                           | (a,aq) ->
                               let uu____15632 =
                                 let uu____15633 =
                                   let uu____15640 =
                                     let uu____15641 =
                                       let uu____15672 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15672, false)  in
                                     Clos uu____15641  in
                                   (uu____15640, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15633  in
                               uu____15632 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15756  ->
                     let uu____15757 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15757);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if (cfg.steps).weak
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___151_15793 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___151_15793.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___151_15793.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15794 ->
                      let uu____15799 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15799)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15802 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15802 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15833 =
                          let uu____15834 =
                            let uu____15841 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___152_15843 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___152_15843.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___152_15843.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15841)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15834  in
                        mk uu____15833 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15862 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15862
               else
                 (let uu____15864 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15864 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15872 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15896  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15872 c1  in
                      let t2 =
                        let uu____15918 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15918 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____16029)::uu____16030 ->
                    (log cfg
                       (fun uu____16041  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____16042)::uu____16043 ->
                    (log cfg
                       (fun uu____16054  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____16055,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____16056;
                                   FStar_Syntax_Syntax.vars = uu____16057;_},uu____16058,uu____16059))::uu____16060
                    ->
                    (log cfg
                       (fun uu____16073  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____16074)::uu____16075 ->
                    (log cfg
                       (fun uu____16086  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____16087 ->
                    (log cfg
                       (fun uu____16090  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____16094  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____16111 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____16111
                         | FStar_Util.Inr c ->
                             let uu____16119 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____16119
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____16132 =
                               let uu____16133 =
                                 let uu____16160 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16160, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16133
                                in
                             mk uu____16132 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16179 ->
                           let uu____16180 =
                             let uu____16181 =
                               let uu____16182 =
                                 let uu____16209 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16209, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16182
                                in
                             mk uu____16181 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16180))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____16319 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16319 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___153_16339 = cfg  in
                               let uu____16340 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___153_16339.steps);
                                 tcenv = uu____16340;
                                 debug = (uu___153_16339.debug);
                                 delta_level = (uu___153_16339.delta_level);
                                 primitive_steps =
                                   (uu___153_16339.primitive_steps);
                                 strong = (uu___153_16339.strong);
                                 memoize_lazy = (uu___153_16339.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___153_16339.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16345 =
                                 let uu____16346 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16346  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16345
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___154_16349 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___154_16349.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___154_16349.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___154_16349.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___154_16349.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16350 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16350
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16361,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16362;
                               FStar_Syntax_Syntax.lbunivs = uu____16363;
                               FStar_Syntax_Syntax.lbtyp = uu____16364;
                               FStar_Syntax_Syntax.lbeff = uu____16365;
                               FStar_Syntax_Syntax.lbdef = uu____16366;
                               FStar_Syntax_Syntax.lbattrs = uu____16367;
                               FStar_Syntax_Syntax.lbpos = uu____16368;_}::uu____16369),uu____16370)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16410 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
                   ((((cfg.steps).pure_subterms_within_computations &&
                        (FStar_Syntax_Util.has_attribute
                           lb.FStar_Syntax_Syntax.lbattrs
                           FStar_Parser_Const.inline_let_attr))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.normalize_pure_lets ||
                             (FStar_Syntax_Util.has_attribute
                                lb.FStar_Syntax_Syntax.lbattrs
                                FStar_Parser_Const.inline_let_attr))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations)))
                  in
               if uu____16410
               then
                 let binder =
                   let uu____16412 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16412  in
                 let env1 =
                   let uu____16422 =
                     let uu____16429 =
                       let uu____16430 =
                         let uu____16461 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16461,
                           false)
                          in
                       Clos uu____16430  in
                     ((FStar_Pervasives_Native.Some binder), uu____16429)  in
                   uu____16422 :: env  in
                 (log cfg
                    (fun uu____16554  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16558  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16559 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16559))
                 else
                   (let uu____16561 =
                      let uu____16566 =
                        let uu____16567 =
                          let uu____16568 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16568
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16567]  in
                      FStar_Syntax_Subst.open_term uu____16566 body  in
                    match uu____16561 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16577  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16585 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16585  in
                            FStar_Util.Inl
                              (let uu___155_16595 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_16595.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_16595.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16598  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___156_16600 = lb  in
                             let uu____16601 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___156_16600.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___156_16600.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16601;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___156_16600.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___156_16600.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16636  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___157_16659 = cfg  in
                             {
                               steps = (uu___157_16659.steps);
                               tcenv = (uu___157_16659.tcenv);
                               debug = (uu___157_16659.debug);
                               delta_level = (uu___157_16659.delta_level);
                               primitive_steps =
                                 (uu___157_16659.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___157_16659.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___157_16659.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16662  ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (cfg.steps).compress_uvars ||
                 ((Prims.op_Negation (cfg.steps).zeta) &&
                    (cfg.steps).pure_subterms_within_computations)
               ->
               let uu____16679 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16679 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16715 =
                               let uu___158_16716 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___158_16716.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___158_16716.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16715  in
                           let uu____16717 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16717 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16743 =
                                   FStar_List.map (fun uu____16759  -> dummy)
                                     lbs1
                                    in
                                 let uu____16760 =
                                   let uu____16769 =
                                     FStar_List.map
                                       (fun uu____16789  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16769 env  in
                                 FStar_List.append uu____16743 uu____16760
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16813 =
                                       let uu___159_16814 = rc  in
                                       let uu____16815 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___159_16814.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16815;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___159_16814.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16813
                                 | uu____16822 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___160_16826 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___160_16826.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___160_16826.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___160_16826.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___160_16826.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____16836 =
                        FStar_List.map (fun uu____16852  -> dummy) lbs2  in
                      FStar_List.append uu____16836 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16860 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16860 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___161_16876 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___161_16876.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___161_16876.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16903 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16903
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16922 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16998  ->
                        match uu____16998 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___162_17119 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___162_17119.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___162_17119.FStar_Syntax_Syntax.sort)
                              }  in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env  in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____16922 with
                | (rec_env,memos,uu____17332) ->
                    let uu____17385 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____17696 =
                               let uu____17703 =
                                 let uu____17704 =
                                   let uu____17735 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17735, false)
                                    in
                                 Clos uu____17704  in
                               (FStar_Pervasives_Native.None, uu____17703)
                                in
                             uu____17696 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17845  ->
                     let uu____17846 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17846);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | FStar_Syntax_Syntax.Meta_quoted (qt,inf) ->
                     rebuild cfg env stack t1
                 | uu____17874 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17876::uu____17877 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17882) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____17905 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17919 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17919
                              | uu____17930 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17934 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17960 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17978 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17995 =
                        let uu____17996 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17997 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17996 uu____17997
                         in
                      failwith uu____17995
                    else rebuild cfg env stack t2
                | uu____17999 -> norm cfg env stack t2))

and (do_unfold_fv :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let r_env =
                let uu____18009 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____18009  in
              let uu____18010 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____18010 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____18023  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____18034  ->
                        let uu____18035 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____18036 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____18035 uu____18036);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          (FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                          t
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____18049))::stack1 ->
                          let env1 =
                            FStar_All.pipe_right us'
                              (FStar_List.fold_left
                                 (fun env1  ->
                                    fun u  ->
                                      (FStar_Pervasives_Native.None,
                                        (Univ u))
                                      :: env1) env)
                             in
                          norm cfg env1 stack1 t1
                      | uu____18104 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____18107 ->
                          let uu____18110 =
                            let uu____18111 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____18111
                             in
                          failwith uu____18110
                    else norm cfg env stack t1))

and (reduce_impure_comp :
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t  in
              let stack1 = (Cfg cfg) :: stack  in
              let cfg1 =
                if (cfg.steps).pure_subterms_within_computations
                then
                  let new_steps =
                    [PureSubtermsWithinComputations;
                    Primops;
                    AllowUnboundUniverses;
                    EraseUniverses;
                    Exclude Zeta;
                    Inlining]  in
                  let uu___163_18135 = cfg  in
                  let uu____18136 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____18136;
                    tcenv = (uu___163_18135.tcenv);
                    debug = (uu___163_18135.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___163_18135.primitive_steps);
                    strong = (uu___163_18135.strong);
                    memoize_lazy = (uu___163_18135.memoize_lazy);
                    normalize_pure_lets =
                      (uu___163_18135.normalize_pure_lets)
                  }
                else
                  (let uu___164_18138 = cfg  in
                   {
                     steps =
                       (let uu___165_18141 = cfg.steps  in
                        {
                          beta = (uu___165_18141.beta);
                          iota = (uu___165_18141.iota);
                          zeta = false;
                          weak = (uu___165_18141.weak);
                          hnf = (uu___165_18141.hnf);
                          primops = (uu___165_18141.primops);
                          no_delta_steps = (uu___165_18141.no_delta_steps);
                          unfold_until = (uu___165_18141.unfold_until);
                          unfold_only = (uu___165_18141.unfold_only);
                          unfold_attr = (uu___165_18141.unfold_attr);
                          unfold_tac = (uu___165_18141.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___165_18141.pure_subterms_within_computations);
                          simplify = (uu___165_18141.simplify);
                          erase_universes = (uu___165_18141.erase_universes);
                          allow_unbound_universes =
                            (uu___165_18141.allow_unbound_universes);
                          reify_ = (uu___165_18141.reify_);
                          compress_uvars = (uu___165_18141.compress_uvars);
                          no_full_norm = (uu___165_18141.no_full_norm);
                          check_no_uvars = (uu___165_18141.check_no_uvars);
                          unmeta = (uu___165_18141.unmeta);
                          unascribe = (uu___165_18141.unascribe)
                        });
                     tcenv = (uu___164_18138.tcenv);
                     debug = (uu___164_18138.debug);
                     delta_level = (uu___164_18138.delta_level);
                     primitive_steps = (uu___164_18138.primitive_steps);
                     strong = (uu___164_18138.strong);
                     memoize_lazy = (uu___164_18138.memoize_lazy);
                     normalize_pure_lets =
                       (uu___164_18138.normalize_pure_lets)
                   })
                 in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                 in
              norm cfg1 env
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

and (do_reify_monadic :
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head0 = head1  in
                let head2 = FStar_Syntax_Util.unascribe head1  in
                log cfg
                  (fun uu____18171  ->
                     let uu____18172 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18173 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18172
                       uu____18173);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____18175 =
                   let uu____18176 = FStar_Syntax_Subst.compress head3  in
                   uu____18176.FStar_Syntax_Syntax.n  in
                 match uu____18175 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____18194 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18194
                        in
                     let uu____18195 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18195 with
                      | (uu____18196,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18202 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18210 =
                                   let uu____18211 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18211.FStar_Syntax_Syntax.n  in
                                 match uu____18210 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18217,uu____18218))
                                     ->
                                     let uu____18227 =
                                       let uu____18228 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18228.FStar_Syntax_Syntax.n  in
                                     (match uu____18227 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18234,msrc,uu____18236))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18245 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18245
                                      | uu____18246 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18247 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18248 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18248 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___166_18253 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___166_18253.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___166_18253.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___166_18253.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___166_18253.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___166_18253.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18254 = FStar_List.tl stack  in
                                    let uu____18255 =
                                      let uu____18256 =
                                        let uu____18259 =
                                          let uu____18260 =
                                            let uu____18273 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18273)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18260
                                           in
                                        FStar_Syntax_Syntax.mk uu____18259
                                         in
                                      uu____18256
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18254 uu____18255
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18289 =
                                      let uu____18290 = is_return body  in
                                      match uu____18290 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18294;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18295;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18304 -> false  in
                                    if uu____18289
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head3.FStar_Syntax_Syntax.pos  in
                                       let head4 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef
                                          in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body
                                          in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         }  in
                                       let body2 =
                                         let uu____18327 =
                                           let uu____18330 =
                                             let uu____18331 =
                                               let uu____18348 =
                                                 let uu____18351 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18351]  in
                                               (uu____18348, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18331
                                              in
                                           FStar_Syntax_Syntax.mk uu____18330
                                            in
                                         uu____18327
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18367 =
                                           let uu____18368 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18368.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18367 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18374::uu____18375::[])
                                             ->
                                             let uu____18382 =
                                               let uu____18385 =
                                                 let uu____18386 =
                                                   let uu____18393 =
                                                     let uu____18396 =
                                                       let uu____18397 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18397
                                                        in
                                                     let uu____18398 =
                                                       let uu____18401 =
                                                         let uu____18402 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18402
                                                          in
                                                       [uu____18401]  in
                                                     uu____18396 ::
                                                       uu____18398
                                                      in
                                                   (bind1, uu____18393)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18386
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18385
                                                in
                                             uu____18382
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18410 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18416 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18416
                                         then
                                           let uu____18419 =
                                             let uu____18420 =
                                               FStar_Syntax_Embeddings.embed_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18420
                                              in
                                           let uu____18421 =
                                             let uu____18424 =
                                               let uu____18425 =
                                                 FStar_Syntax_Embeddings.embed_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____18425
                                                in
                                             [uu____18424]  in
                                           uu____18419 :: uu____18421
                                         else []  in
                                       let reified =
                                         let uu____18430 =
                                           let uu____18433 =
                                             let uu____18434 =
                                               let uu____18449 =
                                                 let uu____18452 =
                                                   let uu____18455 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____18456 =
                                                     let uu____18459 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____18459]  in
                                                   uu____18455 :: uu____18456
                                                    in
                                                 let uu____18460 =
                                                   let uu____18463 =
                                                     let uu____18466 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18467 =
                                                       let uu____18470 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____18471 =
                                                         let uu____18474 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18475 =
                                                           let uu____18478 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18478]  in
                                                         uu____18474 ::
                                                           uu____18475
                                                          in
                                                       uu____18470 ::
                                                         uu____18471
                                                        in
                                                     uu____18466 ::
                                                       uu____18467
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____18463
                                                    in
                                                 FStar_List.append
                                                   uu____18452 uu____18460
                                                  in
                                               (bind_inst, uu____18449)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18434
                                              in
                                           FStar_Syntax_Syntax.mk uu____18433
                                            in
                                         uu____18430
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18490  ->
                                            let uu____18491 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18492 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18491 uu____18492);
                                       (let uu____18493 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18493 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____18517 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18517
                        in
                     let uu____18518 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18518 with
                      | (uu____18519,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18554 =
                                  let uu____18555 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18555.FStar_Syntax_Syntax.n  in
                                match uu____18554 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18561) -> t2
                                | uu____18566 -> head4  in
                              let uu____18567 =
                                let uu____18568 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18568.FStar_Syntax_Syntax.n  in
                              match uu____18567 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18574 -> FStar_Pervasives_Native.None
                               in
                            let uu____18575 = maybe_extract_fv head4  in
                            match uu____18575 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18585 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18585
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____18590 = maybe_extract_fv head5
                                     in
                                  match uu____18590 with
                                  | FStar_Pervasives_Native.Some uu____18595
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18596 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____18601 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18616 =
                              match uu____18616 with
                              | (e,q) ->
                                  let uu____18623 =
                                    let uu____18624 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18624.FStar_Syntax_Syntax.n  in
                                  (match uu____18623 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____18639 -> false)
                               in
                            let uu____18640 =
                              let uu____18641 =
                                let uu____18648 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18648 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18641
                               in
                            if uu____18640
                            then
                              let uu____18653 =
                                let uu____18654 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18654
                                 in
                              failwith uu____18653
                            else ());
                           (let uu____18656 = maybe_unfold_action head_app
                               in
                            match uu____18656 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head3.FStar_Syntax_Syntax.pos
                                   in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args))
                                   in
                                let body1 =
                                  match found_action with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Syntax_Util.mk_reify body
                                  | FStar_Pervasives_Native.Some (false ) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body
                                   in
                                (log cfg
                                   (fun uu____18697  ->
                                      let uu____18698 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18699 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18698 uu____18699);
                                 (let uu____18700 = FStar_List.tl stack  in
                                  norm cfg env uu____18700 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18702) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18726 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18726  in
                     (log cfg
                        (fun uu____18730  ->
                           let uu____18731 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18731);
                      (let uu____18732 = FStar_List.tl stack  in
                       norm cfg env uu____18732 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____18853  ->
                               match uu____18853 with
                               | (pat,wopt,tm) ->
                                   let uu____18901 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____18901)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____18933 = FStar_List.tl stack  in
                     norm cfg env uu____18933 tm
                 | uu____18934 -> fallback ())

and (reify_lift :
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv  in
            log cfg
              (fun uu____18948  ->
                 let uu____18949 = FStar_Ident.string_of_lid msrc  in
                 let uu____18950 = FStar_Ident.string_of_lid mtgt  in
                 let uu____18951 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____18949
                   uu____18950 uu____18951);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed =
                 let uu____18953 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____18953  in
               let uu____18954 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____18954 with
               | (uu____18955,return_repr) ->
                   let return_inst =
                     let uu____18964 =
                       let uu____18965 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____18965.FStar_Syntax_Syntax.n  in
                     match uu____18964 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____18971::[]) ->
                         let uu____18978 =
                           let uu____18981 =
                             let uu____18982 =
                               let uu____18989 =
                                 let uu____18992 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____18992]  in
                               (return_tm, uu____18989)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____18982  in
                           FStar_Syntax_Syntax.mk uu____18981  in
                         uu____18978 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____19000 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____19003 =
                     let uu____19006 =
                       let uu____19007 =
                         let uu____19022 =
                           let uu____19025 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____19026 =
                             let uu____19029 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____19029]  in
                           uu____19025 :: uu____19026  in
                         (return_inst, uu____19022)  in
                       FStar_Syntax_Syntax.Tm_app uu____19007  in
                     FStar_Syntax_Syntax.mk uu____19006  in
                   uu____19003 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____19038 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____19038 with
               | FStar_Pervasives_Native.None  ->
                   let uu____19041 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____19041
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____19042;
                     FStar_TypeChecker_Env.mtarget = uu____19043;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____19044;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____19059 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____19059
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____19060;
                     FStar_TypeChecker_Env.mtarget = uu____19061;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____19062;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____19086 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____19087 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____19086 t FStar_Syntax_Syntax.tun uu____19087)

and (norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____19143  ->
                   match uu____19143 with
                   | (a,imp) ->
                       let uu____19154 = norm cfg env [] a  in
                       (uu____19154, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___167_19168 = comp  in
            let uu____19169 =
              let uu____19170 =
                let uu____19179 = norm cfg env [] t  in
                let uu____19180 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____19179, uu____19180)  in
              FStar_Syntax_Syntax.Total uu____19170  in
            {
              FStar_Syntax_Syntax.n = uu____19169;
              FStar_Syntax_Syntax.pos =
                (uu___167_19168.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_19168.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___168_19195 = comp  in
            let uu____19196 =
              let uu____19197 =
                let uu____19206 = norm cfg env [] t  in
                let uu____19207 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____19206, uu____19207)  in
              FStar_Syntax_Syntax.GTotal uu____19197  in
            {
              FStar_Syntax_Syntax.n = uu____19196;
              FStar_Syntax_Syntax.pos =
                (uu___168_19195.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_19195.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____19259  ->
                      match uu____19259 with
                      | (a,i) ->
                          let uu____19270 = norm cfg env [] a  in
                          (uu____19270, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_19281  ->
                      match uu___88_19281 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____19285 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____19285
                      | f -> f))
               in
            let uu___169_19289 = comp  in
            let uu____19290 =
              let uu____19291 =
                let uu___170_19292 = ct  in
                let uu____19293 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____19294 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____19297 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____19293;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___170_19292.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____19294;
                  FStar_Syntax_Syntax.effect_args = uu____19297;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____19291  in
            {
              FStar_Syntax_Syntax.n = uu____19290;
              FStar_Syntax_Syntax.pos =
                (uu___169_19289.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_19289.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19308  ->
        match uu____19308 with
        | (x,imp) ->
            let uu____19311 =
              let uu___171_19312 = x  in
              let uu____19313 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___171_19312.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___171_19312.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19313
              }  in
            (uu____19311, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19319 =
          FStar_List.fold_left
            (fun uu____19337  ->
               fun b  ->
                 match uu____19337 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19319 with | (nbs,uu____19377) -> FStar_List.rev nbs

and (norm_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____19393 =
              let uu___172_19394 = rc  in
              let uu____19395 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___172_19394.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19395;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___172_19394.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19393
        | uu____19402 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19415  ->
               let uu____19416 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19417 = FStar_Syntax_Print.term_to_string t  in
               let uu____19418 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19425 =
                 let uu____19426 =
                   let uu____19429 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19429
                    in
                 stack_to_string uu____19426  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19416 uu____19417 uu____19418 uu____19425);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19460 =
                     let uu____19461 =
                       let uu____19462 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19462  in
                     FStar_Util.string_of_int uu____19461  in
                   let uu____19467 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19468 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19460 uu____19467 uu____19468)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19522  ->
                     let uu____19523 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19523);
                rebuild cfg env stack1 t1)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t1  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env' stack1 t2
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs  in
               let lopt1 = norm_lcomp_opt cfg env'' lopt  in
               let uu____19559 =
                 let uu___173_19560 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___173_19560.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___173_19560.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19559
           | (Arg (Univ uu____19561,uu____19562,uu____19563))::uu____19564 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19567,uu____19568))::uu____19569 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19584,uu____19585),aq,r))::stack1
               when
               let uu____19635 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19635 ->
               let t2 =
                 let uu____19639 =
                   let uu____19640 =
                     let uu____19641 = closure_as_term cfg env_arg tm  in
                     (uu____19641, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____19640  in
                 uu____19639 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____19647),aq,r))::stack1 ->
               (log cfg
                  (fun uu____19700  ->
                     let uu____19701 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19701);
                if Prims.op_Negation (cfg.steps).iota
                then
                  (if (cfg.steps).hnf
                   then
                     let arg = closure_as_term cfg env_arg tm  in
                     let t2 =
                       FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env_arg stack1 t2
                   else
                     (let stack2 = (App (env, t1, aq, r)) :: stack1  in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____19711 = FStar_ST.op_Bang m  in
                   match uu____19711 with
                   | FStar_Pervasives_Native.None  ->
                       if (cfg.steps).hnf
                       then
                         let arg = closure_as_term cfg env_arg tm  in
                         let t2 =
                           FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                             FStar_Pervasives_Native.None r
                            in
                         rebuild cfg env_arg stack1 t2
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t1, aq, r))
                            :: stack1  in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____19848,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____19895 =
                 log cfg
                   (fun uu____19899  ->
                      let uu____19900 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____19900);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____19904 =
                 let uu____19905 = FStar_Syntax_Subst.compress t1  in
                 uu____19905.FStar_Syntax_Syntax.n  in
               (match uu____19904 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____19932 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____19932  in
                    (log cfg
                       (fun uu____19936  ->
                          let uu____19937 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____19937);
                     (let uu____19938 = FStar_List.tl stack  in
                      norm cfg env1 uu____19938 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____19939);
                       FStar_Syntax_Syntax.pos = uu____19940;
                       FStar_Syntax_Syntax.vars = uu____19941;_},(e,uu____19943)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____19976 when
                    (cfg.steps).primops ->
                    let uu____19991 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____19991 with
                     | (hd1,args) ->
                         let uu____20028 =
                           let uu____20029 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20029.FStar_Syntax_Syntax.n  in
                         (match uu____20028 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20033 = find_prim_step cfg fv  in
                              (match uu____20033 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20036; arity = uu____20037;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20039;
                                     requires_binder_substitution =
                                       uu____20040;
                                     interpretation = uu____20041;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20054 -> fallback " (3)" ())
                          | uu____20057 -> fallback " (4)" ()))
                | uu____20058 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____20078  ->
                     let uu____20079 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20079);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____20084 =
                   log cfg
                     (fun uu____20089  ->
                        let uu____20090 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____20091 =
                          let uu____20092 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20109  ->
                                    match uu____20109 with
                                    | (p,uu____20119,uu____20120) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____20092
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20090 uu____20091);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_20137  ->
                                match uu___89_20137 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____20138 -> false))
                         in
                      let uu___174_20139 = cfg  in
                      {
                        steps =
                          (let uu___175_20142 = cfg.steps  in
                           {
                             beta = (uu___175_20142.beta);
                             iota = (uu___175_20142.iota);
                             zeta = false;
                             weak = (uu___175_20142.weak);
                             hnf = (uu___175_20142.hnf);
                             primops = (uu___175_20142.primops);
                             no_delta_steps = (uu___175_20142.no_delta_steps);
                             unfold_until = (uu___175_20142.unfold_until);
                             unfold_only = (uu___175_20142.unfold_only);
                             unfold_attr = (uu___175_20142.unfold_attr);
                             unfold_tac = (uu___175_20142.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___175_20142.pure_subterms_within_computations);
                             simplify = (uu___175_20142.simplify);
                             erase_universes =
                               (uu___175_20142.erase_universes);
                             allow_unbound_universes =
                               (uu___175_20142.allow_unbound_universes);
                             reify_ = (uu___175_20142.reify_);
                             compress_uvars = (uu___175_20142.compress_uvars);
                             no_full_norm = (uu___175_20142.no_full_norm);
                             check_no_uvars = (uu___175_20142.check_no_uvars);
                             unmeta = (uu___175_20142.unmeta);
                             unascribe = (uu___175_20142.unascribe)
                           });
                        tcenv = (uu___174_20139.tcenv);
                        debug = (uu___174_20139.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___174_20139.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___174_20139.memoize_lazy);
                        normalize_pure_lets =
                          (uu___174_20139.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20174 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____20195 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20255  ->
                                    fun uu____20256  ->
                                      match (uu____20255, uu____20256) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20347 = norm_pat env3 p1
                                             in
                                          (match uu____20347 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____20195 with
                           | (pats1,env3) ->
                               ((let uu___176_20429 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___176_20429.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___177_20448 = x  in
                            let uu____20449 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___177_20448.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___177_20448.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20449
                            }  in
                          ((let uu___178_20463 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___178_20463.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___179_20474 = x  in
                            let uu____20475 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_20474.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_20474.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20475
                            }  in
                          ((let uu___180_20489 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_20489.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___181_20505 = x  in
                            let uu____20506 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_20505.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_20505.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20506
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___182_20513 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___182_20513.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20523 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20537 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20537 with
                                  | (p,wopt,e) ->
                                      let uu____20557 = norm_pat env1 p  in
                                      (match uu____20557 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20582 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20582
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____20588 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____20588)
                    in
                 let rec is_cons head1 =
                   let uu____20593 =
                     let uu____20594 = FStar_Syntax_Subst.compress head1  in
                     uu____20594.FStar_Syntax_Syntax.n  in
                   match uu____20593 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____20598) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20603 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20604;
                         FStar_Syntax_Syntax.fv_delta = uu____20605;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20606;
                         FStar_Syntax_Syntax.fv_delta = uu____20607;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20608);_}
                       -> true
                   | uu____20615 -> false  in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b  in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r
                          in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch
                    in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig
                      in
                   let uu____20760 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____20760 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____20847 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____20886 ->
                                 let uu____20887 =
                                   let uu____20888 = is_cons head1  in
                                   Prims.op_Negation uu____20888  in
                                 FStar_Util.Inr uu____20887)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____20913 =
                              let uu____20914 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____20914.FStar_Syntax_Syntax.n  in
                            (match uu____20913 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____20932 ->
                                 let uu____20933 =
                                   let uu____20934 = is_cons head1  in
                                   Prims.op_Negation uu____20934  in
                                 FStar_Util.Inr uu____20933))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21003)::rest_a,(p1,uu____21006)::rest_p) ->
                       let uu____21050 = matches_pat t2 p1  in
                       (match uu____21050 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21099 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21205 = matches_pat scrutinee1 p1  in
                       (match uu____21205 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____21245  ->
                                  let uu____21246 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21247 =
                                    let uu____21248 =
                                      FStar_List.map
                                        (fun uu____21258  ->
                                           match uu____21258 with
                                           | (uu____21263,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21248
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21246 uu____21247);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21294  ->
                                       match uu____21294 with
                                       | (bv,t2) ->
                                           let uu____21317 =
                                             let uu____21324 =
                                               let uu____21327 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21327
                                                in
                                             let uu____21328 =
                                               let uu____21329 =
                                                 let uu____21360 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21360, false)
                                                  in
                                               Clos uu____21329  in
                                             (uu____21324, uu____21328)  in
                                           uu____21317 :: env2) env1 s
                                 in
                              let uu____21477 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21477)))
                    in
                 if (cfg.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let (plugins :
  (primitive_step -> Prims.unit,Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____21500 =
      let uu____21503 = FStar_ST.op_Bang plugins  in p :: uu____21503  in
    FStar_ST.op_Colon_Equals plugins uu____21500  in
  let retrieve uu____21601 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____21666  -> FStar_Pervasives_Native.snd plugins () 
let (config' :
  primitive_step Prims.list ->
    step Prims.list -> FStar_TypeChecker_Env.env -> cfg)
  =
  fun psteps  ->
    fun s  ->
      fun e  ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___90_21699  ->
                  match uu___90_21699 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____21703 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____21709 -> d  in
        let uu____21712 = to_fsteps s  in
        let uu____21713 =
          let uu____21714 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____21715 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____21716 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____21717 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____21718 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____21714;
            primop = uu____21715;
            b380 = uu____21716;
            norm_delayed = uu____21717;
            print_normalized = uu____21718
          }  in
        let uu____21719 =
          let uu____21722 =
            let uu____21725 = retrieve_plugins ()  in
            FStar_List.append uu____21725 psteps  in
          add_steps built_in_primitive_steps uu____21722  in
        let uu____21728 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____21730 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____21730)
           in
        {
          steps = uu____21712;
          tcenv = e;
          debug = uu____21713;
          delta_level = d1;
          primitive_steps = uu____21719;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____21728
        }
  
let (config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg) =
  fun s  -> fun e  -> config' [] s e 
let (normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  -> fun e  -> fun t  -> let c = config' ps s e  in norm c [] [] t
  
let (normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let (normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____21788 = config s e  in norm_comp uu____21788 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____21801 = config [] env  in norm_universe uu____21801 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env
         in
      let non_info t =
        let uu____21819 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21819  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____21826 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___183_21845 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___183_21845.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___183_21845.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____21852 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____21852
          then
            let ct1 =
              match downgrade_ghost_effect_name
                      ct.FStar_Syntax_Syntax.effect_name
              with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    if
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___184_21861 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___184_21861.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___184_21861.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___184_21861.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___185_21863 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___185_21863.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___185_21863.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___185_21863.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___185_21863.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___186_21864 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___186_21864.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_21864.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____21866 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____21878 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21878  in
      let uu____21885 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____21885
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____21889  ->
                 let uu____21890 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____21890)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____21907 =
                let uu____21912 =
                  let uu____21913 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21913
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21912)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____21907);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____21924 = config [AllowUnboundUniverses] env  in
          norm_comp uu____21924 [] c
        with
        | e ->
            ((let uu____21937 =
                let uu____21942 =
                  let uu____21943 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21943
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21942)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____21937);
             c)
         in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
  
let (normalize_refinement :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0  in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____21980 =
                     let uu____21981 =
                       let uu____21988 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____21988)  in
                     FStar_Syntax_Syntax.Tm_refine uu____21981  in
                   mk uu____21980 t01.FStar_Syntax_Syntax.pos
               | uu____21993 -> t2)
          | uu____21994 -> t2  in
        aux t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [Primops;
        Weak;
        HNF;
        UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
        Beta] env t
  
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
  
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____22034 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____22034 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____22063 ->
                 let uu____22070 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____22070 with
                  | (actuals,uu____22080,uu____22081) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22095 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____22095 with
                         | (binders,args) ->
                             let uu____22112 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____22112
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____22120 ->
          let uu____22121 = FStar_Syntax_Util.head_and_args t  in
          (match uu____22121 with
           | (head1,args) ->
               let uu____22158 =
                 let uu____22159 = FStar_Syntax_Subst.compress head1  in
                 uu____22159.FStar_Syntax_Syntax.n  in
               (match uu____22158 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22162,thead) ->
                    let uu____22188 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____22188 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22230 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___191_22238 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___191_22238.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___191_22238.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___191_22238.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___191_22238.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___191_22238.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___191_22238.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___191_22238.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___191_22238.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___191_22238.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___191_22238.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___191_22238.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___191_22238.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___191_22238.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___191_22238.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___191_22238.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___191_22238.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___191_22238.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___191_22238.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___191_22238.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___191_22238.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___191_22238.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___191_22238.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___191_22238.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___191_22238.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___191_22238.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___191_22238.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___191_22238.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___191_22238.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___191_22238.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___191_22238.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___191_22238.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___191_22238.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___191_22238.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____22230 with
                            | (uu____22239,ty,uu____22241) ->
                                eta_expand_with_type env t ty))
                | uu____22242 ->
                    let uu____22243 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___192_22251 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___192_22251.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___192_22251.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___192_22251.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___192_22251.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___192_22251.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___192_22251.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___192_22251.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___192_22251.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___192_22251.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___192_22251.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___192_22251.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___192_22251.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___192_22251.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___192_22251.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___192_22251.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___192_22251.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___192_22251.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___192_22251.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___192_22251.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___192_22251.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___192_22251.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___192_22251.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___192_22251.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___192_22251.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___192_22251.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___192_22251.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___192_22251.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.splice =
                             (uu___192_22251.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___192_22251.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___192_22251.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___192_22251.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___192_22251.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___192_22251.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____22243 with
                     | (uu____22252,ty,uu____22254) ->
                         eta_expand_with_type env t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___193_22311 = x  in
      let uu____22312 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___193_22311.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___193_22311.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22312
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22315 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22340 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22341 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22342 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22343 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22350 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22351 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22352 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___194_22380 = rc  in
          let uu____22381 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____22388 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___194_22380.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22381;
            FStar_Syntax_Syntax.residual_flags = uu____22388
          }  in
        let uu____22391 =
          let uu____22392 =
            let uu____22409 = elim_delayed_subst_binders bs  in
            let uu____22416 = elim_delayed_subst_term t2  in
            let uu____22417 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22409, uu____22416, uu____22417)  in
          FStar_Syntax_Syntax.Tm_abs uu____22392  in
        mk1 uu____22391
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22446 =
          let uu____22447 =
            let uu____22460 = elim_delayed_subst_binders bs  in
            let uu____22467 = elim_delayed_subst_comp c  in
            (uu____22460, uu____22467)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22447  in
        mk1 uu____22446
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22480 =
          let uu____22481 =
            let uu____22488 = elim_bv bv  in
            let uu____22489 = elim_delayed_subst_term phi  in
            (uu____22488, uu____22489)  in
          FStar_Syntax_Syntax.Tm_refine uu____22481  in
        mk1 uu____22480
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22512 =
          let uu____22513 =
            let uu____22528 = elim_delayed_subst_term t2  in
            let uu____22529 = elim_delayed_subst_args args  in
            (uu____22528, uu____22529)  in
          FStar_Syntax_Syntax.Tm_app uu____22513  in
        mk1 uu____22512
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___195_22593 = p  in
              let uu____22594 =
                let uu____22595 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____22595  in
              {
                FStar_Syntax_Syntax.v = uu____22594;
                FStar_Syntax_Syntax.p =
                  (uu___195_22593.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___196_22597 = p  in
              let uu____22598 =
                let uu____22599 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____22599  in
              {
                FStar_Syntax_Syntax.v = uu____22598;
                FStar_Syntax_Syntax.p =
                  (uu___196_22597.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___197_22606 = p  in
              let uu____22607 =
                let uu____22608 =
                  let uu____22615 = elim_bv x  in
                  let uu____22616 = elim_delayed_subst_term t0  in
                  (uu____22615, uu____22616)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____22608  in
              {
                FStar_Syntax_Syntax.v = uu____22607;
                FStar_Syntax_Syntax.p =
                  (uu___197_22606.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___198_22635 = p  in
              let uu____22636 =
                let uu____22637 =
                  let uu____22650 =
                    FStar_List.map
                      (fun uu____22673  ->
                         match uu____22673 with
                         | (x,b) ->
                             let uu____22686 = elim_pat x  in
                             (uu____22686, b)) pats
                     in
                  (fv, uu____22650)  in
                FStar_Syntax_Syntax.Pat_cons uu____22637  in
              {
                FStar_Syntax_Syntax.v = uu____22636;
                FStar_Syntax_Syntax.p =
                  (uu___198_22635.FStar_Syntax_Syntax.p)
              }
          | uu____22699 -> p  in
        let elim_branch uu____22721 =
          match uu____22721 with
          | (pat,wopt,t3) ->
              let uu____22747 = elim_pat pat  in
              let uu____22750 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____22753 = elim_delayed_subst_term t3  in
              (uu____22747, uu____22750, uu____22753)
           in
        let uu____22758 =
          let uu____22759 =
            let uu____22782 = elim_delayed_subst_term t2  in
            let uu____22783 = FStar_List.map elim_branch branches  in
            (uu____22782, uu____22783)  in
          FStar_Syntax_Syntax.Tm_match uu____22759  in
        mk1 uu____22758
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____22892 =
          match uu____22892 with
          | (tc,topt) ->
              let uu____22927 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____22937 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____22937
                | FStar_Util.Inr c ->
                    let uu____22939 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____22939
                 in
              let uu____22940 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____22927, uu____22940)
           in
        let uu____22949 =
          let uu____22950 =
            let uu____22977 = elim_delayed_subst_term t2  in
            let uu____22978 = elim_ascription a  in
            (uu____22977, uu____22978, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____22950  in
        mk1 uu____22949
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___199_23023 = lb  in
          let uu____23024 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23027 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___199_23023.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___199_23023.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23024;
            FStar_Syntax_Syntax.lbeff =
              (uu___199_23023.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23027;
            FStar_Syntax_Syntax.lbattrs =
              (uu___199_23023.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___199_23023.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____23030 =
          let uu____23031 =
            let uu____23044 =
              let uu____23051 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____23051)  in
            let uu____23060 = elim_delayed_subst_term t2  in
            (uu____23044, uu____23060)  in
          FStar_Syntax_Syntax.Tm_let uu____23031  in
        mk1 uu____23030
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____23093 =
          let uu____23094 =
            let uu____23111 = elim_delayed_subst_term t2  in
            (uv, uu____23111)  in
          FStar_Syntax_Syntax.Tm_uvar uu____23094  in
        mk1 uu____23093
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____23128 =
          let uu____23129 =
            let uu____23136 = elim_delayed_subst_term t2  in
            let uu____23137 = elim_delayed_subst_meta md  in
            (uu____23136, uu____23137)  in
          FStar_Syntax_Syntax.Tm_meta uu____23129  in
        mk1 uu____23128

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_23144  ->
         match uu___91_23144 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23148 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____23148
         | f -> f) flags1

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____23169 =
          let uu____23170 =
            let uu____23179 = elim_delayed_subst_term t  in
            (uu____23179, uopt)  in
          FStar_Syntax_Syntax.Total uu____23170  in
        mk1 uu____23169
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____23192 =
          let uu____23193 =
            let uu____23202 = elim_delayed_subst_term t  in
            (uu____23202, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____23193  in
        mk1 uu____23192
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___200_23207 = ct  in
          let uu____23208 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____23211 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____23220 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___200_23207.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___200_23207.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23208;
            FStar_Syntax_Syntax.effect_args = uu____23211;
            FStar_Syntax_Syntax.flags = uu____23220
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___92_23223  ->
    match uu___92_23223 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23235 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23235
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23268 =
          let uu____23275 = elim_delayed_subst_term t  in (m, uu____23275)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23268
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23283 =
          let uu____23292 = elim_delayed_subst_term t  in
          (m1, m2, uu____23292)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23283
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23315  ->
         match uu____23315 with
         | (t,q) ->
             let uu____23326 = elim_delayed_subst_term t  in (uu____23326, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23346  ->
         match uu____23346 with
         | (x,q) ->
             let uu____23357 =
               let uu___201_23358 = x  in
               let uu____23359 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___201_23358.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___201_23358.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23359
               }  in
             (uu____23357, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____23435,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23441,FStar_Util.Inl t) ->
                let uu____23447 =
                  let uu____23450 =
                    let uu____23451 =
                      let uu____23464 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23464)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23451  in
                  FStar_Syntax_Syntax.mk uu____23450  in
                uu____23447 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23468 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23468 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23496 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23551 ->
                    let uu____23552 =
                      let uu____23561 =
                        let uu____23562 = FStar_Syntax_Subst.compress t4  in
                        uu____23562.FStar_Syntax_Syntax.n  in
                      (uu____23561, tc)  in
                    (match uu____23552 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____23587) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____23624) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23663,FStar_Util.Inl uu____23664) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23687 -> failwith "Impossible")
                 in
              (match uu____23496 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____23792 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____23792 with
          | (univ_names1,binders1,tc) ->
              let uu____23850 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____23850)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____23885 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____23885 with
          | (univ_names1,binders1,tc) ->
              let uu____23945 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____23945)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____23978 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____23978 with
           | (univ_names1,binders1,typ1) ->
               let uu___202_24006 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___202_24006.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___202_24006.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___202_24006.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___202_24006.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___203_24027 = s  in
          let uu____24028 =
            let uu____24029 =
              let uu____24038 = FStar_List.map (elim_uvars env) sigs  in
              (uu____24038, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____24029  in
          {
            FStar_Syntax_Syntax.sigel = uu____24028;
            FStar_Syntax_Syntax.sigrng =
              (uu___203_24027.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___203_24027.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___203_24027.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___203_24027.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____24055 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24055 with
           | (univ_names1,uu____24073,typ1) ->
               let uu___204_24087 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_24087.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_24087.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_24087.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_24087.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24093 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24093 with
           | (univ_names1,uu____24111,typ1) ->
               let uu___205_24125 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_24125.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_24125.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_24125.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_24125.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24159 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24159 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24182 =
                            let uu____24183 =
                              let uu____24184 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24184  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24183
                             in
                          elim_delayed_subst_term uu____24182  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___206_24187 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___206_24187.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___206_24187.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___206_24187.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___206_24187.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___207_24188 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___207_24188.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_24188.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_24188.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_24188.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___208_24200 = s  in
          let uu____24201 =
            let uu____24202 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24202  in
          {
            FStar_Syntax_Syntax.sigel = uu____24201;
            FStar_Syntax_Syntax.sigrng =
              (uu___208_24200.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_24200.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_24200.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___208_24200.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24206 = elim_uvars_aux_t env us [] t  in
          (match uu____24206 with
           | (us1,uu____24224,t1) ->
               let uu___209_24238 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_24238.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_24238.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_24238.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_24238.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24239 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24241 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24241 with
           | (univs1,binders,signature) ->
               let uu____24269 =
                 let uu____24278 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24278 with
                 | (univs_opening,univs2) ->
                     let uu____24305 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24305)
                  in
               (match uu____24269 with
                | (univs_opening,univs_closing) ->
                    let uu____24322 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24328 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24329 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24328, uu____24329)  in
                    (match uu____24322 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24351 =
                           match uu____24351 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____24369 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____24369 with
                                | (us1,t1) ->
                                    let uu____24380 =
                                      let uu____24385 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____24392 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____24385, uu____24392)  in
                                    (match uu____24380 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24405 =
                                           let uu____24410 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24419 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24410, uu____24419)  in
                                         (match uu____24405 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24435 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24435
                                                 in
                                              let uu____24436 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24436 with
                                               | (uu____24457,uu____24458,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24473 =
                                                       let uu____24474 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24474
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24473
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24479 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24479 with
                           | (uu____24492,uu____24493,t1) -> t1  in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____24553 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24570 =
                               let uu____24571 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24571.FStar_Syntax_Syntax.n  in
                             match uu____24570 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____24630 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____24659 =
                               let uu____24660 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____24660.FStar_Syntax_Syntax.n  in
                             match uu____24659 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____24681) ->
                                 let uu____24702 = destruct_action_body body
                                    in
                                 (match uu____24702 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____24747 ->
                                 let uu____24748 = destruct_action_body t  in
                                 (match uu____24748 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____24797 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____24797 with
                           | (action_univs,t) ->
                               let uu____24806 = destruct_action_typ_templ t
                                  in
                               (match uu____24806 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___210_24847 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___210_24847.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___210_24847.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      }  in
                                    a')
                            in
                         let ed1 =
                           let uu___211_24849 = ed  in
                           let uu____24850 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____24851 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____24852 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____24853 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____24854 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____24855 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____24856 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____24857 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____24858 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____24859 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____24860 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____24861 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____24862 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____24863 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___211_24849.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___211_24849.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____24850;
                             FStar_Syntax_Syntax.bind_wp = uu____24851;
                             FStar_Syntax_Syntax.if_then_else = uu____24852;
                             FStar_Syntax_Syntax.ite_wp = uu____24853;
                             FStar_Syntax_Syntax.stronger = uu____24854;
                             FStar_Syntax_Syntax.close_wp = uu____24855;
                             FStar_Syntax_Syntax.assert_p = uu____24856;
                             FStar_Syntax_Syntax.assume_p = uu____24857;
                             FStar_Syntax_Syntax.null_wp = uu____24858;
                             FStar_Syntax_Syntax.trivial = uu____24859;
                             FStar_Syntax_Syntax.repr = uu____24860;
                             FStar_Syntax_Syntax.return_repr = uu____24861;
                             FStar_Syntax_Syntax.bind_repr = uu____24862;
                             FStar_Syntax_Syntax.actions = uu____24863;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___211_24849.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___212_24866 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___212_24866.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___212_24866.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___212_24866.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___212_24866.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_24883 =
            match uu___93_24883 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____24910 = elim_uvars_aux_t env us [] t  in
                (match uu____24910 with
                 | (us1,uu____24934,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___213_24953 = sub_eff  in
            let uu____24954 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____24957 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___213_24953.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___213_24953.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____24954;
              FStar_Syntax_Syntax.lift = uu____24957
            }  in
          let uu___214_24960 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___214_24960.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_24960.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_24960.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_24960.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____24970 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____24970 with
           | (univ_names1,binders1,comp1) ->
               let uu___215_25004 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_25004.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_25004.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_25004.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_25004.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25015 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25016 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  