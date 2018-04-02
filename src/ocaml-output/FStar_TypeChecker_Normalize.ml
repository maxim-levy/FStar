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
  | UnfoldFully of FStar_Ident.lid Prims.list 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____28 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____32 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____36 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____41 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____52 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____56 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____60 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____64 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____68 -> false
  
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____72 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____77 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____91 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____111 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____129 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____140 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____144 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____148 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____152 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____156 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____160 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____164 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____168 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____172 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____176 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____180 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____188 'Auu____189 .
    ('Auu____188 -> 'Auu____189) ->
      'Auu____189 ->
        'Auu____188 FStar_Pervasives_Native.option -> 'Auu____189
  =
  fun f  ->
    fun d  ->
      fun uu___77_206  ->
        match uu___77_206 with
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
  unfold_fully: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
  
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_fully = __fname__unfold_fully;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_fully
  
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
        unfold_fully = __fname__unfold_fully;
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
    unfold_fully = FStar_Pervasives_Native.None;
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
      let add_opt x uu___78_1226 =
        match uu___78_1226 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1246 = fs  in
          {
            beta = true;
            iota = (uu___96_1246.iota);
            zeta = (uu___96_1246.zeta);
            weak = (uu___96_1246.weak);
            hnf = (uu___96_1246.hnf);
            primops = (uu___96_1246.primops);
            no_delta_steps = (uu___96_1246.no_delta_steps);
            unfold_until = (uu___96_1246.unfold_until);
            unfold_only = (uu___96_1246.unfold_only);
            unfold_fully = (uu___96_1246.unfold_fully);
            unfold_attr = (uu___96_1246.unfold_attr);
            unfold_tac = (uu___96_1246.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1246.pure_subterms_within_computations);
            simplify = (uu___96_1246.simplify);
            erase_universes = (uu___96_1246.erase_universes);
            allow_unbound_universes = (uu___96_1246.allow_unbound_universes);
            reify_ = (uu___96_1246.reify_);
            compress_uvars = (uu___96_1246.compress_uvars);
            no_full_norm = (uu___96_1246.no_full_norm);
            check_no_uvars = (uu___96_1246.check_no_uvars);
            unmeta = (uu___96_1246.unmeta);
            unascribe = (uu___96_1246.unascribe)
          }
      | Iota  ->
          let uu___97_1247 = fs  in
          {
            beta = (uu___97_1247.beta);
            iota = true;
            zeta = (uu___97_1247.zeta);
            weak = (uu___97_1247.weak);
            hnf = (uu___97_1247.hnf);
            primops = (uu___97_1247.primops);
            no_delta_steps = (uu___97_1247.no_delta_steps);
            unfold_until = (uu___97_1247.unfold_until);
            unfold_only = (uu___97_1247.unfold_only);
            unfold_fully = (uu___97_1247.unfold_fully);
            unfold_attr = (uu___97_1247.unfold_attr);
            unfold_tac = (uu___97_1247.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1247.pure_subterms_within_computations);
            simplify = (uu___97_1247.simplify);
            erase_universes = (uu___97_1247.erase_universes);
            allow_unbound_universes = (uu___97_1247.allow_unbound_universes);
            reify_ = (uu___97_1247.reify_);
            compress_uvars = (uu___97_1247.compress_uvars);
            no_full_norm = (uu___97_1247.no_full_norm);
            check_no_uvars = (uu___97_1247.check_no_uvars);
            unmeta = (uu___97_1247.unmeta);
            unascribe = (uu___97_1247.unascribe)
          }
      | Zeta  ->
          let uu___98_1248 = fs  in
          {
            beta = (uu___98_1248.beta);
            iota = (uu___98_1248.iota);
            zeta = true;
            weak = (uu___98_1248.weak);
            hnf = (uu___98_1248.hnf);
            primops = (uu___98_1248.primops);
            no_delta_steps = (uu___98_1248.no_delta_steps);
            unfold_until = (uu___98_1248.unfold_until);
            unfold_only = (uu___98_1248.unfold_only);
            unfold_fully = (uu___98_1248.unfold_fully);
            unfold_attr = (uu___98_1248.unfold_attr);
            unfold_tac = (uu___98_1248.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1248.pure_subterms_within_computations);
            simplify = (uu___98_1248.simplify);
            erase_universes = (uu___98_1248.erase_universes);
            allow_unbound_universes = (uu___98_1248.allow_unbound_universes);
            reify_ = (uu___98_1248.reify_);
            compress_uvars = (uu___98_1248.compress_uvars);
            no_full_norm = (uu___98_1248.no_full_norm);
            check_no_uvars = (uu___98_1248.check_no_uvars);
            unmeta = (uu___98_1248.unmeta);
            unascribe = (uu___98_1248.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___99_1249 = fs  in
          {
            beta = false;
            iota = (uu___99_1249.iota);
            zeta = (uu___99_1249.zeta);
            weak = (uu___99_1249.weak);
            hnf = (uu___99_1249.hnf);
            primops = (uu___99_1249.primops);
            no_delta_steps = (uu___99_1249.no_delta_steps);
            unfold_until = (uu___99_1249.unfold_until);
            unfold_only = (uu___99_1249.unfold_only);
            unfold_fully = (uu___99_1249.unfold_fully);
            unfold_attr = (uu___99_1249.unfold_attr);
            unfold_tac = (uu___99_1249.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1249.pure_subterms_within_computations);
            simplify = (uu___99_1249.simplify);
            erase_universes = (uu___99_1249.erase_universes);
            allow_unbound_universes = (uu___99_1249.allow_unbound_universes);
            reify_ = (uu___99_1249.reify_);
            compress_uvars = (uu___99_1249.compress_uvars);
            no_full_norm = (uu___99_1249.no_full_norm);
            check_no_uvars = (uu___99_1249.check_no_uvars);
            unmeta = (uu___99_1249.unmeta);
            unascribe = (uu___99_1249.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___100_1250 = fs  in
          {
            beta = (uu___100_1250.beta);
            iota = false;
            zeta = (uu___100_1250.zeta);
            weak = (uu___100_1250.weak);
            hnf = (uu___100_1250.hnf);
            primops = (uu___100_1250.primops);
            no_delta_steps = (uu___100_1250.no_delta_steps);
            unfold_until = (uu___100_1250.unfold_until);
            unfold_only = (uu___100_1250.unfold_only);
            unfold_fully = (uu___100_1250.unfold_fully);
            unfold_attr = (uu___100_1250.unfold_attr);
            unfold_tac = (uu___100_1250.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1250.pure_subterms_within_computations);
            simplify = (uu___100_1250.simplify);
            erase_universes = (uu___100_1250.erase_universes);
            allow_unbound_universes = (uu___100_1250.allow_unbound_universes);
            reify_ = (uu___100_1250.reify_);
            compress_uvars = (uu___100_1250.compress_uvars);
            no_full_norm = (uu___100_1250.no_full_norm);
            check_no_uvars = (uu___100_1250.check_no_uvars);
            unmeta = (uu___100_1250.unmeta);
            unascribe = (uu___100_1250.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___101_1251 = fs  in
          {
            beta = (uu___101_1251.beta);
            iota = (uu___101_1251.iota);
            zeta = false;
            weak = (uu___101_1251.weak);
            hnf = (uu___101_1251.hnf);
            primops = (uu___101_1251.primops);
            no_delta_steps = (uu___101_1251.no_delta_steps);
            unfold_until = (uu___101_1251.unfold_until);
            unfold_only = (uu___101_1251.unfold_only);
            unfold_fully = (uu___101_1251.unfold_fully);
            unfold_attr = (uu___101_1251.unfold_attr);
            unfold_tac = (uu___101_1251.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1251.pure_subterms_within_computations);
            simplify = (uu___101_1251.simplify);
            erase_universes = (uu___101_1251.erase_universes);
            allow_unbound_universes = (uu___101_1251.allow_unbound_universes);
            reify_ = (uu___101_1251.reify_);
            compress_uvars = (uu___101_1251.compress_uvars);
            no_full_norm = (uu___101_1251.no_full_norm);
            check_no_uvars = (uu___101_1251.check_no_uvars);
            unmeta = (uu___101_1251.unmeta);
            unascribe = (uu___101_1251.unascribe)
          }
      | Exclude uu____1252 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1253 = fs  in
          {
            beta = (uu___102_1253.beta);
            iota = (uu___102_1253.iota);
            zeta = (uu___102_1253.zeta);
            weak = true;
            hnf = (uu___102_1253.hnf);
            primops = (uu___102_1253.primops);
            no_delta_steps = (uu___102_1253.no_delta_steps);
            unfold_until = (uu___102_1253.unfold_until);
            unfold_only = (uu___102_1253.unfold_only);
            unfold_fully = (uu___102_1253.unfold_fully);
            unfold_attr = (uu___102_1253.unfold_attr);
            unfold_tac = (uu___102_1253.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1253.pure_subterms_within_computations);
            simplify = (uu___102_1253.simplify);
            erase_universes = (uu___102_1253.erase_universes);
            allow_unbound_universes = (uu___102_1253.allow_unbound_universes);
            reify_ = (uu___102_1253.reify_);
            compress_uvars = (uu___102_1253.compress_uvars);
            no_full_norm = (uu___102_1253.no_full_norm);
            check_no_uvars = (uu___102_1253.check_no_uvars);
            unmeta = (uu___102_1253.unmeta);
            unascribe = (uu___102_1253.unascribe)
          }
      | HNF  ->
          let uu___103_1254 = fs  in
          {
            beta = (uu___103_1254.beta);
            iota = (uu___103_1254.iota);
            zeta = (uu___103_1254.zeta);
            weak = (uu___103_1254.weak);
            hnf = true;
            primops = (uu___103_1254.primops);
            no_delta_steps = (uu___103_1254.no_delta_steps);
            unfold_until = (uu___103_1254.unfold_until);
            unfold_only = (uu___103_1254.unfold_only);
            unfold_fully = (uu___103_1254.unfold_fully);
            unfold_attr = (uu___103_1254.unfold_attr);
            unfold_tac = (uu___103_1254.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1254.pure_subterms_within_computations);
            simplify = (uu___103_1254.simplify);
            erase_universes = (uu___103_1254.erase_universes);
            allow_unbound_universes = (uu___103_1254.allow_unbound_universes);
            reify_ = (uu___103_1254.reify_);
            compress_uvars = (uu___103_1254.compress_uvars);
            no_full_norm = (uu___103_1254.no_full_norm);
            check_no_uvars = (uu___103_1254.check_no_uvars);
            unmeta = (uu___103_1254.unmeta);
            unascribe = (uu___103_1254.unascribe)
          }
      | Primops  ->
          let uu___104_1255 = fs  in
          {
            beta = (uu___104_1255.beta);
            iota = (uu___104_1255.iota);
            zeta = (uu___104_1255.zeta);
            weak = (uu___104_1255.weak);
            hnf = (uu___104_1255.hnf);
            primops = true;
            no_delta_steps = (uu___104_1255.no_delta_steps);
            unfold_until = (uu___104_1255.unfold_until);
            unfold_only = (uu___104_1255.unfold_only);
            unfold_fully = (uu___104_1255.unfold_fully);
            unfold_attr = (uu___104_1255.unfold_attr);
            unfold_tac = (uu___104_1255.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1255.pure_subterms_within_computations);
            simplify = (uu___104_1255.simplify);
            erase_universes = (uu___104_1255.erase_universes);
            allow_unbound_universes = (uu___104_1255.allow_unbound_universes);
            reify_ = (uu___104_1255.reify_);
            compress_uvars = (uu___104_1255.compress_uvars);
            no_full_norm = (uu___104_1255.no_full_norm);
            check_no_uvars = (uu___104_1255.check_no_uvars);
            unmeta = (uu___104_1255.unmeta);
            unascribe = (uu___104_1255.unascribe)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | NoDeltaSteps  ->
          let uu___105_1256 = fs  in
          {
            beta = (uu___105_1256.beta);
            iota = (uu___105_1256.iota);
            zeta = (uu___105_1256.zeta);
            weak = (uu___105_1256.weak);
            hnf = (uu___105_1256.hnf);
            primops = (uu___105_1256.primops);
            no_delta_steps = true;
            unfold_until = (uu___105_1256.unfold_until);
            unfold_only = (uu___105_1256.unfold_only);
            unfold_fully = (uu___105_1256.unfold_fully);
            unfold_attr = (uu___105_1256.unfold_attr);
            unfold_tac = (uu___105_1256.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1256.pure_subterms_within_computations);
            simplify = (uu___105_1256.simplify);
            erase_universes = (uu___105_1256.erase_universes);
            allow_unbound_universes = (uu___105_1256.allow_unbound_universes);
            reify_ = (uu___105_1256.reify_);
            compress_uvars = (uu___105_1256.compress_uvars);
            no_full_norm = (uu___105_1256.no_full_norm);
            check_no_uvars = (uu___105_1256.check_no_uvars);
            unmeta = (uu___105_1256.unmeta);
            unascribe = (uu___105_1256.unascribe)
          }
      | UnfoldUntil d ->
          let uu___106_1258 = fs  in
          {
            beta = (uu___106_1258.beta);
            iota = (uu___106_1258.iota);
            zeta = (uu___106_1258.zeta);
            weak = (uu___106_1258.weak);
            hnf = (uu___106_1258.hnf);
            primops = (uu___106_1258.primops);
            no_delta_steps = (uu___106_1258.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1258.unfold_only);
            unfold_fully = (uu___106_1258.unfold_fully);
            unfold_attr = (uu___106_1258.unfold_attr);
            unfold_tac = (uu___106_1258.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1258.pure_subterms_within_computations);
            simplify = (uu___106_1258.simplify);
            erase_universes = (uu___106_1258.erase_universes);
            allow_unbound_universes = (uu___106_1258.allow_unbound_universes);
            reify_ = (uu___106_1258.reify_);
            compress_uvars = (uu___106_1258.compress_uvars);
            no_full_norm = (uu___106_1258.no_full_norm);
            check_no_uvars = (uu___106_1258.check_no_uvars);
            unmeta = (uu___106_1258.unmeta);
            unascribe = (uu___106_1258.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___107_1262 = fs  in
          {
            beta = (uu___107_1262.beta);
            iota = (uu___107_1262.iota);
            zeta = (uu___107_1262.zeta);
            weak = (uu___107_1262.weak);
            hnf = (uu___107_1262.hnf);
            primops = (uu___107_1262.primops);
            no_delta_steps = (uu___107_1262.no_delta_steps);
            unfold_until = (uu___107_1262.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1262.unfold_fully);
            unfold_attr = (uu___107_1262.unfold_attr);
            unfold_tac = (uu___107_1262.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1262.pure_subterms_within_computations);
            simplify = (uu___107_1262.simplify);
            erase_universes = (uu___107_1262.erase_universes);
            allow_unbound_universes = (uu___107_1262.allow_unbound_universes);
            reify_ = (uu___107_1262.reify_);
            compress_uvars = (uu___107_1262.compress_uvars);
            no_full_norm = (uu___107_1262.no_full_norm);
            check_no_uvars = (uu___107_1262.check_no_uvars);
            unmeta = (uu___107_1262.unmeta);
            unascribe = (uu___107_1262.unascribe)
          }
      | UnfoldFully lids ->
          let uu___108_1268 = fs  in
          {
            beta = (uu___108_1268.beta);
            iota = (uu___108_1268.iota);
            zeta = (uu___108_1268.zeta);
            weak = (uu___108_1268.weak);
            hnf = (uu___108_1268.hnf);
            primops = (uu___108_1268.primops);
            no_delta_steps = (uu___108_1268.no_delta_steps);
            unfold_until = (uu___108_1268.unfold_until);
            unfold_only = (uu___108_1268.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1268.unfold_attr);
            unfold_tac = (uu___108_1268.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1268.pure_subterms_within_computations);
            simplify = (uu___108_1268.simplify);
            erase_universes = (uu___108_1268.erase_universes);
            allow_unbound_universes = (uu___108_1268.allow_unbound_universes);
            reify_ = (uu___108_1268.reify_);
            compress_uvars = (uu___108_1268.compress_uvars);
            no_full_norm = (uu___108_1268.no_full_norm);
            check_no_uvars = (uu___108_1268.check_no_uvars);
            unmeta = (uu___108_1268.unmeta);
            unascribe = (uu___108_1268.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___109_1272 = fs  in
          {
            beta = (uu___109_1272.beta);
            iota = (uu___109_1272.iota);
            zeta = (uu___109_1272.zeta);
            weak = (uu___109_1272.weak);
            hnf = (uu___109_1272.hnf);
            primops = (uu___109_1272.primops);
            no_delta_steps = (uu___109_1272.no_delta_steps);
            unfold_until = (uu___109_1272.unfold_until);
            unfold_only = (uu___109_1272.unfold_only);
            unfold_fully = (uu___109_1272.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1272.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1272.pure_subterms_within_computations);
            simplify = (uu___109_1272.simplify);
            erase_universes = (uu___109_1272.erase_universes);
            allow_unbound_universes = (uu___109_1272.allow_unbound_universes);
            reify_ = (uu___109_1272.reify_);
            compress_uvars = (uu___109_1272.compress_uvars);
            no_full_norm = (uu___109_1272.no_full_norm);
            check_no_uvars = (uu___109_1272.check_no_uvars);
            unmeta = (uu___109_1272.unmeta);
            unascribe = (uu___109_1272.unascribe)
          }
      | UnfoldTac  ->
          let uu___110_1273 = fs  in
          {
            beta = (uu___110_1273.beta);
            iota = (uu___110_1273.iota);
            zeta = (uu___110_1273.zeta);
            weak = (uu___110_1273.weak);
            hnf = (uu___110_1273.hnf);
            primops = (uu___110_1273.primops);
            no_delta_steps = (uu___110_1273.no_delta_steps);
            unfold_until = (uu___110_1273.unfold_until);
            unfold_only = (uu___110_1273.unfold_only);
            unfold_fully = (uu___110_1273.unfold_fully);
            unfold_attr = (uu___110_1273.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1273.pure_subterms_within_computations);
            simplify = (uu___110_1273.simplify);
            erase_universes = (uu___110_1273.erase_universes);
            allow_unbound_universes = (uu___110_1273.allow_unbound_universes);
            reify_ = (uu___110_1273.reify_);
            compress_uvars = (uu___110_1273.compress_uvars);
            no_full_norm = (uu___110_1273.no_full_norm);
            check_no_uvars = (uu___110_1273.check_no_uvars);
            unmeta = (uu___110_1273.unmeta);
            unascribe = (uu___110_1273.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1274 = fs  in
          {
            beta = (uu___111_1274.beta);
            iota = (uu___111_1274.iota);
            zeta = (uu___111_1274.zeta);
            weak = (uu___111_1274.weak);
            hnf = (uu___111_1274.hnf);
            primops = (uu___111_1274.primops);
            no_delta_steps = (uu___111_1274.no_delta_steps);
            unfold_until = (uu___111_1274.unfold_until);
            unfold_only = (uu___111_1274.unfold_only);
            unfold_fully = (uu___111_1274.unfold_fully);
            unfold_attr = (uu___111_1274.unfold_attr);
            unfold_tac = (uu___111_1274.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1274.simplify);
            erase_universes = (uu___111_1274.erase_universes);
            allow_unbound_universes = (uu___111_1274.allow_unbound_universes);
            reify_ = (uu___111_1274.reify_);
            compress_uvars = (uu___111_1274.compress_uvars);
            no_full_norm = (uu___111_1274.no_full_norm);
            check_no_uvars = (uu___111_1274.check_no_uvars);
            unmeta = (uu___111_1274.unmeta);
            unascribe = (uu___111_1274.unascribe)
          }
      | Simplify  ->
          let uu___112_1275 = fs  in
          {
            beta = (uu___112_1275.beta);
            iota = (uu___112_1275.iota);
            zeta = (uu___112_1275.zeta);
            weak = (uu___112_1275.weak);
            hnf = (uu___112_1275.hnf);
            primops = (uu___112_1275.primops);
            no_delta_steps = (uu___112_1275.no_delta_steps);
            unfold_until = (uu___112_1275.unfold_until);
            unfold_only = (uu___112_1275.unfold_only);
            unfold_fully = (uu___112_1275.unfold_fully);
            unfold_attr = (uu___112_1275.unfold_attr);
            unfold_tac = (uu___112_1275.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1275.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1275.erase_universes);
            allow_unbound_universes = (uu___112_1275.allow_unbound_universes);
            reify_ = (uu___112_1275.reify_);
            compress_uvars = (uu___112_1275.compress_uvars);
            no_full_norm = (uu___112_1275.no_full_norm);
            check_no_uvars = (uu___112_1275.check_no_uvars);
            unmeta = (uu___112_1275.unmeta);
            unascribe = (uu___112_1275.unascribe)
          }
      | EraseUniverses  ->
          let uu___113_1276 = fs  in
          {
            beta = (uu___113_1276.beta);
            iota = (uu___113_1276.iota);
            zeta = (uu___113_1276.zeta);
            weak = (uu___113_1276.weak);
            hnf = (uu___113_1276.hnf);
            primops = (uu___113_1276.primops);
            no_delta_steps = (uu___113_1276.no_delta_steps);
            unfold_until = (uu___113_1276.unfold_until);
            unfold_only = (uu___113_1276.unfold_only);
            unfold_fully = (uu___113_1276.unfold_fully);
            unfold_attr = (uu___113_1276.unfold_attr);
            unfold_tac = (uu___113_1276.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1276.pure_subterms_within_computations);
            simplify = (uu___113_1276.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1276.allow_unbound_universes);
            reify_ = (uu___113_1276.reify_);
            compress_uvars = (uu___113_1276.compress_uvars);
            no_full_norm = (uu___113_1276.no_full_norm);
            check_no_uvars = (uu___113_1276.check_no_uvars);
            unmeta = (uu___113_1276.unmeta);
            unascribe = (uu___113_1276.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1277 = fs  in
          {
            beta = (uu___114_1277.beta);
            iota = (uu___114_1277.iota);
            zeta = (uu___114_1277.zeta);
            weak = (uu___114_1277.weak);
            hnf = (uu___114_1277.hnf);
            primops = (uu___114_1277.primops);
            no_delta_steps = (uu___114_1277.no_delta_steps);
            unfold_until = (uu___114_1277.unfold_until);
            unfold_only = (uu___114_1277.unfold_only);
            unfold_fully = (uu___114_1277.unfold_fully);
            unfold_attr = (uu___114_1277.unfold_attr);
            unfold_tac = (uu___114_1277.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1277.pure_subterms_within_computations);
            simplify = (uu___114_1277.simplify);
            erase_universes = (uu___114_1277.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1277.reify_);
            compress_uvars = (uu___114_1277.compress_uvars);
            no_full_norm = (uu___114_1277.no_full_norm);
            check_no_uvars = (uu___114_1277.check_no_uvars);
            unmeta = (uu___114_1277.unmeta);
            unascribe = (uu___114_1277.unascribe)
          }
      | Reify  ->
          let uu___115_1278 = fs  in
          {
            beta = (uu___115_1278.beta);
            iota = (uu___115_1278.iota);
            zeta = (uu___115_1278.zeta);
            weak = (uu___115_1278.weak);
            hnf = (uu___115_1278.hnf);
            primops = (uu___115_1278.primops);
            no_delta_steps = (uu___115_1278.no_delta_steps);
            unfold_until = (uu___115_1278.unfold_until);
            unfold_only = (uu___115_1278.unfold_only);
            unfold_fully = (uu___115_1278.unfold_fully);
            unfold_attr = (uu___115_1278.unfold_attr);
            unfold_tac = (uu___115_1278.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1278.pure_subterms_within_computations);
            simplify = (uu___115_1278.simplify);
            erase_universes = (uu___115_1278.erase_universes);
            allow_unbound_universes = (uu___115_1278.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1278.compress_uvars);
            no_full_norm = (uu___115_1278.no_full_norm);
            check_no_uvars = (uu___115_1278.check_no_uvars);
            unmeta = (uu___115_1278.unmeta);
            unascribe = (uu___115_1278.unascribe)
          }
      | CompressUvars  ->
          let uu___116_1279 = fs  in
          {
            beta = (uu___116_1279.beta);
            iota = (uu___116_1279.iota);
            zeta = (uu___116_1279.zeta);
            weak = (uu___116_1279.weak);
            hnf = (uu___116_1279.hnf);
            primops = (uu___116_1279.primops);
            no_delta_steps = (uu___116_1279.no_delta_steps);
            unfold_until = (uu___116_1279.unfold_until);
            unfold_only = (uu___116_1279.unfold_only);
            unfold_fully = (uu___116_1279.unfold_fully);
            unfold_attr = (uu___116_1279.unfold_attr);
            unfold_tac = (uu___116_1279.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1279.pure_subterms_within_computations);
            simplify = (uu___116_1279.simplify);
            erase_universes = (uu___116_1279.erase_universes);
            allow_unbound_universes = (uu___116_1279.allow_unbound_universes);
            reify_ = (uu___116_1279.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1279.no_full_norm);
            check_no_uvars = (uu___116_1279.check_no_uvars);
            unmeta = (uu___116_1279.unmeta);
            unascribe = (uu___116_1279.unascribe)
          }
      | NoFullNorm  ->
          let uu___117_1280 = fs  in
          {
            beta = (uu___117_1280.beta);
            iota = (uu___117_1280.iota);
            zeta = (uu___117_1280.zeta);
            weak = (uu___117_1280.weak);
            hnf = (uu___117_1280.hnf);
            primops = (uu___117_1280.primops);
            no_delta_steps = (uu___117_1280.no_delta_steps);
            unfold_until = (uu___117_1280.unfold_until);
            unfold_only = (uu___117_1280.unfold_only);
            unfold_fully = (uu___117_1280.unfold_fully);
            unfold_attr = (uu___117_1280.unfold_attr);
            unfold_tac = (uu___117_1280.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1280.pure_subterms_within_computations);
            simplify = (uu___117_1280.simplify);
            erase_universes = (uu___117_1280.erase_universes);
            allow_unbound_universes = (uu___117_1280.allow_unbound_universes);
            reify_ = (uu___117_1280.reify_);
            compress_uvars = (uu___117_1280.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1280.check_no_uvars);
            unmeta = (uu___117_1280.unmeta);
            unascribe = (uu___117_1280.unascribe)
          }
      | CheckNoUvars  ->
          let uu___118_1281 = fs  in
          {
            beta = (uu___118_1281.beta);
            iota = (uu___118_1281.iota);
            zeta = (uu___118_1281.zeta);
            weak = (uu___118_1281.weak);
            hnf = (uu___118_1281.hnf);
            primops = (uu___118_1281.primops);
            no_delta_steps = (uu___118_1281.no_delta_steps);
            unfold_until = (uu___118_1281.unfold_until);
            unfold_only = (uu___118_1281.unfold_only);
            unfold_fully = (uu___118_1281.unfold_fully);
            unfold_attr = (uu___118_1281.unfold_attr);
            unfold_tac = (uu___118_1281.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1281.pure_subterms_within_computations);
            simplify = (uu___118_1281.simplify);
            erase_universes = (uu___118_1281.erase_universes);
            allow_unbound_universes = (uu___118_1281.allow_unbound_universes);
            reify_ = (uu___118_1281.reify_);
            compress_uvars = (uu___118_1281.compress_uvars);
            no_full_norm = (uu___118_1281.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1281.unmeta);
            unascribe = (uu___118_1281.unascribe)
          }
      | Unmeta  ->
          let uu___119_1282 = fs  in
          {
            beta = (uu___119_1282.beta);
            iota = (uu___119_1282.iota);
            zeta = (uu___119_1282.zeta);
            weak = (uu___119_1282.weak);
            hnf = (uu___119_1282.hnf);
            primops = (uu___119_1282.primops);
            no_delta_steps = (uu___119_1282.no_delta_steps);
            unfold_until = (uu___119_1282.unfold_until);
            unfold_only = (uu___119_1282.unfold_only);
            unfold_fully = (uu___119_1282.unfold_fully);
            unfold_attr = (uu___119_1282.unfold_attr);
            unfold_tac = (uu___119_1282.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1282.pure_subterms_within_computations);
            simplify = (uu___119_1282.simplify);
            erase_universes = (uu___119_1282.erase_universes);
            allow_unbound_universes = (uu___119_1282.allow_unbound_universes);
            reify_ = (uu___119_1282.reify_);
            compress_uvars = (uu___119_1282.compress_uvars);
            no_full_norm = (uu___119_1282.no_full_norm);
            check_no_uvars = (uu___119_1282.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1282.unascribe)
          }
      | Unascribe  ->
          let uu___120_1283 = fs  in
          {
            beta = (uu___120_1283.beta);
            iota = (uu___120_1283.iota);
            zeta = (uu___120_1283.zeta);
            weak = (uu___120_1283.weak);
            hnf = (uu___120_1283.hnf);
            primops = (uu___120_1283.primops);
            no_delta_steps = (uu___120_1283.no_delta_steps);
            unfold_until = (uu___120_1283.unfold_until);
            unfold_only = (uu___120_1283.unfold_only);
            unfold_fully = (uu___120_1283.unfold_fully);
            unfold_attr = (uu___120_1283.unfold_attr);
            unfold_tac = (uu___120_1283.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1283.pure_subterms_within_computations);
            simplify = (uu___120_1283.simplify);
            erase_universes = (uu___120_1283.erase_universes);
            allow_unbound_universes = (uu___120_1283.allow_unbound_universes);
            reify_ = (uu___120_1283.reify_);
            compress_uvars = (uu___120_1283.compress_uvars);
            no_full_norm = (uu___120_1283.no_full_norm);
            check_no_uvars = (uu___120_1283.check_no_uvars);
            unmeta = (uu___120_1283.unmeta);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1322  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1565 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1667 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1678 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___79_1697  ->
    match uu___79_1697 with
    | Clos (uu____1698,t,uu____1700,uu____1701) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1746 -> "Univ"
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
             let uu____1998 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____1998 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2010 = FStar_Util.psmap_empty ()  in add_steps uu____2010 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2021 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2021
  
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
  FStar_Pervasives_Native.tuple2 
  | AscribedBy of
  (env,FStar_Syntax_Syntax.ascription,FStar_Ident.lid
                                        FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple4 
  | RefinedBy of
  (FStar_Syntax_Syntax.bv,env,FStar_Syntax_Syntax.term,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Refining of (FStar_Syntax_Syntax.bv,FStar_Range.range,env)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____2199 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2235 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2271 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2340 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2382 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2438 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2478 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2510 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2546 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2562 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
let (uu___is_AscribedBy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | AscribedBy _0 -> true | uu____2596 -> false
  
let (__proj__AscribedBy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.ascription,FStar_Ident.lid
                                          FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | AscribedBy _0 -> _0 
let (uu___is_RefinedBy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | RefinedBy _0 -> true | uu____2646 -> false
  
let (__proj__RefinedBy__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.bv,env,FStar_Syntax_Syntax.term,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | RefinedBy _0 -> _0 
let (uu___is_Refining : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refining _0 -> true | uu____2688 -> false
  
let (__proj__Refining__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.bv,FStar_Range.range,env)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Refining _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2719 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2719 with | (hd1,uu____2733) -> hd1
  
let mk :
  'Auu____2753 .
    'Auu____2753 ->
      FStar_Range.range -> 'Auu____2753 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2807 = FStar_ST.op_Bang r  in
          match uu____2807 with
          | FStar_Pervasives_Native.Some uu____2855 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2909 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2909 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2916  ->
    match uu___80_2916 with
    | Arg (c,uu____2918,uu____2919) ->
        let uu____2920 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2920
    | MemoLazy uu____2921 -> "MemoLazy"
    | Abs (uu____2928,bs,uu____2930,uu____2931,uu____2932) ->
        let uu____2937 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2937
    | UnivArgs uu____2942 -> "UnivArgs"
    | Match uu____2949 -> "Match"
    | App (uu____2956,t,uu____2958,uu____2959) ->
        let uu____2960 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2960
    | Meta (m,uu____2962) -> "Meta"
    | Let uu____2963 -> "Let"
    | Cfg uu____2972 -> "Cfg"
    | Debug (t,uu____2974) ->
        let uu____2975 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2975
    | AscribedBy uu____2976 -> "AscribedBy"
    | RefinedBy uu____2987 -> "RefinedBy"
    | Refining uu____2996 -> "Refining"
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3010 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3010 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3041 . 'Auu____3041 Prims.list -> Prims.bool =
  fun uu___81_3047  ->
    match uu___81_3047 with | [] -> true | uu____3050 -> false
  
let lookup_bvar :
  'Auu____3057 'Auu____3058 .
    ('Auu____3057,'Auu____3058) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____3058
  =
  fun env  ->
    fun x  ->
      try
        let uu____3082 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3082
      with
      | uu____3095 ->
          let uu____3096 =
            let uu____3097 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____3097  in
          failwith uu____3096
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3103 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3103
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3107 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3107
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3111 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3111
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
  
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____3137 =
            FStar_List.fold_left
              (fun uu____3163  ->
                 fun u1  ->
                   match uu____3163 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3188 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3188 with
                        | (k_u,n1) ->
                            let uu____3203 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3203
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3137 with
          | (uu____3221,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3246 =
                   let uu____3247 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3247  in
                 match uu____3246 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3265 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3273 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3279 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3288 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3297 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3304 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3304 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3321 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3321 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3329 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3337 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3337 with
                                  | (uu____3342,m) -> n1 <= m))
                           in
                        if uu____3329 then rest1 else us1
                    | uu____3347 -> us1)
               | uu____3352 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3356 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3356
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3360 = aux u  in
           match uu____3360 with
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
          (fun uu____3464  ->
             let uu____3465 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3466 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3465
               uu____3466);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3473 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3475 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3500 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3501 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3502 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3503 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3504 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3521 =
                      let uu____3522 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3523 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3522 uu____3523
                       in
                    failwith uu____3521
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3526 =
                    let uu____3527 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3527  in
                  mk uu____3526 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3534 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3534
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3536 = lookup_bvar env x  in
                  (match uu____3536 with
                   | Univ uu____3539 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3542,uu____3543) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3655 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3655 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3683 =
                         let uu____3684 =
                           let uu____3701 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3701)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3684  in
                       mk uu____3683 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3732 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3732 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3774 =
                    let uu____3785 =
                      let uu____3792 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3792]  in
                    closures_as_binders_delayed cfg env uu____3785  in
                  (match uu____3774 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3810 =
                         let uu____3811 =
                           let uu____3818 =
                             let uu____3819 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3819
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3818, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3811  in
                       mk uu____3810 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3910 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3910
                    | FStar_Util.Inr c ->
                        let uu____3924 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3924
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3940 =
                    let uu____3941 =
                      let uu____3968 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3968, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3941  in
                  mk uu____3940 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                  (match qi.FStar_Syntax_Syntax.qkind with
                   | FStar_Syntax_Syntax.Quote_dynamic  ->
                       let uu____4009 =
                         let uu____4010 =
                           let uu____4017 =
                             closure_as_term_delayed cfg env t'  in
                           (uu____4017, qi)  in
                         FStar_Syntax_Syntax.Tm_quoted uu____4010  in
                       mk uu____4009 t1.FStar_Syntax_Syntax.pos
                   | FStar_Syntax_Syntax.Quote_static  ->
                       let qi1 =
                         FStar_Syntax_Syntax.on_antiquoted
                           (closure_as_term_delayed cfg env) qi
                          in
                       mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____4041 =
                    let uu____4042 =
                      let uu____4049 = closure_as_term_delayed cfg env t'  in
                      let uu____4052 =
                        let uu____4053 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____4053  in
                      (uu____4049, uu____4052)  in
                    FStar_Syntax_Syntax.Tm_meta uu____4042  in
                  mk uu____4041 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____4113 =
                    let uu____4114 =
                      let uu____4121 = closure_as_term_delayed cfg env t'  in
                      let uu____4124 =
                        let uu____4125 =
                          let uu____4132 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____4132)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____4125  in
                      (uu____4121, uu____4124)  in
                    FStar_Syntax_Syntax.Tm_meta uu____4114  in
                  mk uu____4113 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____4151 =
                    let uu____4152 =
                      let uu____4159 = closure_as_term_delayed cfg env t'  in
                      let uu____4162 =
                        let uu____4163 =
                          let uu____4172 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____4172)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____4163  in
                      (uu____4159, uu____4162)  in
                    FStar_Syntax_Syntax.Tm_meta uu____4152  in
                  mk uu____4151 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____4185 =
                    let uu____4186 =
                      let uu____4193 = closure_as_term_delayed cfg env t'  in
                      (uu____4193, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____4186  in
                  mk uu____4185 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____4233  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____4252 =
                    let uu____4263 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____4263
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____4282 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___125_4294 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_4294.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_4294.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____4282))
                     in
                  (match uu____4252 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___126_4310 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___126_4310.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___126_4310.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___126_4310.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___126_4310.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____4321,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4380  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4405 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4405
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4425  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4447 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4447
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___127_4459 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_4459.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_4459.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___128_4460 = lb  in
                    let uu____4461 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___128_4460.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___128_4460.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4461;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___128_4460.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___128_4460.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4491  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4580 =
                    match uu____4580 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4635 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4656 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4716  ->
                                        fun uu____4717  ->
                                          match (uu____4716, uu____4717) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4808 =
                                                norm_pat env3 p1  in
                                              (match uu____4808 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4656 with
                               | (pats1,env3) ->
                                   ((let uu___129_4890 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___129_4890.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___130_4909 = x  in
                                let uu____4910 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___130_4909.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___130_4909.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4910
                                }  in
                              ((let uu___131_4924 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___131_4924.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___132_4935 = x  in
                                let uu____4936 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___132_4935.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___132_4935.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4936
                                }  in
                              ((let uu___133_4950 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___133_4950.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___134_4966 = x  in
                                let uu____4967 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___134_4966.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___134_4966.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4967
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___135_4974 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___135_4974.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4977 = norm_pat env1 pat  in
                        (match uu____4977 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____5006 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____5006
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____5012 =
                    let uu____5013 =
                      let uu____5036 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____5036)  in
                    FStar_Syntax_Syntax.Tm_match uu____5013  in
                  mk uu____5012 t1.FStar_Syntax_Syntax.pos))

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
        | uu____5122 -> closure_as_term cfg env t

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
        | uu____5148 ->
            FStar_List.map
              (fun uu____5165  ->
                 match uu____5165 with
                 | (x,imp) ->
                     let uu____5184 = closure_as_term_delayed cfg env x  in
                     (uu____5184, imp)) args

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
        let uu____5198 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5247  ->
                  fun uu____5248  ->
                    match (uu____5247, uu____5248) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___136_5318 = b  in
                          let uu____5319 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___136_5318.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___136_5318.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5319
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5198 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5412 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5425 = closure_as_term_delayed cfg env t  in
                 let uu____5426 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5425 uu____5426
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5439 = closure_as_term_delayed cfg env t  in
                 let uu____5440 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5439 uu____5440
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
                        (fun uu___82_5466  ->
                           match uu___82_5466 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5470 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5470
                           | f -> f))
                    in
                 let uu____5474 =
                   let uu___137_5475 = c1  in
                   let uu____5476 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5476;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___137_5475.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5474)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5486  ->
            match uu___83_5486 with
            | FStar_Syntax_Syntax.DECREASES uu____5487 -> false
            | uu____5490 -> true))

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
                   (fun uu___84_5508  ->
                      match uu___84_5508 with
                      | FStar_Syntax_Syntax.DECREASES uu____5509 -> false
                      | uu____5512 -> true))
               in
            let rc1 =
              let uu___138_5514 = rc  in
              let uu____5515 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___138_5514.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5515;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5522 -> lopt

let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_int)
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_bool)
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_char)
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_string)
     in
  let arg_as_list a e a =
    let uu____5604 =
      let uu____5611 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____5611  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5604  in
  let arg_as_bounded_int uu____5635 =
    match uu____5635 with
    | (a,uu____5647) ->
        let uu____5654 =
          let uu____5655 = FStar_Syntax_Subst.compress a  in
          uu____5655.FStar_Syntax_Syntax.n  in
        (match uu____5654 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5665;
                FStar_Syntax_Syntax.vars = uu____5666;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5668;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5669;_},uu____5670)::[])
             when
             let uu____5709 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5709 "int_to_t" ->
             let uu____5710 =
               let uu____5715 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5715)  in
             FStar_Pervasives_Native.Some uu____5710
         | uu____5720 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5760 = f a  in FStar_Pervasives_Native.Some uu____5760
    | uu____5761 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5809 = f a0 a1  in FStar_Pervasives_Native.Some uu____5809
    | uu____5810 -> FStar_Pervasives_Native.None  in
  let unary_op a394 a395 a396 a397 a398 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5852 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a393  -> (Obj.magic (f res.psc_range)) a393)
                    uu____5852)) a394 a395 a396 a397 a398
     in
  let binary_op a401 a402 a403 a404 a405 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5901 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a399  ->
                       fun a400  -> (Obj.magic (f res.psc_range)) a399 a400)
                    uu____5901)) a401 a402 a403 a404 a405
     in
  let as_primitive_step is_strong uu____5928 =
    match uu____5928 with
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
    unary_op () (fun a406  -> (Obj.magic arg_as_int) a406)
      (fun a407  ->
         fun a408  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5976 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____5976)) a407 a408)
     in
  let binary_int_op f =
    binary_op () (fun a409  -> (Obj.magic arg_as_int) a409)
      (fun a410  ->
         fun a411  ->
           fun a412  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6004 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____6004)) a410
               a411 a412)
     in
  let unary_bool_op f =
    unary_op () (fun a413  -> (Obj.magic arg_as_bool) a413)
      (fun a414  ->
         fun a415  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6025 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____6025)) a414 a415)
     in
  let binary_bool_op f =
    binary_op () (fun a416  -> (Obj.magic arg_as_bool) a416)
      (fun a417  ->
         fun a418  ->
           fun a419  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6053 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____6053)) a417
               a418 a419)
     in
  let binary_string_op f =
    binary_op () (fun a420  -> (Obj.magic arg_as_string) a420)
      (fun a421  ->
         fun a422  ->
           fun a423  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6081 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____6081)) a421
               a422 a423)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____6189 =
          let uu____6198 = as_a a  in
          let uu____6201 = as_b b  in (uu____6198, uu____6201)  in
        (match uu____6189 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6216 =
               let uu____6217 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6217  in
             FStar_Pervasives_Native.Some uu____6216
         | uu____6218 -> FStar_Pervasives_Native.None)
    | uu____6227 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____6241 =
        let uu____6242 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____6242  in
      mk uu____6241 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____6252 =
      let uu____6255 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____6255  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6252  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____6287 =
      let uu____6288 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____6288  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____6287
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6308 = arg_as_string a1  in
        (match uu____6308 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6314 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2)
                in
             (match uu____6314 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6327 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____6327
              | uu____6328 -> FStar_Pervasives_Native.None)
         | uu____6333 -> FStar_Pervasives_Native.None)
    | uu____6336 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____6346 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____6346
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6377 =
          let uu____6398 = arg_as_string fn  in
          let uu____6401 = arg_as_int from_line  in
          let uu____6404 = arg_as_int from_col  in
          let uu____6407 = arg_as_int to_line  in
          let uu____6410 = arg_as_int to_col  in
          (uu____6398, uu____6401, uu____6404, uu____6407, uu____6410)  in
        (match uu____6377 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6441 =
                 let uu____6442 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6443 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6442 uu____6443  in
               let uu____6444 =
                 let uu____6445 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6446 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6445 uu____6446  in
               FStar_Range.mk_range fn1 uu____6441 uu____6444  in
             let uu____6447 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6447
         | uu____6448 -> FStar_Pervasives_Native.None)
    | uu____6469 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6496)::(a1,uu____6498)::(a2,uu____6500)::[] ->
        let uu____6537 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6537 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6550 -> FStar_Pervasives_Native.None)
    | uu____6551 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6580)::[] ->
        let uu____6589 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____6589 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6595 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6595
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6596 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6620 =
      let uu____6635 =
        let uu____6650 =
          let uu____6665 =
            let uu____6680 =
              let uu____6695 =
                let uu____6710 =
                  let uu____6725 =
                    let uu____6740 =
                      let uu____6755 =
                        let uu____6770 =
                          let uu____6785 =
                            let uu____6800 =
                              let uu____6815 =
                                let uu____6830 =
                                  let uu____6845 =
                                    let uu____6860 =
                                      let uu____6875 =
                                        let uu____6890 =
                                          let uu____6905 =
                                            let uu____6920 =
                                              let uu____6935 =
                                                let uu____6948 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6948,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a424  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a424)
                                                     (fun a425  ->
                                                        fun a426  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a425 a426)))
                                                 in
                                              let uu____6955 =
                                                let uu____6970 =
                                                  let uu____6983 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6983,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a427  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_char)))
                                                            a427)
                                                       (fun a428  ->
                                                          fun a429  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a428 a429)))
                                                   in
                                                let uu____6990 =
                                                  let uu____7005 =
                                                    let uu____7020 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____7020,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____7029 =
                                                    let uu____7046 =
                                                      let uu____7061 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____7061,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____7046]  in
                                                  uu____7005 :: uu____7029
                                                   in
                                                uu____6970 :: uu____6990  in
                                              uu____6935 :: uu____6955  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6920
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6905
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a430  ->
                                                (Obj.magic arg_as_string)
                                                  a430)
                                             (fun a431  ->
                                                fun a432  ->
                                                  fun a433  ->
                                                    (Obj.magic
                                                       string_compare') a431
                                                      a432 a433)))
                                          :: uu____6890
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a434  ->
                                              (Obj.magic arg_as_bool) a434)
                                           (fun a435  ->
                                              fun a436  ->
                                                (Obj.magic string_of_bool1)
                                                  a435 a436)))
                                        :: uu____6875
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a437  ->
                                            (Obj.magic arg_as_int) a437)
                                         (fun a438  ->
                                            fun a439  ->
                                              (Obj.magic string_of_int1) a438
                                                a439)))
                                      :: uu____6860
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a440  ->
                                          (Obj.magic arg_as_int) a440)
                                       (fun a441  ->
                                          (Obj.magic arg_as_char) a441)
                                       (fun a442  ->
                                          fun a443  ->
                                            (Obj.magic
                                               (FStar_Syntax_Embeddings.embed
                                                  FStar_Syntax_Embeddings.e_string))
                                              a442 a443)
                                       (fun a444  ->
                                          fun a445  ->
                                            fun a446  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____7252 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____7252 y)) a444
                                                a445 a446)))
                                    :: uu____6845
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6830
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6815
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6800
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6785
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6770
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6755
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a447  -> (Obj.magic arg_as_int) a447)
                         (fun a448  ->
                            fun a449  ->
                              fun a450  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7419 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____7419)) a448 a449 a450)))
                      :: uu____6740
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a451  -> (Obj.magic arg_as_int) a451)
                       (fun a452  ->
                          fun a453  ->
                            fun a454  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7445 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____7445)) a452 a453 a454)))
                    :: uu____6725
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a455  -> (Obj.magic arg_as_int) a455)
                     (fun a456  ->
                        fun a457  ->
                          fun a458  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7471 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____7471)) a456 a457 a458)))
                  :: uu____6710
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a459  -> (Obj.magic arg_as_int) a459)
                   (fun a460  ->
                      fun a461  ->
                        fun a462  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7497 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____7497)) a460 a461 a462)))
                :: uu____6695
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6680
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6665
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6650
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6635
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6620
     in
  let weak_ops =
    let uu____7636 =
      let uu____7655 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7655, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7636]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7739 =
        let uu____7740 =
          let uu____7741 = FStar_Syntax_Syntax.as_arg c  in [uu____7741]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7740  in
      uu____7739 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7791 =
                let uu____7804 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7804, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a463  -> (Obj.magic arg_as_bounded_int) a463)
                     (fun a464  ->
                        fun a465  ->
                          fun a466  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7820  ->
                                    fun uu____7821  ->
                                      match (uu____7820, uu____7821) with
                                      | ((int_to_t1,x),(uu____7840,y)) ->
                                          let uu____7850 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7850)) a464 a465 a466)))
                 in
              let uu____7851 =
                let uu____7866 =
                  let uu____7879 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7879, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a467  -> (Obj.magic arg_as_bounded_int) a467)
                       (fun a468  ->
                          fun a469  ->
                            fun a470  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7895  ->
                                      fun uu____7896  ->
                                        match (uu____7895, uu____7896) with
                                        | ((int_to_t1,x),(uu____7915,y)) ->
                                            let uu____7925 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7925)) a468 a469 a470)))
                   in
                let uu____7926 =
                  let uu____7941 =
                    let uu____7954 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7954, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a471  -> (Obj.magic arg_as_bounded_int) a471)
                         (fun a472  ->
                            fun a473  ->
                              fun a474  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7970  ->
                                        fun uu____7971  ->
                                          match (uu____7970, uu____7971) with
                                          | ((int_to_t1,x),(uu____7990,y)) ->
                                              let uu____8000 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____8000)) a472 a473 a474)))
                     in
                  let uu____8001 =
                    let uu____8016 =
                      let uu____8029 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____8029, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a475  -> (Obj.magic arg_as_bounded_int) a475)
                           (fun a476  ->
                              fun a477  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8041  ->
                                        match uu____8041 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a476 a477)))
                       in
                    [uu____8016]  in
                  uu____7941 :: uu____8001  in
                uu____7866 :: uu____7926  in
              uu____7791 :: uu____7851))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____8155 =
                let uu____8168 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____8168, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a478  -> (Obj.magic arg_as_bounded_int) a478)
                     (fun a479  ->
                        fun a480  ->
                          fun a481  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8184  ->
                                    fun uu____8185  ->
                                      match (uu____8184, uu____8185) with
                                      | ((int_to_t1,x),(uu____8204,y)) ->
                                          let uu____8214 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8214)) a479 a480 a481)))
                 in
              let uu____8215 =
                let uu____8230 =
                  let uu____8243 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____8243, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                       (fun a483  ->
                          fun a484  ->
                            fun a485  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8259  ->
                                      fun uu____8260  ->
                                        match (uu____8259, uu____8260) with
                                        | ((int_to_t1,x),(uu____8279,y)) ->
                                            let uu____8289 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8289)) a483 a484 a485)))
                   in
                [uu____8230]  in
              uu____8155 :: uu____8215))
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
    | (_typ,uu____8401)::(a1,uu____8403)::(a2,uu____8405)::[] ->
        let uu____8442 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8442 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8448 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8448.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8448.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8452 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8452.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8452.FStar_Syntax_Syntax.vars)
                })
         | uu____8453 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8455)::uu____8456::(a1,uu____8458)::(a2,uu____8460)::[] ->
        let uu____8509 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8509 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8515 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8515.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8515.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8519 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8519.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8519.FStar_Syntax_Syntax.vars)
                })
         | uu____8520 -> FStar_Pervasives_Native.None)
    | uu____8521 -> failwith "Unexpected number of arguments"  in
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
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8573 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8573 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8618 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8618) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8678  ->
           fun subst1  ->
             match uu____8678 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8719,uu____8720)) ->
                      let uu____8779 = b  in
                      (match uu____8779 with
                       | (bv,uu____8787) ->
                           let uu____8788 =
                             let uu____8789 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8789  in
                           if uu____8788
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8794 = unembed_binder term1  in
                              match uu____8794 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8801 =
                                      let uu___141_8802 = bv  in
                                      let uu____8803 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___141_8802.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___141_8802.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8803
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8801
                                     in
                                  let b_for_x =
                                    let uu____8807 =
                                      let uu____8814 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8814)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8807  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_8824  ->
                                         match uu___85_8824 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8825,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8827;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8828;_})
                                             ->
                                             let uu____8833 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____8833
                                         | uu____8834 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8835 -> subst1)) env []
  
let reduce_primops :
  'Auu____8852 'Auu____8853 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8852) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8853 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8895 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8895 with
             | (head1,args) ->
                 let uu____8932 =
                   let uu____8933 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8933.FStar_Syntax_Syntax.n  in
                 (match uu____8932 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8937 = find_prim_step cfg fv  in
                      (match uu____8937 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8959  ->
                                   let uu____8960 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8961 =
                                     FStar_Util.string_of_int l  in
                                   let uu____8968 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8960 uu____8961 uu____8968);
                              tm)
                           else
                             (let uu____8970 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____8970 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____9081  ->
                                        let uu____9082 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____9082);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____9085  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____9087 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____9087 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____9093  ->
                                              let uu____9094 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____9094);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____9100  ->
                                              let uu____9101 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____9102 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____9101 uu____9102);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____9103 ->
                           (log_primops cfg
                              (fun uu____9107  ->
                                 let uu____9108 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____9108);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9112  ->
                            let uu____9113 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9113);
                       (match args with
                        | (a1,uu____9115)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____9132 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9144  ->
                            let uu____9145 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9145);
                       (match args with
                        | (t,uu____9147)::(r,uu____9149)::[] ->
                            let uu____9176 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____9176 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___142_9180 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___142_9180.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___142_9180.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____9183 -> tm))
                  | uu____9192 -> tm))
  
let reduce_equality :
  'Auu____9197 'Auu____9198 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9197) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9198 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___143_9236 = cfg  in
         {
           steps =
             (let uu___144_9239 = default_steps  in
              {
                beta = (uu___144_9239.beta);
                iota = (uu___144_9239.iota);
                zeta = (uu___144_9239.zeta);
                weak = (uu___144_9239.weak);
                hnf = (uu___144_9239.hnf);
                primops = true;
                no_delta_steps = (uu___144_9239.no_delta_steps);
                unfold_until = (uu___144_9239.unfold_until);
                unfold_only = (uu___144_9239.unfold_only);
                unfold_fully = (uu___144_9239.unfold_fully);
                unfold_attr = (uu___144_9239.unfold_attr);
                unfold_tac = (uu___144_9239.unfold_tac);
                pure_subterms_within_computations =
                  (uu___144_9239.pure_subterms_within_computations);
                simplify = (uu___144_9239.simplify);
                erase_universes = (uu___144_9239.erase_universes);
                allow_unbound_universes =
                  (uu___144_9239.allow_unbound_universes);
                reify_ = (uu___144_9239.reify_);
                compress_uvars = (uu___144_9239.compress_uvars);
                no_full_norm = (uu___144_9239.no_full_norm);
                check_no_uvars = (uu___144_9239.check_no_uvars);
                unmeta = (uu___144_9239.unmeta);
                unascribe = (uu___144_9239.unascribe)
              });
           tcenv = (uu___143_9236.tcenv);
           debug = (uu___143_9236.debug);
           delta_level = (uu___143_9236.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___143_9236.strong);
           memoize_lazy = (uu___143_9236.memoize_lazy);
           normalize_pure_lets = (uu___143_9236.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____9243 .
    FStar_Syntax_Syntax.term -> 'Auu____9243 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9256 =
        let uu____9263 =
          let uu____9264 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9264.FStar_Syntax_Syntax.n  in
        (uu____9263, args)  in
      match uu____9256 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9270::uu____9271::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9275::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____9280::uu____9281::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9284 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_9295  ->
    match uu___86_9295 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9301 =
          let uu____9304 =
            let uu____9305 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____9305  in
          [uu____9304]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9301
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____9311 =
          let uu____9314 =
            let uu____9315 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldFully uu____9315  in
          [uu____9314]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9311
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____9331 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____9331) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____9373 =
          let uu____9378 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____9378 s  in
        match uu____9373 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____9394 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____9394
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____9411::(tm,uu____9413)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____9442)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____9463)::uu____9464::(tm,uu____9466)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9503 =
            let uu____9508 = full_norm steps  in parse_steps uu____9508  in
          (match uu____9503 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9547 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_9564  ->
    match uu___87_9564 with
    | (App
        (uu____9567,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9568;
                      FStar_Syntax_Syntax.vars = uu____9569;_},uu____9570,uu____9571))::uu____9572
        -> true
    | uu____9579 -> false
  
let firstn :
  'Auu____9585 .
    Prims.int ->
      'Auu____9585 Prims.list ->
        ('Auu____9585 Prims.list,'Auu____9585 Prims.list)
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
          (uu____9621,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9622;
                        FStar_Syntax_Syntax.vars = uu____9623;_},uu____9624,uu____9625))::uu____9626
          -> (cfg.steps).reify_
      | uu____9633 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9817 ->
                   let uu____9842 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9842
               | uu____9843 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____9851  ->
               let uu____9852 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9853 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9854 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9861 =
                 let uu____9862 =
                   let uu____9865 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9865
                    in
                 stack_to_string uu____9862  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9852 uu____9853 uu____9854 uu____9861);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9888 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9889 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9890 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9891;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____9892;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9895;
                 FStar_Syntax_Syntax.fv_delta = uu____9896;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9897;
                 FStar_Syntax_Syntax.fv_delta = uu____9898;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9899);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____9906 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____9942 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____9942)
               ->
               let cfg' =
                 let uu___145_9944 = cfg  in
                 {
                   steps =
                     (let uu___146_9947 = cfg.steps  in
                      {
                        beta = (uu___146_9947.beta);
                        iota = (uu___146_9947.iota);
                        zeta = (uu___146_9947.zeta);
                        weak = (uu___146_9947.weak);
                        hnf = (uu___146_9947.hnf);
                        primops = (uu___146_9947.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___146_9947.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___146_9947.unfold_attr);
                        unfold_tac = (uu___146_9947.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___146_9947.pure_subterms_within_computations);
                        simplify = (uu___146_9947.simplify);
                        erase_universes = (uu___146_9947.erase_universes);
                        allow_unbound_universes =
                          (uu___146_9947.allow_unbound_universes);
                        reify_ = (uu___146_9947.reify_);
                        compress_uvars = (uu___146_9947.compress_uvars);
                        no_full_norm = (uu___146_9947.no_full_norm);
                        check_no_uvars = (uu___146_9947.check_no_uvars);
                        unmeta = (uu___146_9947.unmeta);
                        unascribe = (uu___146_9947.unascribe)
                      });
                   tcenv = (uu___145_9944.tcenv);
                   debug = (uu___145_9944.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___145_9944.primitive_steps);
                   strong = (uu___145_9944.strong);
                   memoize_lazy = (uu___145_9944.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____9952 = get_norm_request (norm cfg' env []) args  in
               (match uu____9952 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____9983  ->
                              fun stack1  ->
                                match uu____9983 with
                                | (a,aq) ->
                                    let uu____9995 =
                                      let uu____9996 =
                                        let uu____10003 =
                                          let uu____10004 =
                                            let uu____10035 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____10035, false)  in
                                          Clos uu____10004  in
                                        (uu____10003, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____9996  in
                                    uu____9995 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____10119  ->
                          let uu____10120 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10120);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____10142 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_10147  ->
                                match uu___88_10147 with
                                | UnfoldUntil uu____10148 -> true
                                | UnfoldOnly uu____10149 -> true
                                | UnfoldFully uu____10152 -> true
                                | uu____10155 -> false))
                         in
                      if uu____10142
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___147_10160 = cfg  in
                      let uu____10161 = to_fsteps s  in
                      {
                        steps = uu____10161;
                        tcenv = (uu___147_10160.tcenv);
                        debug = (uu___147_10160.debug);
                        delta_level;
                        primitive_steps = (uu___147_10160.primitive_steps);
                        strong = (uu___147_10160.strong);
                        memoize_lazy = (uu___147_10160.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____10170 =
                          let uu____10171 =
                            let uu____10176 = FStar_Util.now ()  in
                            (t1, uu____10176)  in
                          Debug uu____10171  in
                        uu____10170 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10180 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10180
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10189 =
                      let uu____10196 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10196, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10189  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____10206 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____10206  in
               let uu____10207 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____10207
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____10213  ->
                       let uu____10214 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10215 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____10214 uu____10215);
                  if b
                  then
                    (let uu____10216 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____10216 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____10224 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____10224) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_10230  ->
                               match uu___89_10230 with
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
                          (let uu____10240 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____10240))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____10259) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____10294,uu____10295) -> false)))
                     in
                  let uu____10312 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____10328 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____10328 then (true, true) else (false, false)
                     in
                  match uu____10312 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____10341  ->
                            let uu____10342 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____10343 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____10344 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____10342 uu____10343 uu____10344);
                       if should_delta2
                       then
                         (let uu____10345 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___148_10361 = cfg  in
                                 {
                                   steps =
                                     (let uu___149_10364 = cfg.steps  in
                                      {
                                        beta = (uu___149_10364.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        no_delta_steps =
                                          (uu___149_10364.no_delta_steps);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___149_10364.unfold_attr);
                                        unfold_tac =
                                          (uu___149_10364.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___149_10364.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___149_10364.erase_universes);
                                        allow_unbound_universes =
                                          (uu___149_10364.allow_unbound_universes);
                                        reify_ = (uu___149_10364.reify_);
                                        compress_uvars =
                                          (uu___149_10364.compress_uvars);
                                        no_full_norm =
                                          (uu___149_10364.no_full_norm);
                                        check_no_uvars =
                                          (uu___149_10364.check_no_uvars);
                                        unmeta = (uu___149_10364.unmeta);
                                        unascribe =
                                          (uu___149_10364.unascribe)
                                      });
                                   tcenv = (uu___148_10361.tcenv);
                                   debug = (uu___148_10361.debug);
                                   delta_level = (uu___148_10361.delta_level);
                                   primitive_steps =
                                     (uu___148_10361.primitive_steps);
                                   strong = (uu___148_10361.strong);
                                   memoize_lazy =
                                     (uu___148_10361.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___148_10361.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____10345 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10378 = lookup_bvar env x  in
               (match uu____10378 with
                | Univ uu____10381 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10430 = FStar_ST.op_Bang r  in
                      (match uu____10430 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10548  ->
                                 let uu____10549 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10550 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10549
                                   uu____10550);
                            (let uu____10551 =
                               let uu____10552 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____10552.FStar_Syntax_Syntax.n  in
                             match uu____10551 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10555 ->
                                 norm cfg env2 stack t'
                             | uu____10572 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10642)::uu____10643 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10652)::uu____10653 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10663,uu____10664))::stack_rest ->
                    (match c with
                     | Univ uu____10668 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10677 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10698  ->
                                    let uu____10699 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10699);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10739  ->
                                    let uu____10740 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10740);
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
                       (fun uu____10818  ->
                          let uu____10819 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10819);
                     norm cfg env stack1 t1)
                | (Debug uu____10820)::uu____10821 ->
                    if (cfg.steps).weak
                    then
                      let uu____10828 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10828
                    else
                      (let uu____10830 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10830 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10872  -> dummy :: env1) env)
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
                                          let uu____10909 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10909)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10914 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10914.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10914.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10915 -> lopt  in
                           (log cfg
                              (fun uu____10921  ->
                                 let uu____10922 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10922);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10931 = cfg  in
                               {
                                 steps = (uu___151_10931.steps);
                                 tcenv = (uu___151_10931.tcenv);
                                 debug = (uu___151_10931.debug);
                                 delta_level = (uu___151_10931.delta_level);
                                 primitive_steps =
                                   (uu___151_10931.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10931.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10931.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10942)::uu____10943 ->
                    if (cfg.steps).weak
                    then
                      let uu____10950 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10950
                    else
                      (let uu____10952 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10952 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10994  -> dummy :: env1) env)
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
                                          let uu____11031 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11031)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11036 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11036.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11036.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11037 -> lopt  in
                           (log cfg
                              (fun uu____11043  ->
                                 let uu____11044 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11044);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11053 = cfg  in
                               {
                                 steps = (uu___151_11053.steps);
                                 tcenv = (uu___151_11053.tcenv);
                                 debug = (uu___151_11053.debug);
                                 delta_level = (uu___151_11053.delta_level);
                                 primitive_steps =
                                   (uu___151_11053.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11053.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11053.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11064)::uu____11065 ->
                    if (cfg.steps).weak
                    then
                      let uu____11076 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11076
                    else
                      (let uu____11078 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11078 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11120  -> dummy :: env1) env)
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
                                          let uu____11157 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11157)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11162 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11162.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11162.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11163 -> lopt  in
                           (log cfg
                              (fun uu____11169  ->
                                 let uu____11170 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11170);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11179 = cfg  in
                               {
                                 steps = (uu___151_11179.steps);
                                 tcenv = (uu___151_11179.tcenv);
                                 debug = (uu___151_11179.debug);
                                 delta_level = (uu___151_11179.delta_level);
                                 primitive_steps =
                                   (uu___151_11179.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11179.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11179.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11190)::uu____11191 ->
                    if (cfg.steps).weak
                    then
                      let uu____11202 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11202
                    else
                      (let uu____11204 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11204 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11246  -> dummy :: env1) env)
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
                                          let uu____11283 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11283)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11288 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11288.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11288.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11289 -> lopt  in
                           (log cfg
                              (fun uu____11295  ->
                                 let uu____11296 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11296);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11305 = cfg  in
                               {
                                 steps = (uu___151_11305.steps);
                                 tcenv = (uu___151_11305.tcenv);
                                 debug = (uu___151_11305.debug);
                                 delta_level = (uu___151_11305.delta_level);
                                 primitive_steps =
                                   (uu___151_11305.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11305.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11305.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11316)::uu____11317 ->
                    if (cfg.steps).weak
                    then
                      let uu____11332 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11332
                    else
                      (let uu____11334 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11334 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11376  -> dummy :: env1) env)
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
                                          let uu____11413 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11413)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11418 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11418.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11418.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11419 -> lopt  in
                           (log cfg
                              (fun uu____11425  ->
                                 let uu____11426 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11426);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11435 = cfg  in
                               {
                                 steps = (uu___151_11435.steps);
                                 tcenv = (uu___151_11435.tcenv);
                                 debug = (uu___151_11435.debug);
                                 delta_level = (uu___151_11435.delta_level);
                                 primitive_steps =
                                   (uu___151_11435.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11435.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11435.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (AscribedBy uu____11446)::uu____11447 ->
                    if (cfg.steps).weak
                    then
                      let uu____11460 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11460
                    else
                      (let uu____11462 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11462 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11504  -> dummy :: env1) env)
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
                                          let uu____11541 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11541)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11546 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11546.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11546.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11547 -> lopt  in
                           (log cfg
                              (fun uu____11553  ->
                                 let uu____11554 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11554);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11563 = cfg  in
                               {
                                 steps = (uu___151_11563.steps);
                                 tcenv = (uu___151_11563.tcenv);
                                 debug = (uu___151_11563.debug);
                                 delta_level = (uu___151_11563.delta_level);
                                 primitive_steps =
                                   (uu___151_11563.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11563.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11563.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (RefinedBy uu____11574)::uu____11575 ->
                    if (cfg.steps).weak
                    then
                      let uu____11586 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11586
                    else
                      (let uu____11588 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11588 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11630  -> dummy :: env1) env)
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
                                          let uu____11667 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11667)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11672 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11672.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11672.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11673 -> lopt  in
                           (log cfg
                              (fun uu____11679  ->
                                 let uu____11680 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11680);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11689 = cfg  in
                               {
                                 steps = (uu___151_11689.steps);
                                 tcenv = (uu___151_11689.tcenv);
                                 debug = (uu___151_11689.debug);
                                 delta_level = (uu___151_11689.delta_level);
                                 primitive_steps =
                                   (uu___151_11689.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11689.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11689.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Refining uu____11700)::uu____11701 ->
                    if (cfg.steps).weak
                    then
                      let uu____11710 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11710
                    else
                      (let uu____11712 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11712 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11754  -> dummy :: env1) env)
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
                                          let uu____11791 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11791)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11796 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11796.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11796.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11797 -> lopt  in
                           (log cfg
                              (fun uu____11803  ->
                                 let uu____11804 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11804);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11813 = cfg  in
                               {
                                 steps = (uu___151_11813.steps);
                                 tcenv = (uu___151_11813.tcenv);
                                 debug = (uu___151_11813.debug);
                                 delta_level = (uu___151_11813.delta_level);
                                 primitive_steps =
                                   (uu___151_11813.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11813.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11813.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____11824 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11824
                    else
                      (let uu____11826 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11826 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11868  -> dummy :: env1) env)
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
                                          let uu____11905 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11905)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11910 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11910.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11910.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11911 -> lopt  in
                           (log cfg
                              (fun uu____11917  ->
                                 let uu____11918 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11918);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11927 = cfg  in
                               {
                                 steps = (uu___151_11927.steps);
                                 tcenv = (uu___151_11927.tcenv);
                                 debug = (uu___151_11927.debug);
                                 delta_level = (uu___151_11927.delta_level);
                                 primitive_steps =
                                   (uu___151_11927.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11927.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11927.normalize_pure_lets)
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
                      (fun uu____11976  ->
                         fun stack1  ->
                           match uu____11976 with
                           | (a,aq) ->
                               let uu____11988 =
                                 let uu____11989 =
                                   let uu____11996 =
                                     let uu____11997 =
                                       let uu____12028 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12028, false)  in
                                     Clos uu____11997  in
                                   (uu____11996, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11989  in
                               uu____11988 :: stack1) args)
                  in
               (log cfg
                  (fun uu____12112  ->
                     let uu____12113 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12113);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               let uu____12126 = FStar_Syntax_Subst.open_term_bv x f  in
               (match uu____12126 with
                | (x1,f1) ->
                    norm cfg env
                      ((RefinedBy
                          (x1, (dummy :: env), f1,
                            (t1.FStar_Syntax_Syntax.pos))) :: stack)
                      x1.FStar_Syntax_Syntax.sort)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____12165 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12165
               else
                 (let uu____12167 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12167 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12175 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12199  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12175 c1  in
                      let t2 =
                        let uu____12221 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12221 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,l) ->
               (match stack with
                | (Match uu____12323)::uu____12324 ->
                    (log cfg
                       (fun uu____12335  ->
                          FStar_Util.print_string "+++ Dropping ascription\n");
                     norm cfg env stack t11)
                | (Arg uu____12336)::uu____12337 ->
                    (log cfg
                       (fun uu____12348  ->
                          FStar_Util.print_string "+++ Dropping ascription\n");
                     norm cfg env stack t11)
                | (App
                    (uu____12349,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12350;
                                   FStar_Syntax_Syntax.vars = uu____12351;_},uu____12352,uu____12353))::uu____12354
                    ->
                    (log cfg
                       (fun uu____12363  ->
                          FStar_Util.print_string "+++ Dropping ascription\n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12364)::uu____12365 ->
                    (log cfg
                       (fun uu____12376  ->
                          FStar_Util.print_string "+++ Dropping ascription\n");
                     norm cfg env stack t11)
                | uu____12377 ->
                    (log cfg
                       (fun uu____12380  ->
                          FStar_Util.print_string "+++ Keeping ascription\n");
                     norm cfg env
                       ((AscribedBy
                           (env, asc, l, (t1.FStar_Syntax_Syntax.pos))) ::
                       stack) t11))
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
                         let uu____12490 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12490 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___152_12510 = cfg  in
                               let uu____12511 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___152_12510.steps);
                                 tcenv = uu____12511;
                                 debug = (uu___152_12510.debug);
                                 delta_level = (uu___152_12510.delta_level);
                                 primitive_steps =
                                   (uu___152_12510.primitive_steps);
                                 strong = (uu___152_12510.strong);
                                 memoize_lazy = (uu___152_12510.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_12510.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____12516 =
                                 let uu____12517 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12517  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12516
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___153_12520 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___153_12520.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___153_12520.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___153_12520.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___153_12520.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12521 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12521
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12532,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12533;
                               FStar_Syntax_Syntax.lbunivs = uu____12534;
                               FStar_Syntax_Syntax.lbtyp = uu____12535;
                               FStar_Syntax_Syntax.lbeff = uu____12536;
                               FStar_Syntax_Syntax.lbdef = uu____12537;
                               FStar_Syntax_Syntax.lbattrs = uu____12538;
                               FStar_Syntax_Syntax.lbpos = uu____12539;_}::uu____12540),uu____12541)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12581 =
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
               if uu____12581
               then
                 let binder =
                   let uu____12583 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12583  in
                 let env1 =
                   let uu____12593 =
                     let uu____12600 =
                       let uu____12601 =
                         let uu____12632 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12632,
                           false)
                          in
                       Clos uu____12601  in
                     ((FStar_Pervasives_Native.Some binder), uu____12600)  in
                   uu____12593 :: env  in
                 (log cfg
                    (fun uu____12725  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12729  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12730 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12730))
                 else
                   (let uu____12732 =
                      let uu____12737 =
                        let uu____12738 =
                          let uu____12739 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12739
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12738]  in
                      FStar_Syntax_Subst.open_term uu____12737 body  in
                    match uu____12732 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____12748  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12756 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12756  in
                            FStar_Util.Inl
                              (let uu___154_12766 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___154_12766.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___154_12766.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12769  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___155_12771 = lb  in
                             let uu____12772 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___155_12771.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_12771.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12772;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___155_12771.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___155_12771.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12807  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___156_12830 = cfg  in
                             {
                               steps = (uu___156_12830.steps);
                               tcenv = (uu___156_12830.tcenv);
                               debug = (uu___156_12830.debug);
                               delta_level = (uu___156_12830.delta_level);
                               primitive_steps =
                                 (uu___156_12830.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___156_12830.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_12830.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____12833  ->
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
               let uu____12850 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12850 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12886 =
                               let uu___157_12887 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_12887.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_12887.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12886  in
                           let uu____12888 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12888 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12914 =
                                   FStar_List.map (fun uu____12930  -> dummy)
                                     lbs1
                                    in
                                 let uu____12931 =
                                   let uu____12940 =
                                     FStar_List.map
                                       (fun uu____12960  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12940 env  in
                                 FStar_List.append uu____12914 uu____12931
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12984 =
                                       let uu___158_12985 = rc  in
                                       let uu____12986 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___158_12985.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12986;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___158_12985.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12984
                                 | uu____12993 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___159_12997 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___159_12997.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___159_12997.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___159_12997.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___159_12997.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13007 =
                        FStar_List.map (fun uu____13023  -> dummy) lbs2  in
                      FStar_List.append uu____13007 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13031 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13031 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___160_13047 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___160_13047.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___160_13047.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____13074 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13074
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13093 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13169  ->
                        match uu____13169 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___161_13290 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___161_13290.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___161_13290.FStar_Syntax_Syntax.sort)
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
               (match uu____13093 with
                | (rec_env,memos,uu____13503) ->
                    let uu____13556 =
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
                             let uu____13867 =
                               let uu____13874 =
                                 let uu____13875 =
                                   let uu____13906 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13906, false)
                                    in
                                 Clos uu____13875  in
                               (FStar_Pervasives_Native.None, uu____13874)
                                in
                             uu____13867 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14016  ->
                     let uu____14017 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14017);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14039 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14041::uu____14042 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14047) ->
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
                             | uu____14070 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14084 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14084
                              | uu____14095 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14099 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14125 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14143 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____14160 =
                        let uu____14161 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14162 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14161 uu____14162
                         in
                      failwith uu____14160
                    else rebuild cfg env stack t2
                | uu____14164 -> norm cfg env stack t2))

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
                let uu____14174 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____14174  in
              let uu____14175 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14175 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____14188  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____14199  ->
                        let uu____14200 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14201 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____14200 uu____14201);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____14206 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____14206 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____14215))::stack1 ->
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
                      | uu____14270 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14273 ->
                          let uu____14276 =
                            let uu____14277 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14277
                             in
                          failwith uu____14276
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
                  let uu___162_14301 = cfg  in
                  let uu____14302 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____14302;
                    tcenv = (uu___162_14301.tcenv);
                    debug = (uu___162_14301.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___162_14301.primitive_steps);
                    strong = (uu___162_14301.strong);
                    memoize_lazy = (uu___162_14301.memoize_lazy);
                    normalize_pure_lets =
                      (uu___162_14301.normalize_pure_lets)
                  }
                else
                  (let uu___163_14304 = cfg  in
                   {
                     steps =
                       (let uu___164_14307 = cfg.steps  in
                        {
                          beta = (uu___164_14307.beta);
                          iota = (uu___164_14307.iota);
                          zeta = false;
                          weak = (uu___164_14307.weak);
                          hnf = (uu___164_14307.hnf);
                          primops = (uu___164_14307.primops);
                          no_delta_steps = (uu___164_14307.no_delta_steps);
                          unfold_until = (uu___164_14307.unfold_until);
                          unfold_only = (uu___164_14307.unfold_only);
                          unfold_fully = (uu___164_14307.unfold_fully);
                          unfold_attr = (uu___164_14307.unfold_attr);
                          unfold_tac = (uu___164_14307.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___164_14307.pure_subterms_within_computations);
                          simplify = (uu___164_14307.simplify);
                          erase_universes = (uu___164_14307.erase_universes);
                          allow_unbound_universes =
                            (uu___164_14307.allow_unbound_universes);
                          reify_ = (uu___164_14307.reify_);
                          compress_uvars = (uu___164_14307.compress_uvars);
                          no_full_norm = (uu___164_14307.no_full_norm);
                          check_no_uvars = (uu___164_14307.check_no_uvars);
                          unmeta = (uu___164_14307.unmeta);
                          unascribe = (uu___164_14307.unascribe)
                        });
                     tcenv = (uu___163_14304.tcenv);
                     debug = (uu___163_14304.debug);
                     delta_level = (uu___163_14304.delta_level);
                     primitive_steps = (uu___163_14304.primitive_steps);
                     strong = (uu___163_14304.strong);
                     memoize_lazy = (uu___163_14304.memoize_lazy);
                     normalize_pure_lets =
                       (uu___163_14304.normalize_pure_lets)
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
                  (fun uu____14337  ->
                     let uu____14338 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____14339 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14338
                       uu____14339);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____14341 =
                   let uu____14342 = FStar_Syntax_Subst.compress head3  in
                   uu____14342.FStar_Syntax_Syntax.n  in
                 match uu____14341 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____14360 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14360
                        in
                     let uu____14361 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14361 with
                      | (uu____14362,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____14368 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____14376 =
                                   let uu____14377 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____14377.FStar_Syntax_Syntax.n  in
                                 match uu____14376 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____14383,uu____14384))
                                     ->
                                     let uu____14393 =
                                       let uu____14394 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____14394.FStar_Syntax_Syntax.n  in
                                     (match uu____14393 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____14400,msrc,uu____14402))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____14411 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14411
                                      | uu____14412 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____14413 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____14414 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____14414 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___165_14419 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___165_14419.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___165_14419.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___165_14419.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___165_14419.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___165_14419.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____14420 = FStar_List.tl stack  in
                                    let uu____14421 =
                                      let uu____14422 =
                                        let uu____14425 =
                                          let uu____14426 =
                                            let uu____14439 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____14439)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14426
                                           in
                                        FStar_Syntax_Syntax.mk uu____14425
                                         in
                                      uu____14422
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____14420 uu____14421
                                | FStar_Pervasives_Native.None  ->
                                    let uu____14455 =
                                      let uu____14456 = is_return body  in
                                      match uu____14456 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14460;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14461;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14466 -> false  in
                                    if uu____14455
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
                                         let uu____14489 =
                                           let uu____14492 =
                                             let uu____14493 =
                                               let uu____14510 =
                                                 let uu____14513 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____14513]  in
                                               (uu____14510, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14493
                                              in
                                           FStar_Syntax_Syntax.mk uu____14492
                                            in
                                         uu____14489
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____14529 =
                                           let uu____14530 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____14530.FStar_Syntax_Syntax.n
                                            in
                                         match uu____14529 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____14536::uu____14537::[])
                                             ->
                                             let uu____14544 =
                                               let uu____14547 =
                                                 let uu____14548 =
                                                   let uu____14555 =
                                                     let uu____14558 =
                                                       let uu____14559 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14559
                                                        in
                                                     let uu____14560 =
                                                       let uu____14563 =
                                                         let uu____14564 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14564
                                                          in
                                                       [uu____14563]  in
                                                     uu____14558 ::
                                                       uu____14560
                                                      in
                                                   (bind1, uu____14555)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14548
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14547
                                                in
                                             uu____14544
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____14572 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____14578 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____14578
                                         then
                                           let uu____14581 =
                                             let uu____14582 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14582
                                              in
                                           let uu____14583 =
                                             let uu____14586 =
                                               let uu____14587 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____14587
                                                in
                                             [uu____14586]  in
                                           uu____14581 :: uu____14583
                                         else []  in
                                       let reified =
                                         let uu____14592 =
                                           let uu____14595 =
                                             let uu____14596 =
                                               let uu____14611 =
                                                 let uu____14614 =
                                                   let uu____14617 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____14618 =
                                                     let uu____14621 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____14621]  in
                                                   uu____14617 :: uu____14618
                                                    in
                                                 let uu____14622 =
                                                   let uu____14625 =
                                                     let uu____14628 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____14629 =
                                                       let uu____14632 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____14633 =
                                                         let uu____14636 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____14637 =
                                                           let uu____14640 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____14640]  in
                                                         uu____14636 ::
                                                           uu____14637
                                                          in
                                                       uu____14632 ::
                                                         uu____14633
                                                        in
                                                     uu____14628 ::
                                                       uu____14629
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____14625
                                                    in
                                                 FStar_List.append
                                                   uu____14614 uu____14622
                                                  in
                                               (bind_inst, uu____14611)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14596
                                              in
                                           FStar_Syntax_Syntax.mk uu____14595
                                            in
                                         uu____14592
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____14652  ->
                                            let uu____14653 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____14654 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____14653 uu____14654);
                                       (let uu____14655 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____14655 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____14679 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14679
                        in
                     let uu____14680 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14680 with
                      | (uu____14681,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____14716 =
                                  let uu____14717 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____14717.FStar_Syntax_Syntax.n  in
                                match uu____14716 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____14723) -> t2
                                | uu____14728 -> head4  in
                              let uu____14729 =
                                let uu____14730 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____14730.FStar_Syntax_Syntax.n  in
                              match uu____14729 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____14736 -> FStar_Pervasives_Native.None
                               in
                            let uu____14737 = maybe_extract_fv head4  in
                            match uu____14737 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____14747 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____14747
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____14752 = maybe_extract_fv head5
                                     in
                                  match uu____14752 with
                                  | FStar_Pervasives_Native.Some uu____14757
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14758 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____14763 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____14778 =
                              match uu____14778 with
                              | (e,q) ->
                                  let uu____14785 =
                                    let uu____14786 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14786.FStar_Syntax_Syntax.n  in
                                  (match uu____14785 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____14801 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____14801
                                   | uu____14802 -> false)
                               in
                            let uu____14803 =
                              let uu____14804 =
                                let uu____14811 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____14811 :: args  in
                              FStar_Util.for_some is_arg_impure uu____14804
                               in
                            if uu____14803
                            then
                              let uu____14816 =
                                let uu____14817 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14817
                                 in
                              failwith uu____14816
                            else ());
                           (let uu____14819 = maybe_unfold_action head_app
                               in
                            match uu____14819 with
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
                                   (fun uu____14860  ->
                                      let uu____14861 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____14862 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14861 uu____14862);
                                 (let uu____14863 = FStar_List.tl stack  in
                                  norm cfg env uu____14863 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____14865) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____14889 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____14889  in
                     (log cfg
                        (fun uu____14893  ->
                           let uu____14894 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14894);
                      (let uu____14895 = FStar_List.tl stack  in
                       norm cfg env uu____14895 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15016  ->
                               match uu____15016 with
                               | (pat,wopt,tm) ->
                                   let uu____15064 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____15064)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____15096 = FStar_List.tl stack  in
                     norm cfg env uu____15096 tm
                 | uu____15097 -> fallback ())

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
              (fun uu____15111  ->
                 let uu____15112 = FStar_Ident.string_of_lid msrc  in
                 let uu____15113 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15114 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15112
                   uu____15113 uu____15114);
            (let uu____15115 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15115
             then
               let ed =
                 let uu____15117 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15117  in
               let uu____15118 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15118 with
               | (uu____15119,return_repr) ->
                   let return_inst =
                     let uu____15128 =
                       let uu____15129 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15129.FStar_Syntax_Syntax.n  in
                     match uu____15128 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15135::[]) ->
                         let uu____15142 =
                           let uu____15145 =
                             let uu____15146 =
                               let uu____15153 =
                                 let uu____15156 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15156]  in
                               (return_tm, uu____15153)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15146  in
                           FStar_Syntax_Syntax.mk uu____15145  in
                         uu____15142 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15164 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15167 =
                     let uu____15170 =
                       let uu____15171 =
                         let uu____15186 =
                           let uu____15189 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15190 =
                             let uu____15193 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15193]  in
                           uu____15189 :: uu____15190  in
                         (return_inst, uu____15186)  in
                       FStar_Syntax_Syntax.Tm_app uu____15171  in
                     FStar_Syntax_Syntax.mk uu____15170  in
                   uu____15167 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15202 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15202 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15205 =
                      let uu____15206 = FStar_Ident.text_of_lid msrc  in
                      let uu____15207 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15206 uu____15207
                       in
                    failwith uu____15205
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15208;
                      FStar_TypeChecker_Env.mtarget = uu____15209;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15210;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15225 =
                      let uu____15226 = FStar_Ident.text_of_lid msrc  in
                      let uu____15227 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15226 uu____15227
                       in
                    failwith uu____15225
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15228;
                      FStar_TypeChecker_Env.mtarget = uu____15229;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15230;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____15254 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____15255 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____15254 t FStar_Syntax_Syntax.tun uu____15255))

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
                (fun uu____15311  ->
                   match uu____15311 with
                   | (a,imp) ->
                       let uu____15322 = norm cfg env [] a  in
                       (uu____15322, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____15330  ->
             let uu____15331 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____15332 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____15331 uu____15332);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15356 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____15356
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___166_15359 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___166_15359.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___166_15359.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15379 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____15379
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___167_15382 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___167_15382.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___167_15382.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____15415  ->
                      match uu____15415 with
                      | (a,i) ->
                          let uu____15426 = norm cfg env [] a  in
                          (uu____15426, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_15444  ->
                       match uu___90_15444 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15448 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____15448
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___168_15456 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___169_15459 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___169_15459.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___168_15456.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___168_15456.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____15462  ->
        match uu____15462 with
        | (x,imp) ->
            let uu____15465 =
              let uu___170_15466 = x  in
              let uu____15467 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___170_15466.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___170_15466.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15467
              }  in
            (uu____15465, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15473 =
          FStar_List.fold_left
            (fun uu____15491  ->
               fun b  ->
                 match uu____15491 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____15473 with | (nbs,uu____15531) -> FStar_List.rev nbs

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
            let uu____15547 =
              let uu___171_15548 = rc  in
              let uu____15549 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___171_15548.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15549;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___171_15548.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15547
        | uu____15556 -> lopt

and (maybe_simplify :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____15577 = FStar_Syntax_Print.term_to_string tm  in
             let uu____15578 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____15577
               uu____15578)
          else ();
          tm'

and (maybe_simplify_aux :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____15598 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____15598
          then tm1
          else
            (let w t =
               let uu___172_15610 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___172_15610.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___172_15610.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____15619 =
                 let uu____15620 = FStar_Syntax_Util.unmeta t  in
                 uu____15620.FStar_Syntax_Syntax.n  in
               match uu____15619 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15627 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____15672)::args1,(bv,uu____15675)::bs1) ->
                   let uu____15709 =
                     let uu____15710 = FStar_Syntax_Subst.compress t  in
                     uu____15710.FStar_Syntax_Syntax.n  in
                   (match uu____15709 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15714 -> false)
               | ([],[]) -> true
               | (uu____15735,uu____15736) -> false  in
             let is_applied bs t =
               let uu____15772 = FStar_Syntax_Util.head_and_args' t  in
               match uu____15772 with
               | (hd1,args) ->
                   let uu____15805 =
                     let uu____15806 = FStar_Syntax_Subst.compress hd1  in
                     uu____15806.FStar_Syntax_Syntax.n  in
                   (match uu____15805 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15812 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____15824 = FStar_Syntax_Util.is_squash t  in
               match uu____15824 with
               | FStar_Pervasives_Native.Some (uu____15835,t') ->
                   is_applied bs t'
               | uu____15847 ->
                   let uu____15856 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____15856 with
                    | FStar_Pervasives_Native.Some (uu____15867,t') ->
                        is_applied bs t'
                    | uu____15879 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____15896 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15896 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15903)::(q,uu____15905)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15940 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____15940 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15945 =
                          let uu____15946 = FStar_Syntax_Subst.compress p  in
                          uu____15946.FStar_Syntax_Syntax.n  in
                        (match uu____15945 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15952 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____15952
                         | uu____15953 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____15956)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15981 =
                          let uu____15982 = FStar_Syntax_Subst.compress p1
                             in
                          uu____15982.FStar_Syntax_Syntax.n  in
                        (match uu____15981 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15988 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____15988
                         | uu____15989 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____15993 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____15993 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____15998 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____15998 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16005 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16005
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____16008)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____16033 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____16033 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16040 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16040
                              | uu____16041 -> FStar_Pervasives_Native.None)
                         | uu____16044 -> FStar_Pervasives_Native.None)
                    | uu____16047 -> FStar_Pervasives_Native.None)
               | uu____16050 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____16061 =
                 let uu____16062 = FStar_Syntax_Subst.compress phi  in
                 uu____16062.FStar_Syntax_Syntax.n  in
               match uu____16061 with
               | FStar_Syntax_Syntax.Tm_match (uu____16067,br::brs) ->
                   let uu____16134 = br  in
                   (match uu____16134 with
                    | (uu____16151,uu____16152,e) ->
                        let r =
                          let uu____16173 = simp_t e  in
                          match uu____16173 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16179 =
                                FStar_List.for_all
                                  (fun uu____16197  ->
                                     match uu____16197 with
                                     | (uu____16210,uu____16211,e') ->
                                         let uu____16225 = simp_t e'  in
                                         uu____16225 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____16179
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____16233 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____16238 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____16238
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____16259 =
                 match uu____16259 with
                 | (t1,q) ->
                     let uu____16272 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____16272 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____16300 -> (t1, q))
                  in
               let uu____16309 = FStar_Syntax_Util.head_and_args t  in
               match uu____16309 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____16371 =
                 let uu____16372 = FStar_Syntax_Util.unmeta ty  in
                 uu____16372.FStar_Syntax_Syntax.n  in
               match uu____16371 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____16376) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____16381,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____16401 -> false  in
             let simplify1 arg =
               let uu____16424 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____16424, arg)  in
             let uu____16433 = is_quantified_const tm1  in
             match uu____16433 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____16437 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____16437
             | FStar_Pervasives_Native.None  ->
                 let uu____16438 =
                   let uu____16439 = FStar_Syntax_Subst.compress tm1  in
                   uu____16439.FStar_Syntax_Syntax.n  in
                 (match uu____16438 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16443;
                              FStar_Syntax_Syntax.vars = uu____16444;_},uu____16445);
                         FStar_Syntax_Syntax.pos = uu____16446;
                         FStar_Syntax_Syntax.vars = uu____16447;_},args)
                      ->
                      let uu____16473 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16473
                      then
                        let uu____16474 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16474 with
                         | (FStar_Pervasives_Native.Some (true ),uu____16521)::
                             (uu____16522,(arg,uu____16524))::[] ->
                             maybe_auto_squash arg
                         | (uu____16573,(arg,uu____16575))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____16576)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16625)::uu____16626::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16677::(FStar_Pervasives_Native.Some (false
                                         ),uu____16678)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16729 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16743 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16743
                         then
                           let uu____16744 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16744 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16791)::uu____16792::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16843::(FStar_Pervasives_Native.Some (true
                                           ),uu____16844)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16895)::(uu____16896,(arg,uu____16898))::[]
                               -> maybe_auto_squash arg
                           | (uu____16947,(arg,uu____16949))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16950)::[]
                               -> maybe_auto_squash arg
                           | uu____16999 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17013 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____17013
                            then
                              let uu____17014 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____17014 with
                              | uu____17061::(FStar_Pervasives_Native.Some
                                              (true ),uu____17062)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____17113)::uu____17114::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____17165)::(uu____17166,(arg,uu____17168))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17217,(p,uu____17219))::(uu____17220,
                                                                (q,uu____17222))::[]
                                  ->
                                  let uu____17269 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____17269
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17271 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17285 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____17285
                               then
                                 let uu____17286 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____17286 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17333)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17334)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17385)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17386)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17437)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17438)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17489)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17490)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17541,(arg,uu____17543))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17544)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17593)::(uu____17594,(arg,uu____17596))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17645,(arg,uu____17647))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17648)::[]
                                     ->
                                     let uu____17697 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17697
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17698)::(uu____17699,(arg,uu____17701))::[]
                                     ->
                                     let uu____17750 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17750
                                 | (uu____17751,(p,uu____17753))::(uu____17754,
                                                                   (q,uu____17756))::[]
                                     ->
                                     let uu____17803 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17803
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17805 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17819 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17819
                                  then
                                    let uu____17820 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17820 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17867)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17898)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17929 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17943 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17943
                                     then
                                       match args with
                                       | (t,uu____17945)::[] ->
                                           let uu____17962 =
                                             let uu____17963 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17963.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17962 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17966::[],body,uu____17968)
                                                ->
                                                let uu____17995 = simp_t body
                                                   in
                                                (match uu____17995 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17998 -> tm1)
                                            | uu____18001 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18003))::(t,uu____18005)::[]
                                           ->
                                           let uu____18044 =
                                             let uu____18045 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18045.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18044 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18048::[],body,uu____18050)
                                                ->
                                                let uu____18077 = simp_t body
                                                   in
                                                (match uu____18077 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18080 -> tm1)
                                            | uu____18083 -> tm1)
                                       | uu____18084 -> tm1
                                     else
                                       (let uu____18094 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18094
                                        then
                                          match args with
                                          | (t,uu____18096)::[] ->
                                              let uu____18113 =
                                                let uu____18114 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18114.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18113 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18117::[],body,uu____18119)
                                                   ->
                                                   let uu____18146 =
                                                     simp_t body  in
                                                   (match uu____18146 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18149 -> tm1)
                                               | uu____18152 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18154))::(t,uu____18156)::[]
                                              ->
                                              let uu____18195 =
                                                let uu____18196 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18196.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18195 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18199::[],body,uu____18201)
                                                   ->
                                                   let uu____18228 =
                                                     simp_t body  in
                                                   (match uu____18228 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____18231 -> tm1)
                                               | uu____18234 -> tm1)
                                          | uu____18235 -> tm1
                                        else
                                          (let uu____18245 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18245
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18246;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18247;_},uu____18248)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18265;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18266;_},uu____18267)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18284 -> tm1
                                           else
                                             (let uu____18294 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18294 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18314 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18324;
                         FStar_Syntax_Syntax.vars = uu____18325;_},args)
                      ->
                      let uu____18347 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18347
                      then
                        let uu____18348 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18348 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18395)::
                             (uu____18396,(arg,uu____18398))::[] ->
                             maybe_auto_squash arg
                         | (uu____18447,(arg,uu____18449))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18450)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18499)::uu____18500::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18551::(FStar_Pervasives_Native.Some (false
                                         ),uu____18552)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18603 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18617 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18617
                         then
                           let uu____18618 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18618 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18665)::uu____18666::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18717::(FStar_Pervasives_Native.Some (true
                                           ),uu____18718)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18769)::(uu____18770,(arg,uu____18772))::[]
                               -> maybe_auto_squash arg
                           | (uu____18821,(arg,uu____18823))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18824)::[]
                               -> maybe_auto_squash arg
                           | uu____18873 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18887 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18887
                            then
                              let uu____18888 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18888 with
                              | uu____18935::(FStar_Pervasives_Native.Some
                                              (true ),uu____18936)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18987)::uu____18988::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19039)::(uu____19040,(arg,uu____19042))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19091,(p,uu____19093))::(uu____19094,
                                                                (q,uu____19096))::[]
                                  ->
                                  let uu____19143 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19143
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19145 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19159 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19159
                               then
                                 let uu____19160 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19160 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19207)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19208)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19259)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19260)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19311)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19312)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19363)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19364)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19415,(arg,uu____19417))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19418)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19467)::(uu____19468,(arg,uu____19470))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19519,(arg,uu____19521))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19522)::[]
                                     ->
                                     let uu____19571 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19571
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19572)::(uu____19573,(arg,uu____19575))::[]
                                     ->
                                     let uu____19624 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19624
                                 | (uu____19625,(p,uu____19627))::(uu____19628,
                                                                   (q,uu____19630))::[]
                                     ->
                                     let uu____19677 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19677
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19679 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19693 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19693
                                  then
                                    let uu____19694 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19694 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19741)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19772)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19803 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19817 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19817
                                     then
                                       match args with
                                       | (t,uu____19819)::[] ->
                                           let uu____19836 =
                                             let uu____19837 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19837.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19836 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19840::[],body,uu____19842)
                                                ->
                                                let uu____19869 = simp_t body
                                                   in
                                                (match uu____19869 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19872 -> tm1)
                                            | uu____19875 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19877))::(t,uu____19879)::[]
                                           ->
                                           let uu____19918 =
                                             let uu____19919 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19919.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19918 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19922::[],body,uu____19924)
                                                ->
                                                let uu____19951 = simp_t body
                                                   in
                                                (match uu____19951 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19954 -> tm1)
                                            | uu____19957 -> tm1)
                                       | uu____19958 -> tm1
                                     else
                                       (let uu____19968 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19968
                                        then
                                          match args with
                                          | (t,uu____19970)::[] ->
                                              let uu____19987 =
                                                let uu____19988 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19988.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19987 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19991::[],body,uu____19993)
                                                   ->
                                                   let uu____20020 =
                                                     simp_t body  in
                                                   (match uu____20020 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20023 -> tm1)
                                               | uu____20026 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20028))::(t,uu____20030)::[]
                                              ->
                                              let uu____20069 =
                                                let uu____20070 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20070.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20069 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20073::[],body,uu____20075)
                                                   ->
                                                   let uu____20102 =
                                                     simp_t body  in
                                                   (match uu____20102 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____20105 -> tm1)
                                               | uu____20108 -> tm1)
                                          | uu____20109 -> tm1
                                        else
                                          (let uu____20119 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20119
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20120;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20121;_},uu____20122)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20139;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20140;_},uu____20141)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20158 -> tm1
                                           else
                                             (let uu____20168 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20168 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20188 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20203 = simp_t t  in
                      (match uu____20203 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20206 ->
                      let uu____20229 = is_const_match tm1  in
                      (match uu____20229 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20232 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____20243  ->
               let uu____20244 = FStar_Syntax_Print.tag_of_term t  in
               let uu____20245 = FStar_Syntax_Print.term_to_string t  in
               let uu____20246 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____20253 =
                 let uu____20254 =
                   let uu____20257 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____20257
                    in
                 stack_to_string uu____20254  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____20244 uu____20245 uu____20246 uu____20253);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____20288 =
                     let uu____20289 =
                       let uu____20290 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20290  in
                     FStar_Util.string_of_int uu____20289  in
                   let uu____20295 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20296 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20288 uu____20295 uu____20296)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____20350  ->
                     let uu____20351 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20351);
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
               let uu____20387 =
                 let uu___173_20388 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___173_20388.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___173_20388.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20387
           | (Arg (Univ uu____20389,uu____20390,uu____20391))::uu____20392 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20395,uu____20396))::uu____20397 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20412,uu____20413),aq,r))::stack1
               when
               let uu____20463 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20463 ->
               let t2 =
                 let uu____20467 =
                   let uu____20468 =
                     let uu____20469 = closure_as_term cfg env_arg tm  in
                     (uu____20469, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20468  in
                 uu____20467 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20475),aq,r))::stack1 ->
               (log cfg
                  (fun uu____20528  ->
                     let uu____20529 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20529);
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
                  (let uu____20539 = FStar_ST.op_Bang m  in
                   match uu____20539 with
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
                   | FStar_Pervasives_Native.Some (uu____20676,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20723 =
                 log cfg
                   (fun uu____20727  ->
                      let uu____20728 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20728);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____20732 =
                 let uu____20733 = FStar_Syntax_Subst.compress t1  in
                 uu____20733.FStar_Syntax_Syntax.n  in
               (match uu____20732 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____20760 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____20760  in
                    (log cfg
                       (fun uu____20764  ->
                          let uu____20765 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20765);
                     (let uu____20766 = FStar_List.tl stack  in
                      norm cfg env1 uu____20766 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20767);
                       FStar_Syntax_Syntax.pos = uu____20768;
                       FStar_Syntax_Syntax.vars = uu____20769;_},(e,uu____20771)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20800 when
                    (cfg.steps).primops ->
                    let uu____20815 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____20815 with
                     | (hd1,args) ->
                         let uu____20852 =
                           let uu____20853 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20853.FStar_Syntax_Syntax.n  in
                         (match uu____20852 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20857 = find_prim_step cfg fv  in
                              (match uu____20857 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20860; arity = uu____20861;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20863;
                                     requires_binder_substitution =
                                       uu____20864;
                                     interpretation = uu____20865;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20878 -> fallback " (3)" ())
                          | uu____20881 -> fallback " (4)" ()))
                | uu____20882 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (AscribedBy (env',(tc,tacopt),l,r))::stack1 ->
               let tc1 =
                 match tc with
                 | FStar_Util.Inl t2 ->
                     let uu____20961 = norm cfg env' [] t2  in
                     FStar_All.pipe_left (fun _0_44  -> FStar_Util.Inl _0_44)
                       uu____20961
                 | FStar_Util.Inr c ->
                     let uu____20973 = norm_comp cfg env' c  in
                     FStar_All.pipe_left (fun _0_45  -> FStar_Util.Inr _0_45)
                       uu____20973
                  in
               let tacopt1 = FStar_Util.map_opt tacopt (norm cfg env' [])  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_ascribed (t1, (tc1, tacopt1), l))
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env stack1 t2
           | (RefinedBy (x,env',f,r))::stack1 ->
               let x1 =
                 let uu___174_21012 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___174_21012.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___174_21012.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t1
                 }  in
               if (cfg.steps).weak
               then
                 let t2 =
                   let uu___175_21016 =
                     let uu____21019 = closure_as_term cfg env' f  in
                     FStar_Syntax_Util.refine x1 uu____21019  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___175_21016.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = r;
                     FStar_Syntax_Syntax.vars =
                       (uu___175_21016.FStar_Syntax_Syntax.vars)
                   }  in
                 rebuild cfg env' stack1 t2
               else norm cfg env' ((Refining (x1, r, env)) :: stack1) f
           | (Refining (x,r,env'))::stack1 ->
               let t2 =
                 let uu___176_21030 = FStar_Syntax_Util.refine x t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___176_21030.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___176_21030.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env' stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____21042  ->
                     let uu____21043 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21043);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21048 =
                   log cfg
                     (fun uu____21053  ->
                        let uu____21054 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21055 =
                          let uu____21056 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21073  ->
                                    match uu____21073 with
                                    | (p,uu____21083,uu____21084) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21056
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21054 uu____21055);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___91_21101  ->
                                match uu___91_21101 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21102 -> false))
                         in
                      let uu___177_21103 = cfg  in
                      {
                        steps =
                          (let uu___178_21106 = cfg.steps  in
                           {
                             beta = (uu___178_21106.beta);
                             iota = (uu___178_21106.iota);
                             zeta = false;
                             weak = (uu___178_21106.weak);
                             hnf = (uu___178_21106.hnf);
                             primops = (uu___178_21106.primops);
                             no_delta_steps = (uu___178_21106.no_delta_steps);
                             unfold_until = (uu___178_21106.unfold_until);
                             unfold_only = (uu___178_21106.unfold_only);
                             unfold_fully = (uu___178_21106.unfold_fully);
                             unfold_attr = (uu___178_21106.unfold_attr);
                             unfold_tac = (uu___178_21106.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___178_21106.pure_subterms_within_computations);
                             simplify = (uu___178_21106.simplify);
                             erase_universes =
                               (uu___178_21106.erase_universes);
                             allow_unbound_universes =
                               (uu___178_21106.allow_unbound_universes);
                             reify_ = (uu___178_21106.reify_);
                             compress_uvars = (uu___178_21106.compress_uvars);
                             no_full_norm = (uu___178_21106.no_full_norm);
                             check_no_uvars = (uu___178_21106.check_no_uvars);
                             unmeta = (uu___178_21106.unmeta);
                             unascribe = (uu___178_21106.unascribe)
                           });
                        tcenv = (uu___177_21103.tcenv);
                        debug = (uu___177_21103.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___177_21103.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___177_21103.memoize_lazy);
                        normalize_pure_lets =
                          (uu___177_21103.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21138 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21159 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21219  ->
                                    fun uu____21220  ->
                                      match (uu____21219, uu____21220) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21311 = norm_pat env3 p1
                                             in
                                          (match uu____21311 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21159 with
                           | (pats1,env3) ->
                               ((let uu___179_21393 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___179_21393.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___180_21412 = x  in
                            let uu____21413 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___180_21412.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___180_21412.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21413
                            }  in
                          ((let uu___181_21427 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___181_21427.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___182_21438 = x  in
                            let uu____21439 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___182_21438.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___182_21438.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21439
                            }  in
                          ((let uu___183_21453 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___183_21453.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___184_21469 = x  in
                            let uu____21470 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___184_21469.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___184_21469.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21470
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___185_21477 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___185_21477.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21487 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____21501 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____21501 with
                                  | (p,wopt,e) ->
                                      let uu____21521 = norm_pat env1 p  in
                                      (match uu____21521 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____21546 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____21546
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____21552 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____21552)
                    in
                 let rec is_cons head1 =
                   let uu____21557 =
                     let uu____21558 = FStar_Syntax_Subst.compress head1  in
                     uu____21558.FStar_Syntax_Syntax.n  in
                   match uu____21557 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____21562) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____21567 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21568;
                         FStar_Syntax_Syntax.fv_delta = uu____21569;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21570;
                         FStar_Syntax_Syntax.fv_delta = uu____21571;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____21572);_}
                       -> true
                   | uu____21579 -> false  in
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
                   let uu____21724 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____21724 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21811 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____21850 ->
                                 let uu____21851 =
                                   let uu____21852 = is_cons head1  in
                                   Prims.op_Negation uu____21852  in
                                 FStar_Util.Inr uu____21851)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____21877 =
                              let uu____21878 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____21878.FStar_Syntax_Syntax.n  in
                            (match uu____21877 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21896 ->
                                 let uu____21897 =
                                   let uu____21898 = is_cons head1  in
                                   Prims.op_Negation uu____21898  in
                                 FStar_Util.Inr uu____21897))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21977)::rest_a,(p1,uu____21980)::rest_p) ->
                       let uu____22024 = matches_pat t2 p1  in
                       (match uu____22024 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22073 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22179 = matches_pat scrutinee1 p1  in
                       (match uu____22179 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____22219  ->
                                  let uu____22220 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22221 =
                                    let uu____22222 =
                                      FStar_List.map
                                        (fun uu____22232  ->
                                           match uu____22232 with
                                           | (uu____22237,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22222
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22220 uu____22221);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22268  ->
                                       match uu____22268 with
                                       | (bv,t2) ->
                                           let uu____22291 =
                                             let uu____22298 =
                                               let uu____22301 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22301
                                                in
                                             let uu____22302 =
                                               let uu____22303 =
                                                 let uu____22334 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22334, false)
                                                  in
                                               Clos uu____22303  in
                                             (uu____22298, uu____22302)  in
                                           uu____22291 :: env2) env1 s
                                 in
                              let uu____22451 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____22451)))
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
    let uu____22474 =
      let uu____22477 = FStar_ST.op_Bang plugins  in p :: uu____22477  in
    FStar_ST.op_Colon_Equals plugins uu____22474  in
  let retrieve uu____22575 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____22640  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_22673  ->
                  match uu___92_22673 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____22677 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____22683 -> d  in
        let uu____22686 = to_fsteps s  in
        let uu____22687 =
          let uu____22688 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____22689 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____22690 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____22691 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____22692 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____22688;
            primop = uu____22689;
            b380 = uu____22690;
            norm_delayed = uu____22691;
            print_normalized = uu____22692
          }  in
        let uu____22693 =
          let uu____22696 =
            let uu____22699 = retrieve_plugins ()  in
            FStar_List.append uu____22699 psteps  in
          add_steps built_in_primitive_steps uu____22696  in
        let uu____22702 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____22704 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____22704)
           in
        {
          steps = uu____22686;
          tcenv = e;
          debug = uu____22687;
          delta_level = d1;
          primitive_steps = uu____22693;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____22702
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
      fun t  -> let uu____22762 = config s e  in norm_comp uu____22762 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____22775 = config [] env  in norm_universe uu____22775 [] u
  
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
        let uu____22793 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22793  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____22800 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___186_22819 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___186_22819.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___186_22819.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____22826 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____22826
          then
            let ct1 =
              let uu____22828 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____22828 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____22835 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____22835
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___187_22839 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___187_22839.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___187_22839.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___187_22839.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___188_22841 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___188_22841.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___188_22841.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___188_22841.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___188_22841.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___189_22842 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___189_22842.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___189_22842.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____22844 -> c
  
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
        let uu____22856 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22856  in
      let uu____22863 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____22863
      then
        let uu____22864 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____22864 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____22870  ->
                 let uu____22871 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____22871)
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
            ((let uu____22888 =
                let uu____22893 =
                  let uu____22894 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22894
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22893)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____22888);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____22905 = config [AllowUnboundUniverses] env  in
          norm_comp uu____22905 [] c
        with
        | e ->
            ((let uu____22918 =
                let uu____22923 =
                  let uu____22924 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22924
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22923)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22918);
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
                   let uu____22961 =
                     let uu____22962 =
                       let uu____22969 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____22969)  in
                     FStar_Syntax_Syntax.Tm_refine uu____22962  in
                   mk uu____22961 t01.FStar_Syntax_Syntax.pos
               | uu____22974 -> t2)
          | uu____22975 -> t2  in
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
        let uu____23015 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23015 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23044 ->
                 let uu____23051 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23051 with
                  | (actuals,uu____23061,uu____23062) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23076 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23076 with
                         | (binders,args) ->
                             let uu____23093 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23093
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
      | uu____23101 ->
          let uu____23102 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23102 with
           | (head1,args) ->
               let uu____23139 =
                 let uu____23140 = FStar_Syntax_Subst.compress head1  in
                 uu____23140.FStar_Syntax_Syntax.n  in
               (match uu____23139 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____23143,thead) ->
                    let uu____23169 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____23169 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23211 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___194_23219 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___194_23219.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___194_23219.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___194_23219.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___194_23219.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___194_23219.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___194_23219.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___194_23219.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___194_23219.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___194_23219.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___194_23219.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___194_23219.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___194_23219.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___194_23219.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___194_23219.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___194_23219.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___194_23219.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___194_23219.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___194_23219.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___194_23219.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___194_23219.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___194_23219.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___194_23219.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___194_23219.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___194_23219.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___194_23219.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___194_23219.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___194_23219.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___194_23219.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___194_23219.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___194_23219.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___194_23219.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___194_23219.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___194_23219.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____23211 with
                            | (uu____23220,ty,uu____23222) ->
                                eta_expand_with_type env t ty))
                | uu____23223 ->
                    let uu____23224 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___195_23232 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___195_23232.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___195_23232.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___195_23232.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___195_23232.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___195_23232.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___195_23232.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___195_23232.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___195_23232.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___195_23232.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___195_23232.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___195_23232.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___195_23232.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___195_23232.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___195_23232.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___195_23232.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___195_23232.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___195_23232.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___195_23232.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___195_23232.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___195_23232.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___195_23232.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___195_23232.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___195_23232.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___195_23232.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___195_23232.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___195_23232.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___195_23232.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___195_23232.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___195_23232.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___195_23232.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___195_23232.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___195_23232.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___195_23232.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____23224 with
                     | (uu____23233,ty,uu____23235) ->
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
      let uu___196_23292 = x  in
      let uu____23293 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___196_23292.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___196_23292.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23293
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23296 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23321 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23322 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23323 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23324 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23331 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23332 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23333 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___197_23361 = rc  in
          let uu____23362 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23369 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___197_23361.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23362;
            FStar_Syntax_Syntax.residual_flags = uu____23369
          }  in
        let uu____23372 =
          let uu____23373 =
            let uu____23390 = elim_delayed_subst_binders bs  in
            let uu____23397 = elim_delayed_subst_term t2  in
            let uu____23398 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23390, uu____23397, uu____23398)  in
          FStar_Syntax_Syntax.Tm_abs uu____23373  in
        mk1 uu____23372
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23427 =
          let uu____23428 =
            let uu____23441 = elim_delayed_subst_binders bs  in
            let uu____23448 = elim_delayed_subst_comp c  in
            (uu____23441, uu____23448)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23428  in
        mk1 uu____23427
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____23461 =
          let uu____23462 =
            let uu____23469 = elim_bv bv  in
            let uu____23470 = elim_delayed_subst_term phi  in
            (uu____23469, uu____23470)  in
          FStar_Syntax_Syntax.Tm_refine uu____23462  in
        mk1 uu____23461
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____23493 =
          let uu____23494 =
            let uu____23509 = elim_delayed_subst_term t2  in
            let uu____23510 = elim_delayed_subst_args args  in
            (uu____23509, uu____23510)  in
          FStar_Syntax_Syntax.Tm_app uu____23494  in
        mk1 uu____23493
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___198_23574 = p  in
              let uu____23575 =
                let uu____23576 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____23576  in
              {
                FStar_Syntax_Syntax.v = uu____23575;
                FStar_Syntax_Syntax.p =
                  (uu___198_23574.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___199_23578 = p  in
              let uu____23579 =
                let uu____23580 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____23580  in
              {
                FStar_Syntax_Syntax.v = uu____23579;
                FStar_Syntax_Syntax.p =
                  (uu___199_23578.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___200_23587 = p  in
              let uu____23588 =
                let uu____23589 =
                  let uu____23596 = elim_bv x  in
                  let uu____23597 = elim_delayed_subst_term t0  in
                  (uu____23596, uu____23597)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____23589  in
              {
                FStar_Syntax_Syntax.v = uu____23588;
                FStar_Syntax_Syntax.p =
                  (uu___200_23587.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___201_23616 = p  in
              let uu____23617 =
                let uu____23618 =
                  let uu____23631 =
                    FStar_List.map
                      (fun uu____23654  ->
                         match uu____23654 with
                         | (x,b) ->
                             let uu____23667 = elim_pat x  in
                             (uu____23667, b)) pats
                     in
                  (fv, uu____23631)  in
                FStar_Syntax_Syntax.Pat_cons uu____23618  in
              {
                FStar_Syntax_Syntax.v = uu____23617;
                FStar_Syntax_Syntax.p =
                  (uu___201_23616.FStar_Syntax_Syntax.p)
              }
          | uu____23680 -> p  in
        let elim_branch uu____23702 =
          match uu____23702 with
          | (pat,wopt,t3) ->
              let uu____23728 = elim_pat pat  in
              let uu____23731 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____23734 = elim_delayed_subst_term t3  in
              (uu____23728, uu____23731, uu____23734)
           in
        let uu____23739 =
          let uu____23740 =
            let uu____23763 = elim_delayed_subst_term t2  in
            let uu____23764 = FStar_List.map elim_branch branches  in
            (uu____23763, uu____23764)  in
          FStar_Syntax_Syntax.Tm_match uu____23740  in
        mk1 uu____23739
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____23873 =
          match uu____23873 with
          | (tc,topt) ->
              let uu____23908 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23918 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____23918
                | FStar_Util.Inr c ->
                    let uu____23920 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____23920
                 in
              let uu____23921 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____23908, uu____23921)
           in
        let uu____23930 =
          let uu____23931 =
            let uu____23958 = elim_delayed_subst_term t2  in
            let uu____23959 = elim_ascription a  in
            (uu____23958, uu____23959, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____23931  in
        mk1 uu____23930
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___202_24004 = lb  in
          let uu____24005 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24008 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___202_24004.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___202_24004.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24005;
            FStar_Syntax_Syntax.lbeff =
              (uu___202_24004.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24008;
            FStar_Syntax_Syntax.lbattrs =
              (uu___202_24004.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___202_24004.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24011 =
          let uu____24012 =
            let uu____24025 =
              let uu____24032 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24032)  in
            let uu____24041 = elim_delayed_subst_term t2  in
            (uu____24025, uu____24041)  in
          FStar_Syntax_Syntax.Tm_let uu____24012  in
        mk1 uu____24011
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____24074 =
          let uu____24075 =
            let uu____24092 = elim_delayed_subst_term t2  in
            (uv, uu____24092)  in
          FStar_Syntax_Syntax.Tm_uvar uu____24075  in
        mk1 uu____24074
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24110 =
          let uu____24111 =
            let uu____24118 = elim_delayed_subst_term tm  in
            (uu____24118, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24111  in
        mk1 uu____24110
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24125 =
          let uu____24126 =
            let uu____24133 = elim_delayed_subst_term t2  in
            let uu____24134 = elim_delayed_subst_meta md  in
            (uu____24133, uu____24134)  in
          FStar_Syntax_Syntax.Tm_meta uu____24126  in
        mk1 uu____24125

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_24141  ->
         match uu___93_24141 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24145 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24145
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
        let uu____24166 =
          let uu____24167 =
            let uu____24176 = elim_delayed_subst_term t  in
            (uu____24176, uopt)  in
          FStar_Syntax_Syntax.Total uu____24167  in
        mk1 uu____24166
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24189 =
          let uu____24190 =
            let uu____24199 = elim_delayed_subst_term t  in
            (uu____24199, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24190  in
        mk1 uu____24189
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___203_24204 = ct  in
          let uu____24205 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24208 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24217 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___203_24204.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___203_24204.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24205;
            FStar_Syntax_Syntax.effect_args = uu____24208;
            FStar_Syntax_Syntax.flags = uu____24217
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_24220  ->
    match uu___94_24220 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24232 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24232
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24265 =
          let uu____24272 = elim_delayed_subst_term t  in (m, uu____24272)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24265
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24280 =
          let uu____24289 = elim_delayed_subst_term t  in
          (m1, m2, uu____24289)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24280
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____24312  ->
         match uu____24312 with
         | (t,q) ->
             let uu____24323 = elim_delayed_subst_term t  in (uu____24323, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____24343  ->
         match uu____24343 with
         | (x,q) ->
             let uu____24354 =
               let uu___204_24355 = x  in
               let uu____24356 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___204_24355.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___204_24355.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24356
               }  in
             (uu____24354, q)) bs

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
            | (uu____24432,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____24438,FStar_Util.Inl t) ->
                let uu____24444 =
                  let uu____24447 =
                    let uu____24448 =
                      let uu____24461 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____24461)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____24448  in
                  FStar_Syntax_Syntax.mk uu____24447  in
                uu____24444 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____24465 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____24465 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____24493 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____24548 ->
                    let uu____24549 =
                      let uu____24558 =
                        let uu____24559 = FStar_Syntax_Subst.compress t4  in
                        uu____24559.FStar_Syntax_Syntax.n  in
                      (uu____24558, tc)  in
                    (match uu____24549 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____24584) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____24621) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____24660,FStar_Util.Inl uu____24661) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____24684 -> failwith "Impossible")
                 in
              (match uu____24493 with
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
          let uu____24789 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____24789 with
          | (univ_names1,binders1,tc) ->
              let uu____24847 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____24847)
  
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
          let uu____24882 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____24882 with
          | (univ_names1,binders1,tc) ->
              let uu____24942 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____24942)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____24975 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____24975 with
           | (univ_names1,binders1,typ1) ->
               let uu___205_25003 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_25003.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_25003.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_25003.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_25003.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___206_25024 = s  in
          let uu____25025 =
            let uu____25026 =
              let uu____25035 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25035, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25026  in
          {
            FStar_Syntax_Syntax.sigel = uu____25025;
            FStar_Syntax_Syntax.sigrng =
              (uu___206_25024.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___206_25024.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___206_25024.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___206_25024.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25052 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25052 with
           | (univ_names1,uu____25070,typ1) ->
               let uu___207_25084 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_25084.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_25084.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_25084.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_25084.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25090 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25090 with
           | (univ_names1,uu____25108,typ1) ->
               let uu___208_25122 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___208_25122.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___208_25122.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___208_25122.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___208_25122.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____25156 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____25156 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____25179 =
                            let uu____25180 =
                              let uu____25181 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____25181  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____25180
                             in
                          elim_delayed_subst_term uu____25179  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___209_25184 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___209_25184.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___209_25184.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___209_25184.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___209_25184.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___210_25185 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___210_25185.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_25185.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_25185.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___210_25185.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___211_25197 = s  in
          let uu____25198 =
            let uu____25199 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____25199  in
          {
            FStar_Syntax_Syntax.sigel = uu____25198;
            FStar_Syntax_Syntax.sigrng =
              (uu___211_25197.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___211_25197.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___211_25197.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___211_25197.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____25203 = elim_uvars_aux_t env us [] t  in
          (match uu____25203 with
           | (us1,uu____25221,t1) ->
               let uu___212_25235 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___212_25235.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___212_25235.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___212_25235.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___212_25235.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____25236 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____25238 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____25238 with
           | (univs1,binders,signature) ->
               let uu____25266 =
                 let uu____25275 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____25275 with
                 | (univs_opening,univs2) ->
                     let uu____25302 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____25302)
                  in
               (match uu____25266 with
                | (univs_opening,univs_closing) ->
                    let uu____25319 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____25325 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____25326 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____25325, uu____25326)  in
                    (match uu____25319 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____25348 =
                           match uu____25348 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____25366 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____25366 with
                                | (us1,t1) ->
                                    let uu____25377 =
                                      let uu____25382 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____25389 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____25382, uu____25389)  in
                                    (match uu____25377 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____25402 =
                                           let uu____25407 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____25416 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____25407, uu____25416)  in
                                         (match uu____25402 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____25432 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____25432
                                                 in
                                              let uu____25433 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____25433 with
                                               | (uu____25454,uu____25455,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____25470 =
                                                       let uu____25471 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____25471
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____25470
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____25476 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____25476 with
                           | (uu____25489,uu____25490,t1) -> t1  in
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
                             | uu____25550 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____25567 =
                               let uu____25568 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____25568.FStar_Syntax_Syntax.n  in
                             match uu____25567 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____25627 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____25656 =
                               let uu____25657 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____25657.FStar_Syntax_Syntax.n  in
                             match uu____25656 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____25678) ->
                                 let uu____25699 = destruct_action_body body
                                    in
                                 (match uu____25699 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____25744 ->
                                 let uu____25745 = destruct_action_body t  in
                                 (match uu____25745 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____25794 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____25794 with
                           | (action_univs,t) ->
                               let uu____25803 = destruct_action_typ_templ t
                                  in
                               (match uu____25803 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___213_25844 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___213_25844.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___213_25844.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___214_25846 = ed  in
                           let uu____25847 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____25848 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____25849 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____25850 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____25851 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____25852 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____25853 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____25854 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____25855 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____25856 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____25857 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____25858 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____25859 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____25860 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___214_25846.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___214_25846.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____25847;
                             FStar_Syntax_Syntax.bind_wp = uu____25848;
                             FStar_Syntax_Syntax.if_then_else = uu____25849;
                             FStar_Syntax_Syntax.ite_wp = uu____25850;
                             FStar_Syntax_Syntax.stronger = uu____25851;
                             FStar_Syntax_Syntax.close_wp = uu____25852;
                             FStar_Syntax_Syntax.assert_p = uu____25853;
                             FStar_Syntax_Syntax.assume_p = uu____25854;
                             FStar_Syntax_Syntax.null_wp = uu____25855;
                             FStar_Syntax_Syntax.trivial = uu____25856;
                             FStar_Syntax_Syntax.repr = uu____25857;
                             FStar_Syntax_Syntax.return_repr = uu____25858;
                             FStar_Syntax_Syntax.bind_repr = uu____25859;
                             FStar_Syntax_Syntax.actions = uu____25860;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___214_25846.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___215_25863 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___215_25863.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___215_25863.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___215_25863.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___215_25863.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_25880 =
            match uu___95_25880 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____25907 = elim_uvars_aux_t env us [] t  in
                (match uu____25907 with
                 | (us1,uu____25931,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___216_25950 = sub_eff  in
            let uu____25951 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____25954 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___216_25950.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___216_25950.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25951;
              FStar_Syntax_Syntax.lift = uu____25954
            }  in
          let uu___217_25957 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___217_25957.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___217_25957.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___217_25957.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___217_25957.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____25967 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____25967 with
           | (univ_names1,binders1,comp1) ->
               let uu___218_26001 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_26001.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_26001.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_26001.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_26001.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____26012 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____26013 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  