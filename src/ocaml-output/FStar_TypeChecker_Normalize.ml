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
  FStar_Pervasives_Native.tuple3 
  | Branches of (env,branches,branches,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____2211 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2247 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2283 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2352 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2394 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2450 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2490 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2522 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2558 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2574 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
let (uu___is_AscribedBy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | AscribedBy _0 -> true | uu____2608 -> false
  
let (__proj__AscribedBy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.ascription,FStar_Ident.lid
                                          FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | AscribedBy _0 -> _0 
let (uu___is_RefinedBy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | RefinedBy _0 -> true | uu____2658 -> false
  
let (__proj__RefinedBy__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.bv,env,FStar_Syntax_Syntax.term,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | RefinedBy _0 -> _0 
let (uu___is_Refining : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refining _0 -> true | uu____2700 -> false
  
let (__proj__Refining__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.bv,FStar_Range.range,env)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Refining _0 -> _0 
let (uu___is_Branches : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Branches _0 -> true | uu____2738 -> false
  
let (__proj__Branches__item___0 :
  stack_elt ->
    (env,branches,branches,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Branches _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2775 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2775 with | (hd1,uu____2789) -> hd1
  
let mk :
  'Auu____2809 .
    'Auu____2809 ->
      FStar_Range.range -> 'Auu____2809 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2863 = FStar_ST.op_Bang r  in
          match uu____2863 with
          | FStar_Pervasives_Native.Some uu____2911 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2965 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2965 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2972  ->
    match uu___80_2972 with
    | Arg (c,uu____2974,uu____2975) ->
        let uu____2976 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2976
    | MemoLazy uu____2977 -> "MemoLazy"
    | Abs (uu____2984,bs,uu____2986,uu____2987,uu____2988) ->
        let uu____2993 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2993
    | UnivArgs uu____2998 -> "UnivArgs"
    | Match uu____3005 -> "Match"
    | App (uu____3012,t,uu____3014,uu____3015) ->
        let uu____3016 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3016
    | Meta (m,uu____3018) -> "Meta"
    | Let uu____3019 -> "Let"
    | Cfg uu____3028 -> "Cfg"
    | Debug (t,uu____3030) ->
        let uu____3031 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3031
    | AscribedBy uu____3032 -> "AscribedBy"
    | RefinedBy uu____3043 -> "RefinedBy"
    | Refining uu____3052 -> "Refining"
    | Branches uu____3059 -> "Branches"
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3075 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3075 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3106 . 'Auu____3106 Prims.list -> Prims.bool =
  fun uu___81_3112  ->
    match uu___81_3112 with | [] -> true | uu____3115 -> false
  
let lookup_bvar :
  'Auu____3122 'Auu____3123 .
    ('Auu____3122,'Auu____3123) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____3123
  =
  fun env  ->
    fun x  ->
      try
        let uu____3147 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3147
      with
      | uu____3160 ->
          let uu____3161 =
            let uu____3162 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____3162  in
          failwith uu____3161
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3168 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3168
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3172 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3172
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3176 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3176
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
          let uu____3202 =
            FStar_List.fold_left
              (fun uu____3228  ->
                 fun u1  ->
                   match uu____3228 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3253 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3253 with
                        | (k_u,n1) ->
                            let uu____3268 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3268
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3202 with
          | (uu____3286,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3311 =
                   let uu____3312 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3312  in
                 match uu____3311 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3330 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3338 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3344 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3353 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3362 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3369 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3369 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3386 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3386 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3394 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3402 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3402 with
                                  | (uu____3407,m) -> n1 <= m))
                           in
                        if uu____3394 then rest1 else us1
                    | uu____3412 -> us1)
               | uu____3417 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3421 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3421
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3425 = aux u  in
           match uu____3425 with
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
          (fun uu____3529  ->
             let uu____3530 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3531 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3530
               uu____3531);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3538 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3540 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3565 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3566 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3567 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3568 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3569 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3586 =
                      let uu____3587 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3588 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3587 uu____3588
                       in
                    failwith uu____3586
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3591 =
                    let uu____3592 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3592  in
                  mk uu____3591 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3599 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3599
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3601 = lookup_bvar env x  in
                  (match uu____3601 with
                   | Univ uu____3604 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3607,uu____3608) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3720 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3720 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3748 =
                         let uu____3749 =
                           let uu____3766 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3766)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3749  in
                       mk uu____3748 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3797 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3797 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3839 =
                    let uu____3850 =
                      let uu____3857 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3857]  in
                    closures_as_binders_delayed cfg env uu____3850  in
                  (match uu____3839 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3875 =
                         let uu____3876 =
                           let uu____3883 =
                             let uu____3884 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3884
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3883, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3876  in
                       mk uu____3875 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3975 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3975
                    | FStar_Util.Inr c ->
                        let uu____3989 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3989
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____4005 =
                    let uu____4006 =
                      let uu____4033 = closure_as_term_delayed cfg env t11
                         in
                      (uu____4033, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____4006  in
                  mk uu____4005 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                  (match qi.FStar_Syntax_Syntax.qkind with
                   | FStar_Syntax_Syntax.Quote_dynamic  ->
                       let uu____4074 =
                         let uu____4075 =
                           let uu____4082 =
                             closure_as_term_delayed cfg env t'  in
                           (uu____4082, qi)  in
                         FStar_Syntax_Syntax.Tm_quoted uu____4075  in
                       mk uu____4074 t1.FStar_Syntax_Syntax.pos
                   | FStar_Syntax_Syntax.Quote_static  ->
                       let qi1 =
                         FStar_Syntax_Syntax.on_antiquoted
                           (closure_as_term_delayed cfg env) qi
                          in
                       mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____4106 =
                    let uu____4107 =
                      let uu____4114 = closure_as_term_delayed cfg env t'  in
                      let uu____4117 =
                        let uu____4118 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____4118  in
                      (uu____4114, uu____4117)  in
                    FStar_Syntax_Syntax.Tm_meta uu____4107  in
                  mk uu____4106 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____4178 =
                    let uu____4179 =
                      let uu____4186 = closure_as_term_delayed cfg env t'  in
                      let uu____4189 =
                        let uu____4190 =
                          let uu____4197 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____4197)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____4190  in
                      (uu____4186, uu____4189)  in
                    FStar_Syntax_Syntax.Tm_meta uu____4179  in
                  mk uu____4178 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____4216 =
                    let uu____4217 =
                      let uu____4224 = closure_as_term_delayed cfg env t'  in
                      let uu____4227 =
                        let uu____4228 =
                          let uu____4237 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____4237)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____4228  in
                      (uu____4224, uu____4227)  in
                    FStar_Syntax_Syntax.Tm_meta uu____4217  in
                  mk uu____4216 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____4250 =
                    let uu____4251 =
                      let uu____4258 = closure_as_term_delayed cfg env t'  in
                      (uu____4258, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____4251  in
                  mk uu____4250 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____4298  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____4317 =
                    let uu____4328 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____4328
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____4347 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___125_4359 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_4359.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_4359.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____4347))
                     in
                  (match uu____4317 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___126_4375 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___126_4375.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___126_4375.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___126_4375.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___126_4375.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____4386,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4445  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4470 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4470
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4490  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4512 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4512
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___127_4524 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_4524.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_4524.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___128_4525 = lb  in
                    let uu____4526 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___128_4525.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___128_4525.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4526;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___128_4525.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___128_4525.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4556  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4645 =
                    match uu____4645 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4700 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4721 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4781  ->
                                        fun uu____4782  ->
                                          match (uu____4781, uu____4782) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4873 =
                                                norm_pat env3 p1  in
                                              (match uu____4873 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4721 with
                               | (pats1,env3) ->
                                   ((let uu___129_4955 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___129_4955.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___130_4974 = x  in
                                let uu____4975 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___130_4974.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___130_4974.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4975
                                }  in
                              ((let uu___131_4989 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___131_4989.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___132_5000 = x  in
                                let uu____5001 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___132_5000.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___132_5000.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____5001
                                }  in
                              ((let uu___133_5015 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___133_5015.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___134_5031 = x  in
                                let uu____5032 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___134_5031.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___134_5031.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____5032
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___135_5039 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___135_5039.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____5042 = norm_pat env1 pat  in
                        (match uu____5042 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____5071 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____5071
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____5077 =
                    let uu____5078 =
                      let uu____5101 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____5101)  in
                    FStar_Syntax_Syntax.Tm_match uu____5078  in
                  mk uu____5077 t1.FStar_Syntax_Syntax.pos))

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
        | uu____5187 -> closure_as_term cfg env t

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
        | uu____5213 ->
            FStar_List.map
              (fun uu____5230  ->
                 match uu____5230 with
                 | (x,imp) ->
                     let uu____5249 = closure_as_term_delayed cfg env x  in
                     (uu____5249, imp)) args

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
        let uu____5263 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5312  ->
                  fun uu____5313  ->
                    match (uu____5312, uu____5313) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___136_5383 = b  in
                          let uu____5384 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___136_5383.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___136_5383.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5384
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5263 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5477 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5490 = closure_as_term_delayed cfg env t  in
                 let uu____5491 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5490 uu____5491
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5504 = closure_as_term_delayed cfg env t  in
                 let uu____5505 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5504 uu____5505
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
                        (fun uu___82_5531  ->
                           match uu___82_5531 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5535 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5535
                           | f -> f))
                    in
                 let uu____5539 =
                   let uu___137_5540 = c1  in
                   let uu____5541 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5541;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___137_5540.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5539)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5551  ->
            match uu___83_5551 with
            | FStar_Syntax_Syntax.DECREASES uu____5552 -> false
            | uu____5555 -> true))

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
                   (fun uu___84_5573  ->
                      match uu___84_5573 with
                      | FStar_Syntax_Syntax.DECREASES uu____5574 -> false
                      | uu____5577 -> true))
               in
            let rc1 =
              let uu___138_5579 = rc  in
              let uu____5580 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___138_5579.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5580;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5587 -> lopt

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
    let uu____5669 =
      let uu____5676 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____5676  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5669  in
  let arg_as_bounded_int uu____5700 =
    match uu____5700 with
    | (a,uu____5712) ->
        let uu____5719 =
          let uu____5720 = FStar_Syntax_Subst.compress a  in
          uu____5720.FStar_Syntax_Syntax.n  in
        (match uu____5719 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5730;
                FStar_Syntax_Syntax.vars = uu____5731;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5733;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5734;_},uu____5735)::[])
             when
             let uu____5774 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5774 "int_to_t" ->
             let uu____5775 =
               let uu____5780 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5780)  in
             FStar_Pervasives_Native.Some uu____5775
         | uu____5785 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5825 = f a  in FStar_Pervasives_Native.Some uu____5825
    | uu____5826 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5874 = f a0 a1  in FStar_Pervasives_Native.Some uu____5874
    | uu____5875 -> FStar_Pervasives_Native.None  in
  let unary_op a394 a395 a396 a397 a398 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5917 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a393  -> (Obj.magic (f res.psc_range)) a393)
                    uu____5917)) a394 a395 a396 a397 a398
     in
  let binary_op a401 a402 a403 a404 a405 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5966 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a399  ->
                       fun a400  -> (Obj.magic (f res.psc_range)) a399 a400)
                    uu____5966)) a401 a402 a403 a404 a405
     in
  let as_primitive_step is_strong uu____5993 =
    match uu____5993 with
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
                   let uu____6041 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____6041)) a407 a408)
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
                       let uu____6069 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____6069)) a410
               a411 a412)
     in
  let unary_bool_op f =
    unary_op () (fun a413  -> (Obj.magic arg_as_bool) a413)
      (fun a414  ->
         fun a415  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6090 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____6090)) a414 a415)
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
                       let uu____6118 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____6118)) a417
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
                       let uu____6146 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____6146)) a421
               a422 a423)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____6254 =
          let uu____6263 = as_a a  in
          let uu____6266 = as_b b  in (uu____6263, uu____6266)  in
        (match uu____6254 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6281 =
               let uu____6282 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6282  in
             FStar_Pervasives_Native.Some uu____6281
         | uu____6283 -> FStar_Pervasives_Native.None)
    | uu____6292 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____6306 =
        let uu____6307 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____6307  in
      mk uu____6306 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____6317 =
      let uu____6320 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____6320  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6317  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____6352 =
      let uu____6353 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____6353  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____6352
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6371 = arg_as_string a1  in
        (match uu____6371 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6377 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2)
                in
             (match uu____6377 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6390 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____6390
              | uu____6391 -> FStar_Pervasives_Native.None)
         | uu____6396 -> FStar_Pervasives_Native.None)
    | uu____6399 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____6409 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____6409
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6438 =
          let uu____6459 = arg_as_string fn  in
          let uu____6462 = arg_as_int from_line  in
          let uu____6465 = arg_as_int from_col  in
          let uu____6468 = arg_as_int to_line  in
          let uu____6471 = arg_as_int to_col  in
          (uu____6459, uu____6462, uu____6465, uu____6468, uu____6471)  in
        (match uu____6438 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6502 =
                 let uu____6503 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6504 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6503 uu____6504  in
               let uu____6505 =
                 let uu____6506 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6507 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6506 uu____6507  in
               FStar_Range.mk_range fn1 uu____6502 uu____6505  in
             let uu____6508 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6508
         | uu____6509 -> FStar_Pervasives_Native.None)
    | uu____6530 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6557)::(a1,uu____6559)::(a2,uu____6561)::[] ->
        let uu____6598 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6598 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6611 -> FStar_Pervasives_Native.None)
    | uu____6612 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6639)::[] ->
        let uu____6648 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____6648 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6654 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6654
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6655 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6679 =
      let uu____6694 =
        let uu____6709 =
          let uu____6724 =
            let uu____6739 =
              let uu____6754 =
                let uu____6769 =
                  let uu____6784 =
                    let uu____6799 =
                      let uu____6814 =
                        let uu____6829 =
                          let uu____6844 =
                            let uu____6859 =
                              let uu____6874 =
                                let uu____6889 =
                                  let uu____6904 =
                                    let uu____6919 =
                                      let uu____6934 =
                                        let uu____6949 =
                                          let uu____6964 =
                                            let uu____6979 =
                                              let uu____6994 =
                                                let uu____7007 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____7007,
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
                                              let uu____7014 =
                                                let uu____7029 =
                                                  let uu____7042 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____7042,
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
                                                let uu____7049 =
                                                  let uu____7064 =
                                                    let uu____7079 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____7079,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____7088 =
                                                    let uu____7105 =
                                                      let uu____7120 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____7120,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____7105]  in
                                                  uu____7064 :: uu____7088
                                                   in
                                                uu____7029 :: uu____7049  in
                                              uu____6994 :: uu____7014  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6979
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6964
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
                                          :: uu____6949
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
                                        :: uu____6934
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
                                      :: uu____6919
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
                                                        let uu____7311 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____7311 y)) a444
                                                a445 a446)))
                                    :: uu____6904
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6889
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6874
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6859
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6844
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6829
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6814
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
                                          let uu____7478 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____7478)) a448 a449 a450)))
                      :: uu____6799
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
                                        let uu____7504 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____7504)) a452 a453 a454)))
                    :: uu____6784
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
                                      let uu____7530 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____7530)) a456 a457 a458)))
                  :: uu____6769
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
                                    let uu____7556 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____7556)) a460 a461 a462)))
                :: uu____6754
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6739
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6724
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6709
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6694
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6679
     in
  let weak_ops =
    let uu____7695 =
      let uu____7714 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7714, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7695]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7798 =
        let uu____7799 =
          let uu____7800 = FStar_Syntax_Syntax.as_arg c  in [uu____7800]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7799  in
      uu____7798 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7850 =
                let uu____7863 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7863, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a463  -> (Obj.magic arg_as_bounded_int) a463)
                     (fun a464  ->
                        fun a465  ->
                          fun a466  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7879  ->
                                    fun uu____7880  ->
                                      match (uu____7879, uu____7880) with
                                      | ((int_to_t1,x),(uu____7899,y)) ->
                                          let uu____7909 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7909)) a464 a465 a466)))
                 in
              let uu____7910 =
                let uu____7925 =
                  let uu____7938 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7938, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a467  -> (Obj.magic arg_as_bounded_int) a467)
                       (fun a468  ->
                          fun a469  ->
                            fun a470  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7954  ->
                                      fun uu____7955  ->
                                        match (uu____7954, uu____7955) with
                                        | ((int_to_t1,x),(uu____7974,y)) ->
                                            let uu____7984 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7984)) a468 a469 a470)))
                   in
                let uu____7985 =
                  let uu____8000 =
                    let uu____8013 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____8013, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a471  -> (Obj.magic arg_as_bounded_int) a471)
                         (fun a472  ->
                            fun a473  ->
                              fun a474  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8029  ->
                                        fun uu____8030  ->
                                          match (uu____8029, uu____8030) with
                                          | ((int_to_t1,x),(uu____8049,y)) ->
                                              let uu____8059 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____8059)) a472 a473 a474)))
                     in
                  let uu____8060 =
                    let uu____8075 =
                      let uu____8088 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____8088, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a475  -> (Obj.magic arg_as_bounded_int) a475)
                           (fun a476  ->
                              fun a477  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8100  ->
                                        match uu____8100 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a476 a477)))
                       in
                    [uu____8075]  in
                  uu____8000 :: uu____8060  in
                uu____7925 :: uu____7985  in
              uu____7850 :: uu____7910))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____8214 =
                let uu____8227 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____8227, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a478  -> (Obj.magic arg_as_bounded_int) a478)
                     (fun a479  ->
                        fun a480  ->
                          fun a481  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8243  ->
                                    fun uu____8244  ->
                                      match (uu____8243, uu____8244) with
                                      | ((int_to_t1,x),(uu____8263,y)) ->
                                          let uu____8273 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8273)) a479 a480 a481)))
                 in
              let uu____8274 =
                let uu____8289 =
                  let uu____8302 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____8302, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                       (fun a483  ->
                          fun a484  ->
                            fun a485  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8318  ->
                                      fun uu____8319  ->
                                        match (uu____8318, uu____8319) with
                                        | ((int_to_t1,x),(uu____8338,y)) ->
                                            let uu____8348 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8348)) a483 a484 a485)))
                   in
                [uu____8289]  in
              uu____8214 :: uu____8274))
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
    | (_typ,uu____8460)::(a1,uu____8462)::(a2,uu____8464)::[] ->
        let uu____8501 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8501 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8507 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8507.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8507.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8511 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8511.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8511.FStar_Syntax_Syntax.vars)
                })
         | uu____8512 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8514)::uu____8515::(a1,uu____8517)::(a2,uu____8519)::[] ->
        let uu____8568 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8568 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8574 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8574.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8574.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8578 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8578.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8578.FStar_Syntax_Syntax.vars)
                })
         | uu____8579 -> FStar_Pervasives_Native.None)
    | uu____8580 -> failwith "Unexpected number of arguments"  in
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
    let uu____8632 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8632 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8677 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8677) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8737  ->
           fun subst1  ->
             match uu____8737 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8778,uu____8779)) ->
                      let uu____8838 = b  in
                      (match uu____8838 with
                       | (bv,uu____8846) ->
                           let uu____8847 =
                             let uu____8848 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8848  in
                           if uu____8847
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8853 = unembed_binder term1  in
                              match uu____8853 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8860 =
                                      let uu___141_8861 = bv  in
                                      let uu____8862 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___141_8861.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___141_8861.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8862
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8860
                                     in
                                  let b_for_x =
                                    let uu____8866 =
                                      let uu____8873 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8873)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8866  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_8883  ->
                                         match uu___85_8883 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8884,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8886;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8887;_})
                                             ->
                                             let uu____8892 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____8892
                                         | uu____8893 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8894 -> subst1)) env []
  
let reduce_primops :
  'Auu____8911 'Auu____8912 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8911) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8912 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8954 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8954 with
             | (head1,args) ->
                 let uu____8991 =
                   let uu____8992 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8992.FStar_Syntax_Syntax.n  in
                 (match uu____8991 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8996 = find_prim_step cfg fv  in
                      (match uu____8996 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____9018  ->
                                   let uu____9019 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____9020 =
                                     FStar_Util.string_of_int l  in
                                   let uu____9027 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____9019 uu____9020 uu____9027);
                              tm)
                           else
                             (let uu____9029 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____9029 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____9140  ->
                                        let uu____9141 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____9141);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____9144  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____9146 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____9146 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____9152  ->
                                              let uu____9153 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____9153);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____9159  ->
                                              let uu____9160 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____9161 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____9160 uu____9161);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____9162 ->
                           (log_primops cfg
                              (fun uu____9166  ->
                                 let uu____9167 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____9167);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9171  ->
                            let uu____9172 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9172);
                       (match args with
                        | (a1,uu____9174)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____9191 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9203  ->
                            let uu____9204 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9204);
                       (match args with
                        | (t,uu____9206)::(r,uu____9208)::[] ->
                            let uu____9235 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____9235 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___142_9239 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___142_9239.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___142_9239.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____9242 -> tm))
                  | uu____9251 -> tm))
  
let reduce_equality :
  'Auu____9256 'Auu____9257 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9256) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9257 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___143_9295 = cfg  in
         {
           steps =
             (let uu___144_9298 = default_steps  in
              {
                beta = (uu___144_9298.beta);
                iota = (uu___144_9298.iota);
                zeta = (uu___144_9298.zeta);
                weak = (uu___144_9298.weak);
                hnf = (uu___144_9298.hnf);
                primops = true;
                no_delta_steps = (uu___144_9298.no_delta_steps);
                unfold_until = (uu___144_9298.unfold_until);
                unfold_only = (uu___144_9298.unfold_only);
                unfold_fully = (uu___144_9298.unfold_fully);
                unfold_attr = (uu___144_9298.unfold_attr);
                unfold_tac = (uu___144_9298.unfold_tac);
                pure_subterms_within_computations =
                  (uu___144_9298.pure_subterms_within_computations);
                simplify = (uu___144_9298.simplify);
                erase_universes = (uu___144_9298.erase_universes);
                allow_unbound_universes =
                  (uu___144_9298.allow_unbound_universes);
                reify_ = (uu___144_9298.reify_);
                compress_uvars = (uu___144_9298.compress_uvars);
                no_full_norm = (uu___144_9298.no_full_norm);
                check_no_uvars = (uu___144_9298.check_no_uvars);
                unmeta = (uu___144_9298.unmeta);
                unascribe = (uu___144_9298.unascribe)
              });
           tcenv = (uu___143_9295.tcenv);
           debug = (uu___143_9295.debug);
           delta_level = (uu___143_9295.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___143_9295.strong);
           memoize_lazy = (uu___143_9295.memoize_lazy);
           normalize_pure_lets = (uu___143_9295.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____9302 .
    FStar_Syntax_Syntax.term -> 'Auu____9302 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9315 =
        let uu____9322 =
          let uu____9323 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9323.FStar_Syntax_Syntax.n  in
        (uu____9322, args)  in
      match uu____9315 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9329::uu____9330::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9334::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____9339::uu____9340::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9343 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_9354  ->
    match uu___86_9354 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9360 =
          let uu____9363 =
            let uu____9364 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____9364  in
          [uu____9363]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9360
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____9370 =
          let uu____9373 =
            let uu____9374 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldFully uu____9374  in
          [uu____9373]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9370
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____9390 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____9390) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____9432 =
          let uu____9437 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____9437 s  in
        match uu____9432 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____9453 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____9453
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____9470::(tm,uu____9472)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____9501)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____9522)::uu____9523::(tm,uu____9525)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9562 =
            let uu____9567 = full_norm steps  in parse_steps uu____9567  in
          (match uu____9562 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9606 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_9623  ->
    match uu___87_9623 with
    | (App
        (uu____9626,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9627;
                      FStar_Syntax_Syntax.vars = uu____9628;_},uu____9629,uu____9630))::uu____9631
        -> true
    | uu____9638 -> false
  
let firstn :
  'Auu____9644 .
    Prims.int ->
      'Auu____9644 Prims.list ->
        ('Auu____9644 Prims.list,'Auu____9644 Prims.list)
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
          (uu____9680,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9681;
                        FStar_Syntax_Syntax.vars = uu____9682;_},uu____9683,uu____9684))::uu____9685
          -> (cfg.steps).reify_
      | uu____9692 -> false
  
let rec (is_cons : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun head1  ->
    let uu____9698 =
      let uu____9699 = FStar_Syntax_Subst.compress head1  in
      uu____9699.FStar_Syntax_Syntax.n  in
    match uu____9698 with
    | FStar_Syntax_Syntax.Tm_uinst (h,uu____9703) -> is_cons h
    | FStar_Syntax_Syntax.Tm_constant uu____9708 -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____9709;
          FStar_Syntax_Syntax.fv_delta = uu____9710;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____9711;
          FStar_Syntax_Syntax.fv_delta = uu____9712;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____9713);_}
        -> true
    | uu____9720 -> false
  
let rec (matches_pat :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.pat ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2 Prims.list,Prims.bool)
        FStar_Util.either)
  =
  fun scrutinee_orig  ->
    fun p  ->
      let scrutinee = FStar_Syntax_Util.unmeta scrutinee_orig  in
      let uu____9776 = FStar_Syntax_Util.head_and_args scrutinee  in
      match uu____9776 with
      | (head1,args) ->
          (match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_var bv ->
               FStar_Util.Inl [(bv, scrutinee_orig)]
           | FStar_Syntax_Syntax.Pat_wild bv ->
               FStar_Util.Inl [(bv, scrutinee_orig)]
           | FStar_Syntax_Syntax.Pat_dot_term uu____9863 -> FStar_Util.Inl []
           | FStar_Syntax_Syntax.Pat_constant s ->
               (match scrutinee.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_constant s' when
                    FStar_Const.eq_const s s' -> FStar_Util.Inl []
                | uu____9902 ->
                    let uu____9903 =
                      let uu____9904 = is_cons head1  in
                      Prims.op_Negation uu____9904  in
                    FStar_Util.Inr uu____9903)
           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
               let uu____9929 =
                 let uu____9930 = FStar_Syntax_Util.un_uinst head1  in
                 uu____9930.FStar_Syntax_Syntax.n  in
               (match uu____9929 with
                | FStar_Syntax_Syntax.Tm_fvar fv' when
                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                    matches_args [] args arg_pats
                | uu____9948 ->
                    let uu____9949 =
                      let uu____9950 = is_cons head1  in
                      Prims.op_Negation uu____9950  in
                    FStar_Util.Inr uu____9949))

and (matches_args :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.args ->
      (FStar_Syntax_Syntax.pat,Prims.bool) FStar_Pervasives_Native.tuple2
        Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2 Prims.list,Prims.bool)
          FStar_Util.either)
  =
  fun out  ->
    fun a  ->
      fun p  ->
        match (a, p) with
        | ([],[]) -> FStar_Util.Inl out
        | ((t,uu____10019)::rest_a,(p1,uu____10022)::rest_p) ->
            let uu____10066 = matches_pat t p1  in
            (match uu____10066 with
             | FStar_Util.Inl s ->
                 matches_args (FStar_List.append out s) rest_a rest_p
             | m -> m)
        | uu____10115 -> FStar_Util.Inr false

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
               | FStar_Syntax_Syntax.Tm_delayed uu____10313 ->
                   let uu____10338 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____10338
               | uu____10339 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____10347  ->
               let uu____10348 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____10349 = FStar_Syntax_Print.term_to_string t1  in
               let uu____10350 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____10357 =
                 let uu____10358 =
                   let uu____10361 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10361
                    in
                 stack_to_string uu____10358  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____10348 uu____10349 uu____10350 uu____10357);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____10384 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____10385 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____10386 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10387;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____10388;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10391;
                 FStar_Syntax_Syntax.fv_delta = uu____10392;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10393;
                 FStar_Syntax_Syntax.fv_delta = uu____10394;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10395);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____10402 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____10438 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____10438)
               ->
               let cfg' =
                 let uu___145_10440 = cfg  in
                 {
                   steps =
                     (let uu___146_10443 = cfg.steps  in
                      {
                        beta = (uu___146_10443.beta);
                        iota = (uu___146_10443.iota);
                        zeta = (uu___146_10443.zeta);
                        weak = (uu___146_10443.weak);
                        hnf = (uu___146_10443.hnf);
                        primops = (uu___146_10443.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___146_10443.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___146_10443.unfold_attr);
                        unfold_tac = (uu___146_10443.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___146_10443.pure_subterms_within_computations);
                        simplify = (uu___146_10443.simplify);
                        erase_universes = (uu___146_10443.erase_universes);
                        allow_unbound_universes =
                          (uu___146_10443.allow_unbound_universes);
                        reify_ = (uu___146_10443.reify_);
                        compress_uvars = (uu___146_10443.compress_uvars);
                        no_full_norm = (uu___146_10443.no_full_norm);
                        check_no_uvars = (uu___146_10443.check_no_uvars);
                        unmeta = (uu___146_10443.unmeta);
                        unascribe = (uu___146_10443.unascribe)
                      });
                   tcenv = (uu___145_10440.tcenv);
                   debug = (uu___145_10440.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___145_10440.primitive_steps);
                   strong = (uu___145_10440.strong);
                   memoize_lazy = (uu___145_10440.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____10448 = get_norm_request (norm cfg' env []) args  in
               (match uu____10448 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____10479  ->
                              fun stack1  ->
                                match uu____10479 with
                                | (a,aq) ->
                                    let uu____10491 =
                                      let uu____10492 =
                                        let uu____10499 =
                                          let uu____10500 =
                                            let uu____10531 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____10531, false)  in
                                          Clos uu____10500  in
                                        (uu____10499, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____10492  in
                                    uu____10491 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____10615  ->
                          let uu____10616 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10616);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____10638 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_10643  ->
                                match uu___88_10643 with
                                | UnfoldUntil uu____10644 -> true
                                | UnfoldOnly uu____10645 -> true
                                | UnfoldFully uu____10648 -> true
                                | uu____10651 -> false))
                         in
                      if uu____10638
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___147_10656 = cfg  in
                      let uu____10657 = to_fsteps s  in
                      {
                        steps = uu____10657;
                        tcenv = (uu___147_10656.tcenv);
                        debug = (uu___147_10656.debug);
                        delta_level;
                        primitive_steps = (uu___147_10656.primitive_steps);
                        strong = (uu___147_10656.strong);
                        memoize_lazy = (uu___147_10656.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____10666 =
                          let uu____10667 =
                            let uu____10672 = FStar_Util.now ()  in
                            (t1, uu____10672)  in
                          Debug uu____10667  in
                        uu____10666 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10676 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10676
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10685 =
                      let uu____10692 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10692, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10685  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____10702 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____10702  in
               let uu____10703 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____10703
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____10709  ->
                       let uu____10710 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10711 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____10710 uu____10711);
                  if b
                  then
                    (let uu____10712 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____10712 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____10720 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____10720) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_10726  ->
                               match uu___89_10726 with
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
                          (let uu____10736 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____10736))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____10755) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____10790,uu____10791) -> false)))
                     in
                  let uu____10808 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____10824 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____10824 then (true, true) else (false, false)
                     in
                  match uu____10808 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____10837  ->
                            let uu____10838 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____10839 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____10840 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____10838 uu____10839 uu____10840);
                       if should_delta2
                       then
                         (let uu____10841 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___148_10857 = cfg  in
                                 {
                                   steps =
                                     (let uu___149_10860 = cfg.steps  in
                                      {
                                        beta = (uu___149_10860.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        no_delta_steps =
                                          (uu___149_10860.no_delta_steps);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___149_10860.unfold_attr);
                                        unfold_tac =
                                          (uu___149_10860.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___149_10860.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___149_10860.erase_universes);
                                        allow_unbound_universes =
                                          (uu___149_10860.allow_unbound_universes);
                                        reify_ = (uu___149_10860.reify_);
                                        compress_uvars =
                                          (uu___149_10860.compress_uvars);
                                        no_full_norm =
                                          (uu___149_10860.no_full_norm);
                                        check_no_uvars =
                                          (uu___149_10860.check_no_uvars);
                                        unmeta = (uu___149_10860.unmeta);
                                        unascribe =
                                          (uu___149_10860.unascribe)
                                      });
                                   tcenv = (uu___148_10857.tcenv);
                                   debug = (uu___148_10857.debug);
                                   delta_level = (uu___148_10857.delta_level);
                                   primitive_steps =
                                     (uu___148_10857.primitive_steps);
                                   strong = (uu___148_10857.strong);
                                   memoize_lazy =
                                     (uu___148_10857.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___148_10857.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____10841 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10874 = lookup_bvar env x  in
               (match uu____10874 with
                | Univ uu____10877 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10926 = FStar_ST.op_Bang r  in
                      (match uu____10926 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11044  ->
                                 let uu____11045 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____11046 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11045
                                   uu____11046);
                            (let uu____11047 =
                               let uu____11048 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____11048.FStar_Syntax_Syntax.n  in
                             match uu____11047 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11051 ->
                                 norm cfg env2 stack t'
                             | uu____11068 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11138)::uu____11139 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11148)::uu____11149 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11159,uu____11160))::stack_rest ->
                    (match c with
                     | Univ uu____11164 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11173 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11194  ->
                                    let uu____11195 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11195);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11235  ->
                                    let uu____11236 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11236);
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
                       (fun uu____11314  ->
                          let uu____11315 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11315);
                     norm cfg env stack1 t1)
                | (Debug uu____11316)::uu____11317 ->
                    if (cfg.steps).weak
                    then
                      let uu____11324 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11324
                    else
                      (let uu____11326 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11326 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11368  -> dummy :: env1) env)
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
                                          let uu____11405 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11405)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11410 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11410.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11410.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11411 -> lopt  in
                           (log cfg
                              (fun uu____11417  ->
                                 let uu____11418 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11418);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11427 = cfg  in
                               {
                                 steps = (uu___151_11427.steps);
                                 tcenv = (uu___151_11427.tcenv);
                                 debug = (uu___151_11427.debug);
                                 delta_level = (uu___151_11427.delta_level);
                                 primitive_steps =
                                   (uu___151_11427.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11427.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11427.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11438)::uu____11439 ->
                    if (cfg.steps).weak
                    then
                      let uu____11446 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11446
                    else
                      (let uu____11448 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11448 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11490  -> dummy :: env1) env)
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
                                          let uu____11527 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11527)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11532 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11532.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11532.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11533 -> lopt  in
                           (log cfg
                              (fun uu____11539  ->
                                 let uu____11540 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11540);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11549 = cfg  in
                               {
                                 steps = (uu___151_11549.steps);
                                 tcenv = (uu___151_11549.tcenv);
                                 debug = (uu___151_11549.debug);
                                 delta_level = (uu___151_11549.delta_level);
                                 primitive_steps =
                                   (uu___151_11549.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11549.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11549.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11560)::uu____11561 ->
                    if (cfg.steps).weak
                    then
                      let uu____11572 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11572
                    else
                      (let uu____11574 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11574 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11616  -> dummy :: env1) env)
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
                                          let uu____11653 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11653)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11658 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11658.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11658.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11659 -> lopt  in
                           (log cfg
                              (fun uu____11665  ->
                                 let uu____11666 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11666);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11675 = cfg  in
                               {
                                 steps = (uu___151_11675.steps);
                                 tcenv = (uu___151_11675.tcenv);
                                 debug = (uu___151_11675.debug);
                                 delta_level = (uu___151_11675.delta_level);
                                 primitive_steps =
                                   (uu___151_11675.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11675.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11675.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11686)::uu____11687 ->
                    if (cfg.steps).weak
                    then
                      let uu____11698 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11698
                    else
                      (let uu____11700 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11700 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11742  -> dummy :: env1) env)
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
                                          let uu____11779 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11779)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11784 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11784.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11784.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11785 -> lopt  in
                           (log cfg
                              (fun uu____11791  ->
                                 let uu____11792 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11792);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11801 = cfg  in
                               {
                                 steps = (uu___151_11801.steps);
                                 tcenv = (uu___151_11801.tcenv);
                                 debug = (uu___151_11801.debug);
                                 delta_level = (uu___151_11801.delta_level);
                                 primitive_steps =
                                   (uu___151_11801.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11801.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11801.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11812)::uu____11813 ->
                    if (cfg.steps).weak
                    then
                      let uu____11828 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11828
                    else
                      (let uu____11830 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11830 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11872  -> dummy :: env1) env)
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
                                          let uu____11909 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11909)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11914 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11914.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11914.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11915 -> lopt  in
                           (log cfg
                              (fun uu____11921  ->
                                 let uu____11922 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11922);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11931 = cfg  in
                               {
                                 steps = (uu___151_11931.steps);
                                 tcenv = (uu___151_11931.tcenv);
                                 debug = (uu___151_11931.debug);
                                 delta_level = (uu___151_11931.delta_level);
                                 primitive_steps =
                                   (uu___151_11931.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11931.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11931.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (AscribedBy uu____11942)::uu____11943 ->
                    if (cfg.steps).weak
                    then
                      let uu____11956 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11956
                    else
                      (let uu____11958 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11958 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12000  -> dummy :: env1) env)
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
                                          let uu____12037 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12037)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_12042 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_12042.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_12042.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12043 -> lopt  in
                           (log cfg
                              (fun uu____12049  ->
                                 let uu____12050 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12050);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_12059 = cfg  in
                               {
                                 steps = (uu___151_12059.steps);
                                 tcenv = (uu___151_12059.tcenv);
                                 debug = (uu___151_12059.debug);
                                 delta_level = (uu___151_12059.delta_level);
                                 primitive_steps =
                                   (uu___151_12059.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_12059.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_12059.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (RefinedBy uu____12070)::uu____12071 ->
                    if (cfg.steps).weak
                    then
                      let uu____12082 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12082
                    else
                      (let uu____12084 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12084 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12126  -> dummy :: env1) env)
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
                                          let uu____12163 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12163)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_12168 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_12168.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_12168.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12169 -> lopt  in
                           (log cfg
                              (fun uu____12175  ->
                                 let uu____12176 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12176);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_12185 = cfg  in
                               {
                                 steps = (uu___151_12185.steps);
                                 tcenv = (uu___151_12185.tcenv);
                                 debug = (uu___151_12185.debug);
                                 delta_level = (uu___151_12185.delta_level);
                                 primitive_steps =
                                   (uu___151_12185.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_12185.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_12185.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Refining uu____12196)::uu____12197 ->
                    if (cfg.steps).weak
                    then
                      let uu____12206 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12206
                    else
                      (let uu____12208 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12208 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12250  -> dummy :: env1) env)
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
                                          let uu____12287 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12287)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_12292 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_12292.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_12292.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12293 -> lopt  in
                           (log cfg
                              (fun uu____12299  ->
                                 let uu____12300 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12300);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_12309 = cfg  in
                               {
                                 steps = (uu___151_12309.steps);
                                 tcenv = (uu___151_12309.tcenv);
                                 debug = (uu___151_12309.debug);
                                 delta_level = (uu___151_12309.delta_level);
                                 primitive_steps =
                                   (uu___151_12309.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_12309.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_12309.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Branches uu____12320)::uu____12321 ->
                    if (cfg.steps).weak
                    then
                      let uu____12332 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12332
                    else
                      (let uu____12334 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12334 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12376  -> dummy :: env1) env)
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
                                          let uu____12413 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12413)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_12418 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_12418.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_12418.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12419 -> lopt  in
                           (log cfg
                              (fun uu____12425  ->
                                 let uu____12426 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12426);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_12435 = cfg  in
                               {
                                 steps = (uu___151_12435.steps);
                                 tcenv = (uu___151_12435.tcenv);
                                 debug = (uu___151_12435.debug);
                                 delta_level = (uu___151_12435.delta_level);
                                 primitive_steps =
                                   (uu___151_12435.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_12435.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_12435.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____12446 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12446
                    else
                      (let uu____12448 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12448 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12490  -> dummy :: env1) env)
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
                                          let uu____12527 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12527)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_12532 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_12532.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_12532.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12533 -> lopt  in
                           (log cfg
                              (fun uu____12539  ->
                                 let uu____12540 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12540);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_12549 = cfg  in
                               {
                                 steps = (uu___151_12549.steps);
                                 tcenv = (uu___151_12549.tcenv);
                                 debug = (uu___151_12549.debug);
                                 delta_level = (uu___151_12549.delta_level);
                                 primitive_steps =
                                   (uu___151_12549.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_12549.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_12549.normalize_pure_lets)
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
                      (fun uu____12598  ->
                         fun stack1  ->
                           match uu____12598 with
                           | (a,aq) ->
                               let uu____12610 =
                                 let uu____12611 =
                                   let uu____12618 =
                                     let uu____12619 =
                                       let uu____12650 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____12650, false)  in
                                     Clos uu____12619  in
                                   (uu____12618, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____12611  in
                               uu____12610 :: stack1) args)
                  in
               (log cfg
                  (fun uu____12734  ->
                     let uu____12735 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12735);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               let uu____12748 = FStar_Syntax_Subst.open_term_bv x f  in
               (match uu____12748 with
                | (x1,f1) ->
                    norm cfg env
                      ((RefinedBy
                          (x1, (dummy :: env), f1,
                            (t1.FStar_Syntax_Syntax.pos))) :: stack)
                      x1.FStar_Syntax_Syntax.sort)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____12787 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12787
               else
                 (let uu____12789 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12789 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12797 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12821  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12797 c1  in
                      let t2 =
                        let uu____12843 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12843 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,l) ->
               (match stack with
                | (Match uu____12945)::uu____12946 ->
                    (log cfg
                       (fun uu____12957  ->
                          FStar_Util.print_string "+++ Dropping ascription\n");
                     norm cfg env stack t11)
                | (Arg uu____12958)::uu____12959 ->
                    (log cfg
                       (fun uu____12970  ->
                          FStar_Util.print_string "+++ Dropping ascription\n");
                     norm cfg env stack t11)
                | (App
                    (uu____12971,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12972;
                                   FStar_Syntax_Syntax.vars = uu____12973;_},uu____12974,uu____12975))::uu____12976
                    ->
                    (log cfg
                       (fun uu____12985  ->
                          FStar_Util.print_string "+++ Dropping ascription\n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12986)::uu____12987 ->
                    (log cfg
                       (fun uu____12998  ->
                          FStar_Util.print_string "+++ Dropping ascription\n");
                     norm cfg env stack t11)
                | uu____12999 ->
                    (log cfg
                       (fun uu____13002  ->
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
                         let uu____13112 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13112 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___152_13132 = cfg  in
                               let uu____13133 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___152_13132.steps);
                                 tcenv = uu____13133;
                                 debug = (uu___152_13132.debug);
                                 delta_level = (uu___152_13132.delta_level);
                                 primitive_steps =
                                   (uu___152_13132.primitive_steps);
                                 strong = (uu___152_13132.strong);
                                 memoize_lazy = (uu___152_13132.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___152_13132.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____13138 =
                                 let uu____13139 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____13139  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13138
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___153_13142 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___153_13142.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___153_13142.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___153_13142.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___153_13142.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____13143 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13143
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13154,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13155;
                               FStar_Syntax_Syntax.lbunivs = uu____13156;
                               FStar_Syntax_Syntax.lbtyp = uu____13157;
                               FStar_Syntax_Syntax.lbeff = uu____13158;
                               FStar_Syntax_Syntax.lbdef = uu____13159;
                               FStar_Syntax_Syntax.lbattrs = uu____13160;
                               FStar_Syntax_Syntax.lbpos = uu____13161;_}::uu____13162),uu____13163)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____13203 =
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
               if uu____13203
               then
                 let binder =
                   let uu____13205 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13205  in
                 let env1 =
                   let uu____13215 =
                     let uu____13222 =
                       let uu____13223 =
                         let uu____13254 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13254,
                           false)
                          in
                       Clos uu____13223  in
                     ((FStar_Pervasives_Native.Some binder), uu____13222)  in
                   uu____13215 :: env  in
                 (log cfg
                    (fun uu____13347  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____13351  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____13352 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____13352))
                 else
                   (let uu____13354 =
                      let uu____13359 =
                        let uu____13360 =
                          let uu____13361 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____13361
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____13360]  in
                      FStar_Syntax_Subst.open_term uu____13359 body  in
                    match uu____13354 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____13370  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____13378 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____13378  in
                            FStar_Util.Inl
                              (let uu___154_13388 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___154_13388.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___154_13388.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____13391  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___155_13393 = lb  in
                             let uu____13394 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___155_13393.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_13393.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13394;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___155_13393.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___155_13393.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13429  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___156_13452 = cfg  in
                             {
                               steps = (uu___156_13452.steps);
                               tcenv = (uu___156_13452.tcenv);
                               debug = (uu___156_13452.debug);
                               delta_level = (uu___156_13452.delta_level);
                               primitive_steps =
                                 (uu___156_13452.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___156_13452.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13452.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____13455  ->
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
               let uu____13472 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13472 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13508 =
                               let uu___157_13509 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_13509.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_13509.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13508  in
                           let uu____13510 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13510 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13536 =
                                   FStar_List.map (fun uu____13552  -> dummy)
                                     lbs1
                                    in
                                 let uu____13553 =
                                   let uu____13562 =
                                     FStar_List.map
                                       (fun uu____13582  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13562 env  in
                                 FStar_List.append uu____13536 uu____13553
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13606 =
                                       let uu___158_13607 = rc  in
                                       let uu____13608 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___158_13607.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13608;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___158_13607.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13606
                                 | uu____13615 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___159_13619 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___159_13619.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___159_13619.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___159_13619.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___159_13619.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13629 =
                        FStar_List.map (fun uu____13645  -> dummy) lbs2  in
                      FStar_List.append uu____13629 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13653 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13653 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___160_13669 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___160_13669.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___160_13669.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____13696 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13696
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13715 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13791  ->
                        match uu____13791 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___161_13912 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___161_13912.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___161_13912.FStar_Syntax_Syntax.sort)
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
               (match uu____13715 with
                | (rec_env,memos,uu____14125) ->
                    let uu____14178 =
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
                             let uu____14489 =
                               let uu____14496 =
                                 let uu____14497 =
                                   let uu____14528 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14528, false)
                                    in
                                 Clos uu____14497  in
                               (FStar_Pervasives_Native.None, uu____14496)
                                in
                             uu____14489 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14638  ->
                     let uu____14639 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14639);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14661 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14663::uu____14664 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14669) ->
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
                             | uu____14692 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14706 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14706
                              | uu____14717 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14721 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14747 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14765 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____14782 =
                        let uu____14783 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14784 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14783 uu____14784
                         in
                      failwith uu____14782
                    else rebuild cfg env stack t2
                | uu____14786 -> norm cfg env stack t2))

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
                let uu____14796 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____14796  in
              let uu____14797 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14797 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____14810  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____14821  ->
                        let uu____14822 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14823 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____14822 uu____14823);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____14828 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____14828 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____14837))::stack1 ->
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
                      | uu____14892 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14895 ->
                          let uu____14898 =
                            let uu____14899 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14899
                             in
                          failwith uu____14898
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
                  let uu___162_14923 = cfg  in
                  let uu____14924 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____14924;
                    tcenv = (uu___162_14923.tcenv);
                    debug = (uu___162_14923.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___162_14923.primitive_steps);
                    strong = (uu___162_14923.strong);
                    memoize_lazy = (uu___162_14923.memoize_lazy);
                    normalize_pure_lets =
                      (uu___162_14923.normalize_pure_lets)
                  }
                else
                  (let uu___163_14926 = cfg  in
                   {
                     steps =
                       (let uu___164_14929 = cfg.steps  in
                        {
                          beta = (uu___164_14929.beta);
                          iota = (uu___164_14929.iota);
                          zeta = false;
                          weak = (uu___164_14929.weak);
                          hnf = (uu___164_14929.hnf);
                          primops = (uu___164_14929.primops);
                          no_delta_steps = (uu___164_14929.no_delta_steps);
                          unfold_until = (uu___164_14929.unfold_until);
                          unfold_only = (uu___164_14929.unfold_only);
                          unfold_fully = (uu___164_14929.unfold_fully);
                          unfold_attr = (uu___164_14929.unfold_attr);
                          unfold_tac = (uu___164_14929.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___164_14929.pure_subterms_within_computations);
                          simplify = (uu___164_14929.simplify);
                          erase_universes = (uu___164_14929.erase_universes);
                          allow_unbound_universes =
                            (uu___164_14929.allow_unbound_universes);
                          reify_ = (uu___164_14929.reify_);
                          compress_uvars = (uu___164_14929.compress_uvars);
                          no_full_norm = (uu___164_14929.no_full_norm);
                          check_no_uvars = (uu___164_14929.check_no_uvars);
                          unmeta = (uu___164_14929.unmeta);
                          unascribe = (uu___164_14929.unascribe)
                        });
                     tcenv = (uu___163_14926.tcenv);
                     debug = (uu___163_14926.debug);
                     delta_level = (uu___163_14926.delta_level);
                     primitive_steps = (uu___163_14926.primitive_steps);
                     strong = (uu___163_14926.strong);
                     memoize_lazy = (uu___163_14926.memoize_lazy);
                     normalize_pure_lets =
                       (uu___163_14926.normalize_pure_lets)
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
                  (fun uu____14959  ->
                     let uu____14960 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____14961 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14960
                       uu____14961);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____14963 =
                   let uu____14964 = FStar_Syntax_Subst.compress head3  in
                   uu____14964.FStar_Syntax_Syntax.n  in
                 match uu____14963 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____14982 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14982
                        in
                     let uu____14983 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14983 with
                      | (uu____14984,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____14990 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____14998 =
                                   let uu____14999 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____14999.FStar_Syntax_Syntax.n  in
                                 match uu____14998 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15005,uu____15006))
                                     ->
                                     let uu____15015 =
                                       let uu____15016 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____15016.FStar_Syntax_Syntax.n  in
                                     (match uu____15015 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15022,msrc,uu____15024))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15033 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15033
                                      | uu____15034 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15035 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____15036 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____15036 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___165_15041 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___165_15041.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___165_15041.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___165_15041.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___165_15041.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___165_15041.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____15042 = FStar_List.tl stack  in
                                    let uu____15043 =
                                      let uu____15044 =
                                        let uu____15047 =
                                          let uu____15048 =
                                            let uu____15061 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____15061)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15048
                                           in
                                        FStar_Syntax_Syntax.mk uu____15047
                                         in
                                      uu____15044
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____15042 uu____15043
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15077 =
                                      let uu____15078 = is_return body  in
                                      match uu____15078 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15082;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15083;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15088 -> false  in
                                    if uu____15077
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
                                         let uu____15111 =
                                           let uu____15114 =
                                             let uu____15115 =
                                               let uu____15132 =
                                                 let uu____15135 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____15135]  in
                                               (uu____15132, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15115
                                              in
                                           FStar_Syntax_Syntax.mk uu____15114
                                            in
                                         uu____15111
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____15151 =
                                           let uu____15152 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____15152.FStar_Syntax_Syntax.n
                                            in
                                         match uu____15151 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15158::uu____15159::[])
                                             ->
                                             let uu____15166 =
                                               let uu____15169 =
                                                 let uu____15170 =
                                                   let uu____15177 =
                                                     let uu____15180 =
                                                       let uu____15181 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15181
                                                        in
                                                     let uu____15182 =
                                                       let uu____15185 =
                                                         let uu____15186 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15186
                                                          in
                                                       [uu____15185]  in
                                                     uu____15180 ::
                                                       uu____15182
                                                      in
                                                   (bind1, uu____15177)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15170
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15169
                                                in
                                             uu____15166
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15194 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____15200 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____15200
                                         then
                                           let uu____15203 =
                                             let uu____15204 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____15204
                                              in
                                           let uu____15205 =
                                             let uu____15208 =
                                               let uu____15209 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____15209
                                                in
                                             [uu____15208]  in
                                           uu____15203 :: uu____15205
                                         else []  in
                                       let reified =
                                         let uu____15214 =
                                           let uu____15217 =
                                             let uu____15218 =
                                               let uu____15233 =
                                                 let uu____15236 =
                                                   let uu____15239 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____15240 =
                                                     let uu____15243 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____15243]  in
                                                   uu____15239 :: uu____15240
                                                    in
                                                 let uu____15244 =
                                                   let uu____15247 =
                                                     let uu____15250 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____15251 =
                                                       let uu____15254 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____15255 =
                                                         let uu____15258 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____15259 =
                                                           let uu____15262 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____15262]  in
                                                         uu____15258 ::
                                                           uu____15259
                                                          in
                                                       uu____15254 ::
                                                         uu____15255
                                                        in
                                                     uu____15250 ::
                                                       uu____15251
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____15247
                                                    in
                                                 FStar_List.append
                                                   uu____15236 uu____15244
                                                  in
                                               (bind_inst, uu____15233)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15218
                                              in
                                           FStar_Syntax_Syntax.mk uu____15217
                                            in
                                         uu____15214
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____15274  ->
                                            let uu____15275 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____15276 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____15275 uu____15276);
                                       (let uu____15277 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____15277 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____15301 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____15301
                        in
                     let uu____15302 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____15302 with
                      | (uu____15303,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15338 =
                                  let uu____15339 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____15339.FStar_Syntax_Syntax.n  in
                                match uu____15338 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15345) -> t2
                                | uu____15350 -> head4  in
                              let uu____15351 =
                                let uu____15352 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____15352.FStar_Syntax_Syntax.n  in
                              match uu____15351 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15358 -> FStar_Pervasives_Native.None
                               in
                            let uu____15359 = maybe_extract_fv head4  in
                            match uu____15359 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15369 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15369
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____15374 = maybe_extract_fv head5
                                     in
                                  match uu____15374 with
                                  | FStar_Pervasives_Native.Some uu____15379
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15380 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____15385 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____15400 =
                              match uu____15400 with
                              | (e,q) ->
                                  let uu____15407 =
                                    let uu____15408 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15408.FStar_Syntax_Syntax.n  in
                                  (match uu____15407 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____15423 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____15423
                                   | uu____15424 -> false)
                               in
                            let uu____15425 =
                              let uu____15426 =
                                let uu____15433 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____15433 :: args  in
                              FStar_Util.for_some is_arg_impure uu____15426
                               in
                            if uu____15425
                            then
                              let uu____15438 =
                                let uu____15439 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15439
                                 in
                              failwith uu____15438
                            else ());
                           (let uu____15441 = maybe_unfold_action head_app
                               in
                            match uu____15441 with
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
                                   (fun uu____15482  ->
                                      let uu____15483 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____15484 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____15483 uu____15484);
                                 (let uu____15485 = FStar_List.tl stack  in
                                  norm cfg env uu____15485 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15487) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15511 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____15511  in
                     (log cfg
                        (fun uu____15515  ->
                           let uu____15516 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15516);
                      (let uu____15517 = FStar_List.tl stack  in
                       norm cfg env uu____15517 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15638  ->
                               match uu____15638 with
                               | (pat,wopt,tm) ->
                                   let uu____15686 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____15686)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____15718 = FStar_List.tl stack  in
                     norm cfg env uu____15718 tm
                 | uu____15719 -> fallback ())

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
              (fun uu____15733  ->
                 let uu____15734 = FStar_Ident.string_of_lid msrc  in
                 let uu____15735 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15736 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15734
                   uu____15735 uu____15736);
            (let uu____15737 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15737
             then
               let ed =
                 let uu____15739 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15739  in
               let uu____15740 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15740 with
               | (uu____15741,return_repr) ->
                   let return_inst =
                     let uu____15750 =
                       let uu____15751 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15751.FStar_Syntax_Syntax.n  in
                     match uu____15750 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15757::[]) ->
                         let uu____15764 =
                           let uu____15767 =
                             let uu____15768 =
                               let uu____15775 =
                                 let uu____15778 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15778]  in
                               (return_tm, uu____15775)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15768  in
                           FStar_Syntax_Syntax.mk uu____15767  in
                         uu____15764 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15786 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15789 =
                     let uu____15792 =
                       let uu____15793 =
                         let uu____15808 =
                           let uu____15811 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15812 =
                             let uu____15815 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15815]  in
                           uu____15811 :: uu____15812  in
                         (return_inst, uu____15808)  in
                       FStar_Syntax_Syntax.Tm_app uu____15793  in
                     FStar_Syntax_Syntax.mk uu____15792  in
                   uu____15789 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15824 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15824 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15827 =
                      let uu____15828 = FStar_Ident.text_of_lid msrc  in
                      let uu____15829 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15828 uu____15829
                       in
                    failwith uu____15827
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15830;
                      FStar_TypeChecker_Env.mtarget = uu____15831;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15832;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15847 =
                      let uu____15848 = FStar_Ident.text_of_lid msrc  in
                      let uu____15849 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15848 uu____15849
                       in
                    failwith uu____15847
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15850;
                      FStar_TypeChecker_Env.mtarget = uu____15851;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15852;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____15876 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____15877 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____15876 t FStar_Syntax_Syntax.tun uu____15877))

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
                (fun uu____15933  ->
                   match uu____15933 with
                   | (a,imp) ->
                       let uu____15944 = norm cfg env [] a  in
                       (uu____15944, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____15952  ->
             let uu____15953 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____15954 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____15953 uu____15954);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15978 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____15978
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___166_15981 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___166_15981.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___166_15981.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16001 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____16001
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___167_16004 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___167_16004.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___167_16004.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____16037  ->
                      match uu____16037 with
                      | (a,i) ->
                          let uu____16048 = norm cfg env [] a  in
                          (uu____16048, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_16066  ->
                       match uu___90_16066 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16070 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16070
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___168_16078 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___169_16081 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___169_16081.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___168_16078.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___168_16078.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____16084  ->
        match uu____16084 with
        | (x,imp) ->
            let uu____16087 =
              let uu___170_16088 = x  in
              let uu____16089 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___170_16088.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___170_16088.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16089
              }  in
            (uu____16087, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16095 =
          FStar_List.fold_left
            (fun uu____16113  ->
               fun b  ->
                 match uu____16113 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16095 with | (nbs,uu____16153) -> FStar_List.rev nbs

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
            let uu____16169 =
              let uu___171_16170 = rc  in
              let uu____16171 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___171_16170.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16171;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___171_16170.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16169
        | uu____16178 -> lopt

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
            (let uu____16199 = FStar_Syntax_Print.term_to_string tm  in
             let uu____16200 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____16199
               uu____16200)
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
          let uu____16220 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____16220
          then tm1
          else
            (let w t =
               let uu___172_16232 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___172_16232.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___172_16232.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____16241 =
                 let uu____16242 = FStar_Syntax_Util.unmeta t  in
                 uu____16242.FStar_Syntax_Syntax.n  in
               match uu____16241 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____16249 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____16294)::args1,(bv,uu____16297)::bs1) ->
                   let uu____16331 =
                     let uu____16332 = FStar_Syntax_Subst.compress t  in
                     uu____16332.FStar_Syntax_Syntax.n  in
                   (match uu____16331 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16336 -> false)
               | ([],[]) -> true
               | (uu____16357,uu____16358) -> false  in
             let is_applied bs t =
               let uu____16394 = FStar_Syntax_Util.head_and_args' t  in
               match uu____16394 with
               | (hd1,args) ->
                   let uu____16427 =
                     let uu____16428 = FStar_Syntax_Subst.compress hd1  in
                     uu____16428.FStar_Syntax_Syntax.n  in
                   (match uu____16427 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____16434 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____16446 = FStar_Syntax_Util.is_squash t  in
               match uu____16446 with
               | FStar_Pervasives_Native.Some (uu____16457,t') ->
                   is_applied bs t'
               | uu____16469 ->
                   let uu____16478 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____16478 with
                    | FStar_Pervasives_Native.Some (uu____16489,t') ->
                        is_applied bs t'
                    | uu____16501 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____16518 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16518 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____16525)::(q,uu____16527)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____16562 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____16562 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____16567 =
                          let uu____16568 = FStar_Syntax_Subst.compress p  in
                          uu____16568.FStar_Syntax_Syntax.n  in
                        (match uu____16567 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16574 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____16574
                         | uu____16575 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____16578)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____16603 =
                          let uu____16604 = FStar_Syntax_Subst.compress p1
                             in
                          uu____16604.FStar_Syntax_Syntax.n  in
                        (match uu____16603 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____16610 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____16610
                         | uu____16611 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____16615 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____16615 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____16620 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____16620 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16627 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16627
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____16630)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____16655 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____16655 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____16662 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____16662
                              | uu____16663 -> FStar_Pervasives_Native.None)
                         | uu____16666 -> FStar_Pervasives_Native.None)
                    | uu____16669 -> FStar_Pervasives_Native.None)
               | uu____16672 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____16683 =
                 let uu____16684 = FStar_Syntax_Subst.compress phi  in
                 uu____16684.FStar_Syntax_Syntax.n  in
               match uu____16683 with
               | FStar_Syntax_Syntax.Tm_match (uu____16689,br::brs) ->
                   let uu____16756 = br  in
                   (match uu____16756 with
                    | (uu____16773,uu____16774,e) ->
                        let r =
                          let uu____16795 = simp_t e  in
                          match uu____16795 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16801 =
                                FStar_List.for_all
                                  (fun uu____16819  ->
                                     match uu____16819 with
                                     | (uu____16832,uu____16833,e') ->
                                         let uu____16847 = simp_t e'  in
                                         uu____16847 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____16801
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____16855 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____16860 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____16860
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____16881 =
                 match uu____16881 with
                 | (t1,q) ->
                     let uu____16894 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____16894 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____16922 -> (t1, q))
                  in
               let uu____16931 = FStar_Syntax_Util.head_and_args t  in
               match uu____16931 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____16993 =
                 let uu____16994 = FStar_Syntax_Util.unmeta ty  in
                 uu____16994.FStar_Syntax_Syntax.n  in
               match uu____16993 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____16998) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____17003,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____17023 -> false  in
             let simplify1 arg =
               let uu____17046 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____17046, arg)  in
             let uu____17055 = is_quantified_const tm1  in
             match uu____17055 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____17059 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____17059
             | FStar_Pervasives_Native.None  ->
                 let uu____17060 =
                   let uu____17061 = FStar_Syntax_Subst.compress tm1  in
                   uu____17061.FStar_Syntax_Syntax.n  in
                 (match uu____17060 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____17065;
                              FStar_Syntax_Syntax.vars = uu____17066;_},uu____17067);
                         FStar_Syntax_Syntax.pos = uu____17068;
                         FStar_Syntax_Syntax.vars = uu____17069;_},args)
                      ->
                      let uu____17095 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17095
                      then
                        let uu____17096 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17096 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17143)::
                             (uu____17144,(arg,uu____17146))::[] ->
                             maybe_auto_squash arg
                         | (uu____17195,(arg,uu____17197))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17198)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17247)::uu____17248::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17299::(FStar_Pervasives_Native.Some (false
                                         ),uu____17300)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17351 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17365 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17365
                         then
                           let uu____17366 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17366 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17413)::uu____17414::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17465::(FStar_Pervasives_Native.Some (true
                                           ),uu____17466)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____17517)::(uu____17518,(arg,uu____17520))::[]
                               -> maybe_auto_squash arg
                           | (uu____17569,(arg,uu____17571))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____17572)::[]
                               -> maybe_auto_squash arg
                           | uu____17621 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17635 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____17635
                            then
                              let uu____17636 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____17636 with
                              | uu____17683::(FStar_Pervasives_Native.Some
                                              (true ),uu____17684)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____17735)::uu____17736::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____17787)::(uu____17788,(arg,uu____17790))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17839,(p,uu____17841))::(uu____17842,
                                                                (q,uu____17844))::[]
                                  ->
                                  let uu____17891 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____17891
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17893 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17907 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____17907
                               then
                                 let uu____17908 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____17908 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17955)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17956)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18007)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18008)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18059)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18060)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18111)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18112)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18163,(arg,uu____18165))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18166)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18215)::(uu____18216,(arg,uu____18218))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18267,(arg,uu____18269))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____18270)::[]
                                     ->
                                     let uu____18319 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18319
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18320)::(uu____18321,(arg,uu____18323))::[]
                                     ->
                                     let uu____18372 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18372
                                 | (uu____18373,(p,uu____18375))::(uu____18376,
                                                                   (q,uu____18378))::[]
                                     ->
                                     let uu____18425 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18425
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18427 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18441 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18441
                                  then
                                    let uu____18442 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18442 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____18489)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____18520)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18551 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18565 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____18565
                                     then
                                       match args with
                                       | (t,uu____18567)::[] ->
                                           let uu____18584 =
                                             let uu____18585 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18585.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18584 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18588::[],body,uu____18590)
                                                ->
                                                let uu____18617 = simp_t body
                                                   in
                                                (match uu____18617 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18620 -> tm1)
                                            | uu____18623 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18625))::(t,uu____18627)::[]
                                           ->
                                           let uu____18666 =
                                             let uu____18667 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18667.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18666 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18670::[],body,uu____18672)
                                                ->
                                                let uu____18699 = simp_t body
                                                   in
                                                (match uu____18699 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18702 -> tm1)
                                            | uu____18705 -> tm1)
                                       | uu____18706 -> tm1
                                     else
                                       (let uu____18716 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18716
                                        then
                                          match args with
                                          | (t,uu____18718)::[] ->
                                              let uu____18735 =
                                                let uu____18736 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18736.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18735 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18739::[],body,uu____18741)
                                                   ->
                                                   let uu____18768 =
                                                     simp_t body  in
                                                   (match uu____18768 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18771 -> tm1)
                                               | uu____18774 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18776))::(t,uu____18778)::[]
                                              ->
                                              let uu____18817 =
                                                let uu____18818 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18818.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18817 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18821::[],body,uu____18823)
                                                   ->
                                                   let uu____18850 =
                                                     simp_t body  in
                                                   (match uu____18850 with
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
                                                    | uu____18853 -> tm1)
                                               | uu____18856 -> tm1)
                                          | uu____18857 -> tm1
                                        else
                                          (let uu____18867 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18867
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18868;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18869;_},uu____18870)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18887;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18888;_},uu____18889)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18906 -> tm1
                                           else
                                             (let uu____18916 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18916 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18936 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18946;
                         FStar_Syntax_Syntax.vars = uu____18947;_},args)
                      ->
                      let uu____18969 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18969
                      then
                        let uu____18970 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18970 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19017)::
                             (uu____19018,(arg,uu____19020))::[] ->
                             maybe_auto_squash arg
                         | (uu____19069,(arg,uu____19071))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19072)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19121)::uu____19122::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19173::(FStar_Pervasives_Native.Some (false
                                         ),uu____19174)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19225 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19239 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19239
                         then
                           let uu____19240 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19240 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19287)::uu____19288::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19339::(FStar_Pervasives_Native.Some (true
                                           ),uu____19340)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19391)::(uu____19392,(arg,uu____19394))::[]
                               -> maybe_auto_squash arg
                           | (uu____19443,(arg,uu____19445))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19446)::[]
                               -> maybe_auto_squash arg
                           | uu____19495 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19509 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19509
                            then
                              let uu____19510 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19510 with
                              | uu____19557::(FStar_Pervasives_Native.Some
                                              (true ),uu____19558)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19609)::uu____19610::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19661)::(uu____19662,(arg,uu____19664))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19713,(p,uu____19715))::(uu____19716,
                                                                (q,uu____19718))::[]
                                  ->
                                  let uu____19765 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19765
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19767 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19781 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19781
                               then
                                 let uu____19782 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19782 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19829)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19830)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19881)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19882)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19933)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19934)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19985)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19986)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20037,(arg,uu____20039))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20040)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20089)::(uu____20090,(arg,uu____20092))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20141,(arg,uu____20143))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20144)::[]
                                     ->
                                     let uu____20193 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20193
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20194)::(uu____20195,(arg,uu____20197))::[]
                                     ->
                                     let uu____20246 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20246
                                 | (uu____20247,(p,uu____20249))::(uu____20250,
                                                                   (q,uu____20252))::[]
                                     ->
                                     let uu____20299 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20299
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20301 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20315 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20315
                                  then
                                    let uu____20316 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20316 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20363)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20394)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20425 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20439 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20439
                                     then
                                       match args with
                                       | (t,uu____20441)::[] ->
                                           let uu____20458 =
                                             let uu____20459 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20459.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20458 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20462::[],body,uu____20464)
                                                ->
                                                let uu____20491 = simp_t body
                                                   in
                                                (match uu____20491 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20494 -> tm1)
                                            | uu____20497 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20499))::(t,uu____20501)::[]
                                           ->
                                           let uu____20540 =
                                             let uu____20541 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20541.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20540 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20544::[],body,uu____20546)
                                                ->
                                                let uu____20573 = simp_t body
                                                   in
                                                (match uu____20573 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20576 -> tm1)
                                            | uu____20579 -> tm1)
                                       | uu____20580 -> tm1
                                     else
                                       (let uu____20590 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20590
                                        then
                                          match args with
                                          | (t,uu____20592)::[] ->
                                              let uu____20609 =
                                                let uu____20610 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20610.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20609 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20613::[],body,uu____20615)
                                                   ->
                                                   let uu____20642 =
                                                     simp_t body  in
                                                   (match uu____20642 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20645 -> tm1)
                                               | uu____20648 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20650))::(t,uu____20652)::[]
                                              ->
                                              let uu____20691 =
                                                let uu____20692 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20692.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20691 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20695::[],body,uu____20697)
                                                   ->
                                                   let uu____20724 =
                                                     simp_t body  in
                                                   (match uu____20724 with
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
                                                    | uu____20727 -> tm1)
                                               | uu____20730 -> tm1)
                                          | uu____20731 -> tm1
                                        else
                                          (let uu____20741 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20741
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20742;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20743;_},uu____20744)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20761;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20762;_},uu____20763)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20780 -> tm1
                                           else
                                             (let uu____20790 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20790 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20810 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20825 = simp_t t  in
                      (match uu____20825 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20828 ->
                      let uu____20851 = is_const_match tm1  in
                      (match uu____20851 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20854 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____20865  ->
               let uu____20866 = FStar_Syntax_Print.tag_of_term t  in
               let uu____20867 = FStar_Syntax_Print.term_to_string t  in
               let uu____20868 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____20875 =
                 let uu____20876 =
                   let uu____20879 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____20879
                    in
                 stack_to_string uu____20876  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____20866 uu____20867 uu____20868 uu____20875);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____20910 =
                     let uu____20911 =
                       let uu____20912 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20912  in
                     FStar_Util.string_of_int uu____20911  in
                   let uu____20917 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20918 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20910 uu____20917 uu____20918)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____20972  ->
                     let uu____20973 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20973);
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
               let uu____21009 =
                 let uu___173_21010 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___173_21010.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___173_21010.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____21009
           | (Arg (Univ uu____21011,uu____21012,uu____21013))::uu____21014 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____21017,uu____21018))::uu____21019 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____21034,uu____21035),aq,r))::stack1
               when
               let uu____21085 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____21085 ->
               let t2 =
                 let uu____21089 =
                   let uu____21090 =
                     let uu____21091 = closure_as_term cfg env_arg tm  in
                     (uu____21091, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____21090  in
                 uu____21089 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____21097),aq,r))::stack1 ->
               (log cfg
                  (fun uu____21150  ->
                     let uu____21151 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____21151);
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
                  (let uu____21161 = FStar_ST.op_Bang m  in
                   match uu____21161 with
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
                   | FStar_Pervasives_Native.Some (uu____21298,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21345 =
                 log cfg
                   (fun uu____21349  ->
                      let uu____21350 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21350);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21354 =
                 let uu____21355 = FStar_Syntax_Subst.compress t1  in
                 uu____21355.FStar_Syntax_Syntax.n  in
               (match uu____21354 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21382 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21382  in
                    (log cfg
                       (fun uu____21386  ->
                          let uu____21387 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21387);
                     (let uu____21388 = FStar_List.tl stack  in
                      norm cfg env1 uu____21388 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21389);
                       FStar_Syntax_Syntax.pos = uu____21390;
                       FStar_Syntax_Syntax.vars = uu____21391;_},(e,uu____21393)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21422 when
                    (cfg.steps).primops ->
                    let uu____21437 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21437 with
                     | (hd1,args) ->
                         let uu____21474 =
                           let uu____21475 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21475.FStar_Syntax_Syntax.n  in
                         (match uu____21474 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21479 = find_prim_step cfg fv  in
                              (match uu____21479 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____21482; arity = uu____21483;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____21485;
                                     requires_binder_substitution =
                                       uu____21486;
                                     interpretation = uu____21487;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21500 -> fallback " (3)" ())
                          | uu____21503 -> fallback " (4)" ()))
                | uu____21504 -> fallback " (2)" ())
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
                     let uu____21583 = norm cfg env' [] t2  in
                     FStar_All.pipe_left (fun _0_44  -> FStar_Util.Inl _0_44)
                       uu____21583
                 | FStar_Util.Inr c ->
                     let uu____21595 = norm_comp cfg env' c  in
                     FStar_All.pipe_left (fun _0_45  -> FStar_Util.Inr _0_45)
                       uu____21595
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
                 let uu___174_21634 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___174_21634.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___174_21634.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t1
                 }  in
               if (cfg.steps).weak
               then
                 let t2 =
                   let uu___175_21638 =
                     let uu____21641 = closure_as_term cfg env' f  in
                     FStar_Syntax_Util.refine x1 uu____21641  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___175_21638.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = r;
                     FStar_Syntax_Syntax.vars =
                       (uu___175_21638.FStar_Syntax_Syntax.vars)
                   }  in
                 rebuild cfg env' stack1 t2
               else norm cfg env' ((Refining (x1, r, env)) :: stack1) f
           | (Refining (x,r,env'))::stack1 ->
               let t2 =
                 let uu___176_21652 = FStar_Syntax_Util.refine x t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___176_21652.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___176_21652.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env' stack1 t2
           | (Branches (env1,brs,[],r))::stack1 ->
               let uu____21679 =
                 mk (FStar_Syntax_Syntax.Tm_match (t1, (FStar_List.rev brs)))
                   r
                  in
               rebuild cfg env1 stack1 uu____21679
           | (Branches (env1,brs_n,br::brs,r))::stack1 ->
               let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
               let cfg_exclude_iota_zeta =
                 let new_delta =
                   FStar_All.pipe_right cfg.delta_level
                     (FStar_List.filter
                        (fun uu___91_21752  ->
                           match uu___91_21752 with
                           | FStar_TypeChecker_Env.Inlining  -> true
                           | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                               true
                           | uu____21753 -> false))
                    in
                 let uu___177_21754 = cfg  in
                 {
                   steps =
                     (let uu___178_21757 = cfg.steps  in
                      {
                        beta = (uu___178_21757.beta);
                        iota = (uu___178_21757.iota);
                        zeta = false;
                        weak = (uu___178_21757.weak);
                        hnf = (uu___178_21757.hnf);
                        primops = (uu___178_21757.primops);
                        no_delta_steps = (uu___178_21757.no_delta_steps);
                        unfold_until = (uu___178_21757.unfold_until);
                        unfold_only = (uu___178_21757.unfold_only);
                        unfold_fully = (uu___178_21757.unfold_fully);
                        unfold_attr = (uu___178_21757.unfold_attr);
                        unfold_tac = (uu___178_21757.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___178_21757.pure_subterms_within_computations);
                        simplify = (uu___178_21757.simplify);
                        erase_universes = (uu___178_21757.erase_universes);
                        allow_unbound_universes =
                          (uu___178_21757.allow_unbound_universes);
                        reify_ = (uu___178_21757.reify_);
                        compress_uvars = (uu___178_21757.compress_uvars);
                        no_full_norm = (uu___178_21757.no_full_norm);
                        check_no_uvars = (uu___178_21757.check_no_uvars);
                        unmeta = (uu___178_21757.unmeta);
                        unascribe = (uu___178_21757.unascribe)
                      });
                   tcenv = (uu___177_21754.tcenv);
                   debug = (uu___177_21754.debug);
                   delta_level = new_delta;
                   primitive_steps = (uu___177_21754.primitive_steps);
                   strong = true;
                   memoize_lazy = (uu___177_21754.memoize_lazy);
                   normalize_pure_lets = (uu___177_21754.normalize_pure_lets)
                 }  in
               let norm_or_whnf env2 t2 =
                 if whnf
                 then closure_as_term cfg_exclude_iota_zeta env2 t2
                 else norm cfg_exclude_iota_zeta env2 [] t2  in
               let rec norm_pat env2 p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant uu____21789 -> (p, env2)
                 | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                     let uu____21810 =
                       FStar_All.pipe_right pats
                         (FStar_List.fold_left
                            (fun uu____21870  ->
                               fun uu____21871  ->
                                 match (uu____21870, uu____21871) with
                                 | ((pats1,env3),(p1,b)) ->
                                     let uu____21962 = norm_pat env3 p1  in
                                     (match uu____21962 with
                                      | (p2,env4) ->
                                          (((p2, b) :: pats1), env4)))
                            ([], env2))
                        in
                     (match uu____21810 with
                      | (pats1,env3) ->
                          ((let uu___179_22044 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_cons
                                   (fv, (FStar_List.rev pats1)));
                              FStar_Syntax_Syntax.p =
                                (uu___179_22044.FStar_Syntax_Syntax.p)
                            }), env3))
                 | FStar_Syntax_Syntax.Pat_var x ->
                     let x1 =
                       let uu___180_22063 = x  in
                       let uu____22064 =
                         norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___180_22063.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___180_22063.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____22064
                       }  in
                     ((let uu___181_22078 = p  in
                       {
                         FStar_Syntax_Syntax.v =
                           (FStar_Syntax_Syntax.Pat_var x1);
                         FStar_Syntax_Syntax.p =
                           (uu___181_22078.FStar_Syntax_Syntax.p)
                       }), (dummy :: env2))
                 | FStar_Syntax_Syntax.Pat_wild x ->
                     let x1 =
                       let uu___182_22089 = x  in
                       let uu____22090 =
                         norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___182_22089.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___182_22089.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____22090
                       }  in
                     ((let uu___183_22104 = p  in
                       {
                         FStar_Syntax_Syntax.v =
                           (FStar_Syntax_Syntax.Pat_wild x1);
                         FStar_Syntax_Syntax.p =
                           (uu___183_22104.FStar_Syntax_Syntax.p)
                       }), (dummy :: env2))
                 | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                     let x1 =
                       let uu___184_22120 = x  in
                       let uu____22121 =
                         norm_or_whnf env2 x.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___184_22120.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___184_22120.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____22121
                       }  in
                     let t3 = norm_or_whnf env2 t2  in
                     ((let uu___185_22128 = p  in
                       {
                         FStar_Syntax_Syntax.v =
                           (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                         FStar_Syntax_Syntax.p =
                           (uu___185_22128.FStar_Syntax_Syntax.p)
                       }), env2)
                  in
               let br1 =
                 match env1 with
                 | [] when whnf -> br
                 | uu____22154 ->
                     let uu____22155 = FStar_Syntax_Subst.open_branch br  in
                     (match uu____22155 with
                      | (p,wopt,e) ->
                          let uu____22183 = norm_pat env1 p  in
                          (match uu____22183 with
                           | (p1,env2) ->
                               let wopt1 =
                                 match wopt with
                                 | FStar_Pervasives_Native.None  ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some w ->
                                     let uu____22216 = norm_or_whnf env2 w
                                        in
                                     FStar_Pervasives_Native.Some uu____22216
                                  in
                               let e1 = norm_or_whnf env2 e  in
                               FStar_Syntax_Util.branch (p1, wopt1, e1)))
                  in
               rebuild cfg env1 ((Branches (env1, (br1 :: brs_n), brs, r)) ::
                 stack1) t1
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____22259  ->
                     let uu____22260 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____22260);
                (let scrutinee = t1  in
                 let fallback uu____22265 =
                   rebuild cfg env1 ((Branches (env1, [], branches, r)) ::
                     stack1) t1
                    in
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
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> fallback ()
                   | (p1,wopt,b)::rest ->
                       let uu____22460 = matches_pat scrutinee1 p1  in
                       (match uu____22460 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> fallback ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____22500  ->
                                  let uu____22501 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22502 =
                                    let uu____22503 =
                                      FStar_List.map
                                        (fun uu____22513  ->
                                           match uu____22513 with
                                           | (uu____22518,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22503
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22501 uu____22502);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22549  ->
                                       match uu____22549 with
                                       | (bv,t2) ->
                                           let uu____22572 =
                                             let uu____22579 =
                                               let uu____22582 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22582
                                                in
                                             let uu____22583 =
                                               let uu____22584 =
                                                 let uu____22615 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22615, false)
                                                  in
                                               Clos uu____22584  in
                                             (uu____22579, uu____22583)  in
                                           uu____22572 :: env2) env1 s
                                 in
                              let uu____22732 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____22732)))
                    in
                 if (cfg.steps).iota
                 then matches scrutinee branches
                 else fallback ())))

let (plugins :
  (primitive_step -> Prims.unit,Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____22755 =
      let uu____22758 = FStar_ST.op_Bang plugins  in p :: uu____22758  in
    FStar_ST.op_Colon_Equals plugins uu____22755  in
  let retrieve uu____22856 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____22921  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_22954  ->
                  match uu___92_22954 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____22958 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____22964 -> d  in
        let uu____22967 = to_fsteps s  in
        let uu____22968 =
          let uu____22969 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____22970 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____22971 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____22972 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____22973 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____22969;
            primop = uu____22970;
            b380 = uu____22971;
            norm_delayed = uu____22972;
            print_normalized = uu____22973
          }  in
        let uu____22974 =
          let uu____22977 =
            let uu____22980 = retrieve_plugins ()  in
            FStar_List.append uu____22980 psteps  in
          add_steps built_in_primitive_steps uu____22977  in
        let uu____22983 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____22985 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____22985)
           in
        {
          steps = uu____22967;
          tcenv = e;
          debug = uu____22968;
          delta_level = d1;
          primitive_steps = uu____22974;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____22983
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
      fun t  -> let uu____23043 = config s e  in norm_comp uu____23043 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23056 = config [] env  in norm_universe uu____23056 [] u
  
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
        let uu____23074 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23074  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23081 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___186_23100 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___186_23100.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___186_23100.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23107 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23107
          then
            let ct1 =
              let uu____23109 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23109 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23116 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23116
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___187_23120 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___187_23120.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___187_23120.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___187_23120.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___188_23122 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___188_23122.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___188_23122.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___188_23122.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___188_23122.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___189_23123 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___189_23123.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___189_23123.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23125 -> c
  
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
        let uu____23137 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23137  in
      let uu____23144 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23144
      then
        let uu____23145 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23145 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23151  ->
                 let uu____23152 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23152)
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
            ((let uu____23169 =
                let uu____23174 =
                  let uu____23175 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23175
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23174)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23169);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____23186 = config [AllowUnboundUniverses] env  in
          norm_comp uu____23186 [] c
        with
        | e ->
            ((let uu____23199 =
                let uu____23204 =
                  let uu____23205 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23205
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23204)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23199);
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
                   let uu____23242 =
                     let uu____23243 =
                       let uu____23250 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____23250)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23243  in
                   mk uu____23242 t01.FStar_Syntax_Syntax.pos
               | uu____23255 -> t2)
          | uu____23256 -> t2  in
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
        let uu____23296 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23296 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23325 ->
                 let uu____23332 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23332 with
                  | (actuals,uu____23342,uu____23343) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23357 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23357 with
                         | (binders,args) ->
                             let uu____23374 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23374
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
      | uu____23382 ->
          let uu____23383 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23383 with
           | (head1,args) ->
               let uu____23420 =
                 let uu____23421 = FStar_Syntax_Subst.compress head1  in
                 uu____23421.FStar_Syntax_Syntax.n  in
               (match uu____23420 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____23424,thead) ->
                    let uu____23450 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____23450 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23492 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___194_23500 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___194_23500.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___194_23500.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___194_23500.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___194_23500.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___194_23500.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___194_23500.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___194_23500.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___194_23500.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___194_23500.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___194_23500.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___194_23500.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___194_23500.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___194_23500.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___194_23500.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___194_23500.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___194_23500.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___194_23500.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___194_23500.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___194_23500.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___194_23500.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___194_23500.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___194_23500.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___194_23500.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___194_23500.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___194_23500.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___194_23500.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___194_23500.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___194_23500.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___194_23500.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___194_23500.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___194_23500.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___194_23500.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___194_23500.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____23492 with
                            | (uu____23501,ty,uu____23503) ->
                                eta_expand_with_type env t ty))
                | uu____23504 ->
                    let uu____23505 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___195_23513 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___195_23513.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___195_23513.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___195_23513.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___195_23513.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___195_23513.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___195_23513.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___195_23513.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___195_23513.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___195_23513.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___195_23513.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___195_23513.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___195_23513.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___195_23513.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___195_23513.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___195_23513.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___195_23513.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___195_23513.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___195_23513.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___195_23513.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___195_23513.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___195_23513.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___195_23513.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___195_23513.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___195_23513.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___195_23513.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___195_23513.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___195_23513.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___195_23513.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___195_23513.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___195_23513.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___195_23513.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___195_23513.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___195_23513.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____23505 with
                     | (uu____23514,ty,uu____23516) ->
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
      let uu___196_23573 = x  in
      let uu____23574 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___196_23573.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___196_23573.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23574
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23577 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23602 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23603 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23604 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23605 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23612 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23613 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23614 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___197_23642 = rc  in
          let uu____23643 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23650 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___197_23642.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23643;
            FStar_Syntax_Syntax.residual_flags = uu____23650
          }  in
        let uu____23653 =
          let uu____23654 =
            let uu____23671 = elim_delayed_subst_binders bs  in
            let uu____23678 = elim_delayed_subst_term t2  in
            let uu____23679 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23671, uu____23678, uu____23679)  in
          FStar_Syntax_Syntax.Tm_abs uu____23654  in
        mk1 uu____23653
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23708 =
          let uu____23709 =
            let uu____23722 = elim_delayed_subst_binders bs  in
            let uu____23729 = elim_delayed_subst_comp c  in
            (uu____23722, uu____23729)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23709  in
        mk1 uu____23708
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____23742 =
          let uu____23743 =
            let uu____23750 = elim_bv bv  in
            let uu____23751 = elim_delayed_subst_term phi  in
            (uu____23750, uu____23751)  in
          FStar_Syntax_Syntax.Tm_refine uu____23743  in
        mk1 uu____23742
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____23774 =
          let uu____23775 =
            let uu____23790 = elim_delayed_subst_term t2  in
            let uu____23791 = elim_delayed_subst_args args  in
            (uu____23790, uu____23791)  in
          FStar_Syntax_Syntax.Tm_app uu____23775  in
        mk1 uu____23774
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___198_23855 = p  in
              let uu____23856 =
                let uu____23857 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____23857  in
              {
                FStar_Syntax_Syntax.v = uu____23856;
                FStar_Syntax_Syntax.p =
                  (uu___198_23855.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___199_23859 = p  in
              let uu____23860 =
                let uu____23861 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____23861  in
              {
                FStar_Syntax_Syntax.v = uu____23860;
                FStar_Syntax_Syntax.p =
                  (uu___199_23859.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___200_23868 = p  in
              let uu____23869 =
                let uu____23870 =
                  let uu____23877 = elim_bv x  in
                  let uu____23878 = elim_delayed_subst_term t0  in
                  (uu____23877, uu____23878)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____23870  in
              {
                FStar_Syntax_Syntax.v = uu____23869;
                FStar_Syntax_Syntax.p =
                  (uu___200_23868.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___201_23897 = p  in
              let uu____23898 =
                let uu____23899 =
                  let uu____23912 =
                    FStar_List.map
                      (fun uu____23935  ->
                         match uu____23935 with
                         | (x,b) ->
                             let uu____23948 = elim_pat x  in
                             (uu____23948, b)) pats
                     in
                  (fv, uu____23912)  in
                FStar_Syntax_Syntax.Pat_cons uu____23899  in
              {
                FStar_Syntax_Syntax.v = uu____23898;
                FStar_Syntax_Syntax.p =
                  (uu___201_23897.FStar_Syntax_Syntax.p)
              }
          | uu____23961 -> p  in
        let elim_branch uu____23983 =
          match uu____23983 with
          | (pat,wopt,t3) ->
              let uu____24009 = elim_pat pat  in
              let uu____24012 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24015 = elim_delayed_subst_term t3  in
              (uu____24009, uu____24012, uu____24015)
           in
        let uu____24020 =
          let uu____24021 =
            let uu____24044 = elim_delayed_subst_term t2  in
            let uu____24045 = FStar_List.map elim_branch branches  in
            (uu____24044, uu____24045)  in
          FStar_Syntax_Syntax.Tm_match uu____24021  in
        mk1 uu____24020
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24154 =
          match uu____24154 with
          | (tc,topt) ->
              let uu____24189 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24199 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24199
                | FStar_Util.Inr c ->
                    let uu____24201 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24201
                 in
              let uu____24202 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24189, uu____24202)
           in
        let uu____24211 =
          let uu____24212 =
            let uu____24239 = elim_delayed_subst_term t2  in
            let uu____24240 = elim_ascription a  in
            (uu____24239, uu____24240, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24212  in
        mk1 uu____24211
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___202_24285 = lb  in
          let uu____24286 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24289 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___202_24285.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___202_24285.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24286;
            FStar_Syntax_Syntax.lbeff =
              (uu___202_24285.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24289;
            FStar_Syntax_Syntax.lbattrs =
              (uu___202_24285.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___202_24285.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24292 =
          let uu____24293 =
            let uu____24306 =
              let uu____24313 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24313)  in
            let uu____24322 = elim_delayed_subst_term t2  in
            (uu____24306, uu____24322)  in
          FStar_Syntax_Syntax.Tm_let uu____24293  in
        mk1 uu____24292
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____24355 =
          let uu____24356 =
            let uu____24373 = elim_delayed_subst_term t2  in
            (uv, uu____24373)  in
          FStar_Syntax_Syntax.Tm_uvar uu____24356  in
        mk1 uu____24355
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24391 =
          let uu____24392 =
            let uu____24399 = elim_delayed_subst_term tm  in
            (uu____24399, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24392  in
        mk1 uu____24391
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24406 =
          let uu____24407 =
            let uu____24414 = elim_delayed_subst_term t2  in
            let uu____24415 = elim_delayed_subst_meta md  in
            (uu____24414, uu____24415)  in
          FStar_Syntax_Syntax.Tm_meta uu____24407  in
        mk1 uu____24406

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_24422  ->
         match uu___93_24422 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24426 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24426
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
        let uu____24447 =
          let uu____24448 =
            let uu____24457 = elim_delayed_subst_term t  in
            (uu____24457, uopt)  in
          FStar_Syntax_Syntax.Total uu____24448  in
        mk1 uu____24447
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24470 =
          let uu____24471 =
            let uu____24480 = elim_delayed_subst_term t  in
            (uu____24480, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24471  in
        mk1 uu____24470
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___203_24485 = ct  in
          let uu____24486 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24489 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24498 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___203_24485.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___203_24485.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24486;
            FStar_Syntax_Syntax.effect_args = uu____24489;
            FStar_Syntax_Syntax.flags = uu____24498
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_24501  ->
    match uu___94_24501 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24513 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24513
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24546 =
          let uu____24553 = elim_delayed_subst_term t  in (m, uu____24553)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24546
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24561 =
          let uu____24570 = elim_delayed_subst_term t  in
          (m1, m2, uu____24570)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24561
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____24593  ->
         match uu____24593 with
         | (t,q) ->
             let uu____24604 = elim_delayed_subst_term t  in (uu____24604, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____24624  ->
         match uu____24624 with
         | (x,q) ->
             let uu____24635 =
               let uu___204_24636 = x  in
               let uu____24637 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___204_24636.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___204_24636.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24637
               }  in
             (uu____24635, q)) bs

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
            | (uu____24713,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____24719,FStar_Util.Inl t) ->
                let uu____24725 =
                  let uu____24728 =
                    let uu____24729 =
                      let uu____24742 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____24742)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____24729  in
                  FStar_Syntax_Syntax.mk uu____24728  in
                uu____24725 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____24746 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____24746 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____24774 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____24829 ->
                    let uu____24830 =
                      let uu____24839 =
                        let uu____24840 = FStar_Syntax_Subst.compress t4  in
                        uu____24840.FStar_Syntax_Syntax.n  in
                      (uu____24839, tc)  in
                    (match uu____24830 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____24865) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____24902) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____24941,FStar_Util.Inl uu____24942) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____24965 -> failwith "Impossible")
                 in
              (match uu____24774 with
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
          let uu____25070 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25070 with
          | (univ_names1,binders1,tc) ->
              let uu____25128 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25128)
  
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
          let uu____25163 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25163 with
          | (univ_names1,binders1,tc) ->
              let uu____25223 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25223)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25256 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25256 with
           | (univ_names1,binders1,typ1) ->
               let uu___205_25284 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_25284.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_25284.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_25284.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_25284.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___206_25305 = s  in
          let uu____25306 =
            let uu____25307 =
              let uu____25316 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25316, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25307  in
          {
            FStar_Syntax_Syntax.sigel = uu____25306;
            FStar_Syntax_Syntax.sigrng =
              (uu___206_25305.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___206_25305.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___206_25305.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___206_25305.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25333 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25333 with
           | (univ_names1,uu____25351,typ1) ->
               let uu___207_25365 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_25365.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_25365.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_25365.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_25365.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25371 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25371 with
           | (univ_names1,uu____25389,typ1) ->
               let uu___208_25403 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___208_25403.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___208_25403.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___208_25403.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___208_25403.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____25437 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____25437 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____25460 =
                            let uu____25461 =
                              let uu____25462 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____25462  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____25461
                             in
                          elim_delayed_subst_term uu____25460  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___209_25465 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___209_25465.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___209_25465.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___209_25465.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___209_25465.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___210_25466 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___210_25466.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_25466.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_25466.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___210_25466.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___211_25478 = s  in
          let uu____25479 =
            let uu____25480 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____25480  in
          {
            FStar_Syntax_Syntax.sigel = uu____25479;
            FStar_Syntax_Syntax.sigrng =
              (uu___211_25478.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___211_25478.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___211_25478.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___211_25478.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____25484 = elim_uvars_aux_t env us [] t  in
          (match uu____25484 with
           | (us1,uu____25502,t1) ->
               let uu___212_25516 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___212_25516.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___212_25516.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___212_25516.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___212_25516.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____25517 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____25519 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____25519 with
           | (univs1,binders,signature) ->
               let uu____25547 =
                 let uu____25556 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____25556 with
                 | (univs_opening,univs2) ->
                     let uu____25583 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____25583)
                  in
               (match uu____25547 with
                | (univs_opening,univs_closing) ->
                    let uu____25600 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____25606 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____25607 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____25606, uu____25607)  in
                    (match uu____25600 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____25629 =
                           match uu____25629 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____25647 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____25647 with
                                | (us1,t1) ->
                                    let uu____25658 =
                                      let uu____25663 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____25670 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____25663, uu____25670)  in
                                    (match uu____25658 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____25683 =
                                           let uu____25688 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____25697 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____25688, uu____25697)  in
                                         (match uu____25683 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____25713 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____25713
                                                 in
                                              let uu____25714 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____25714 with
                                               | (uu____25735,uu____25736,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____25751 =
                                                       let uu____25752 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____25752
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____25751
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____25757 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____25757 with
                           | (uu____25770,uu____25771,t1) -> t1  in
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
                             | uu____25831 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____25848 =
                               let uu____25849 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____25849.FStar_Syntax_Syntax.n  in
                             match uu____25848 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____25908 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____25937 =
                               let uu____25938 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____25938.FStar_Syntax_Syntax.n  in
                             match uu____25937 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____25959) ->
                                 let uu____25980 = destruct_action_body body
                                    in
                                 (match uu____25980 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____26025 ->
                                 let uu____26026 = destruct_action_body t  in
                                 (match uu____26026 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____26075 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____26075 with
                           | (action_univs,t) ->
                               let uu____26084 = destruct_action_typ_templ t
                                  in
                               (match uu____26084 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___213_26125 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___213_26125.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___213_26125.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___214_26127 = ed  in
                           let uu____26128 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26129 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26130 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26131 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26132 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26133 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26134 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26135 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26136 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26137 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26138 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26139 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26140 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26141 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___214_26127.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___214_26127.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26128;
                             FStar_Syntax_Syntax.bind_wp = uu____26129;
                             FStar_Syntax_Syntax.if_then_else = uu____26130;
                             FStar_Syntax_Syntax.ite_wp = uu____26131;
                             FStar_Syntax_Syntax.stronger = uu____26132;
                             FStar_Syntax_Syntax.close_wp = uu____26133;
                             FStar_Syntax_Syntax.assert_p = uu____26134;
                             FStar_Syntax_Syntax.assume_p = uu____26135;
                             FStar_Syntax_Syntax.null_wp = uu____26136;
                             FStar_Syntax_Syntax.trivial = uu____26137;
                             FStar_Syntax_Syntax.repr = uu____26138;
                             FStar_Syntax_Syntax.return_repr = uu____26139;
                             FStar_Syntax_Syntax.bind_repr = uu____26140;
                             FStar_Syntax_Syntax.actions = uu____26141;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___214_26127.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___215_26144 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___215_26144.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___215_26144.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___215_26144.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___215_26144.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_26161 =
            match uu___95_26161 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26188 = elim_uvars_aux_t env us [] t  in
                (match uu____26188 with
                 | (us1,uu____26212,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___216_26231 = sub_eff  in
            let uu____26232 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____26235 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___216_26231.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___216_26231.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26232;
              FStar_Syntax_Syntax.lift = uu____26235
            }  in
          let uu___217_26238 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___217_26238.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___217_26238.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___217_26238.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___217_26238.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____26248 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____26248 with
           | (univ_names1,binders1,comp1) ->
               let uu___218_26282 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_26282.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_26282.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_26282.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_26282.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____26293 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____26294 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  