open Prims
type decl =
  | DGlobal of
  (flag Prims.list,(Prims.string Prims.list,Prims.string)
                     FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
  FStar_Pervasives_Native.tuple5 
  | DFunction of
  (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,(Prims.string
                                                                    Prims.list,
                                                                    Prims.string)
                                                                    FStar_Pervasives_Native.tuple2,
  binder Prims.list,expr) FStar_Pervasives_Native.tuple7 
  | DTypeAlias of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4 
  | DTypeFlat of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list,Prims.int,(Prims.string,(typ,Prims.bool)
                                            FStar_Pervasives_Native.tuple2)
                              FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple4 
  | DExternal of
  (cc FStar_Pervasives_Native.option,flag Prims.list,(Prims.string Prims.list,
                                                       Prims.string)
                                                       FStar_Pervasives_Native.tuple2,
  typ) FStar_Pervasives_Native.tuple4 
  | DTypeVariant of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list,Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                                          FStar_Pervasives_Native.tuple2)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list)
                              FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple4 [@@deriving show]
and cc =
  | StdCall 
  | CDecl 
  | FastCall [@@deriving show]
and flag =
  | Private 
  | WipeBody 
  | CInline 
  | Substitute 
  | GCType 
  | Comment of Prims.string 
  | MustDisappear 
  | Const of Prims.string 
  | Prologue of Prims.string 
  | Epilogue of Prims.string [@@deriving show]
and lifetime =
  | Eternal 
  | Stack 
  | ManuallyManaged [@@deriving show]
and expr =
  | EBound of Prims.int 
  | EQualified of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2 
  | EConstant of (width,Prims.string) FStar_Pervasives_Native.tuple2 
  | EUnit 
  | EApp of (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 
  | ETypApp of (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 
  | ELet of (binder,expr,expr) FStar_Pervasives_Native.tuple3 
  | EIfThenElse of (expr,expr,expr) FStar_Pervasives_Native.tuple3 
  | ESequence of expr Prims.list 
  | EAssign of (expr,expr) FStar_Pervasives_Native.tuple2 
  | EBufCreate of (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 
  | EBufRead of (expr,expr) FStar_Pervasives_Native.tuple2 
  | EBufWrite of (expr,expr,expr) FStar_Pervasives_Native.tuple3 
  | EBufSub of (expr,expr) FStar_Pervasives_Native.tuple2 
  | EBufBlit of (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 
  | EMatch of (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | EOp of (op,width) FStar_Pervasives_Native.tuple2 
  | ECast of (expr,typ) FStar_Pervasives_Native.tuple2 
  | EPushFrame 
  | EPopFrame 
  | EBool of Prims.bool 
  | EAny 
  | EAbort 
  | EReturn of expr 
  | EFlat of
  (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | EField of (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 
  | EWhile of (expr,expr) FStar_Pervasives_Native.tuple2 
  | EBufCreateL of (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2
  
  | ETuple of expr Prims.list 
  | ECons of (typ,Prims.string,expr Prims.list)
  FStar_Pervasives_Native.tuple3 
  | EBufFill of (expr,expr,expr) FStar_Pervasives_Native.tuple3 
  | EString of Prims.string 
  | EFun of (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 
  | EAbortS of Prims.string 
  | EBufFree of expr [@@deriving show]
and op =
  | Add 
  | AddW 
  | Sub 
  | SubW 
  | Div 
  | DivW 
  | Mult 
  | MultW 
  | Mod 
  | BOr 
  | BAnd 
  | BXor 
  | BShiftL 
  | BShiftR 
  | BNot 
  | Eq 
  | Neq 
  | Lt 
  | Lte 
  | Gt 
  | Gte 
  | And 
  | Or 
  | Xor 
  | Not [@@deriving show]
and pattern =
  | PUnit 
  | PBool of Prims.bool 
  | PVar of binder 
  | PCons of (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  
  | PTuple of pattern Prims.list 
  | PRecord of (Prims.string,pattern) FStar_Pervasives_Native.tuple2
  Prims.list 
  | PConstant of (width,Prims.string) FStar_Pervasives_Native.tuple2 
[@@deriving show]
and width =
  | UInt8 
  | UInt16 
  | UInt32 
  | UInt64 
  | Int8 
  | Int16 
  | Int32 
  | Int64 
  | Bool 
  | CInt [@@deriving show]
and binder = {
  name: Prims.string ;
  typ: typ }[@@deriving show]
and typ =
  | TInt of width 
  | TBuf of typ 
  | TUnit 
  | TQualified of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2 
  | TBool 
  | TAny 
  | TArrow of (typ,typ) FStar_Pervasives_Native.tuple2 
  | TBound of Prims.int 
  | TApp of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  typ Prims.list) FStar_Pervasives_Native.tuple2 
  | TTuple of typ Prims.list [@@deriving show]
let (uu___is_DGlobal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____559 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____651 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____757 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____843 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(typ,Prims.bool)
                                                FStar_Pervasives_Native.tuple2)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____951 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,(Prims.string
                                                          Prims.list,
                                                         Prims.string)
                                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1049 -> false
  
let (__proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                                              FStar_Pervasives_Native.tuple2)
                                                FStar_Pervasives_Native.tuple2
                                                Prims.list)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1156 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1160 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1164 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1168 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1172 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1176 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1180 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1184 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1189 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1200 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1205 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1217 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1229 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1240 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1244 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1248 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1253 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1271 -> false
  
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1305 -> false
  
let (__proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1328 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1339 -> false
  
let (__proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1375 -> false
  
let (__proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1411 -> false
  
let (__proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1447 -> false
  
let (__proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1479 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1501 -> false
  
let (__proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1531 -> false
  
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1565 -> false
  
let (__proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1595 -> false
  
let (__proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1629 -> false
  
let (__proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1663 -> false
  
let (__proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1715 -> false
  
let (__proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1761 -> false
  
let (__proj__EOp__item___0 :
  expr -> (op,width) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1789 -> false
  
let (__proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1812 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1816 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1821 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1832 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1836 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1841 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1863 -> false
  
let (__proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1911 -> false
  
let (__proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1945 -> false
  
let (__proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1975 -> false
  
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2007 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2033 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2075 -> false
  
let (__proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2105 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2125 -> false
  
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2161 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2173 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____2184 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2188 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____2192 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2196 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____2200 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2204 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2208 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2212 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____2216 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____2220 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2224 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2228 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2232 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2236 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2240 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____2244 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____2248 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____2252 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____2256 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____2260 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____2264 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____2268 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____2272 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____2276 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____2280 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2284 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2289 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2301 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2319 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2351 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2375 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2409 -> false
  
let (__proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2432 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2436 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2440 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2444 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2448 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2452 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2456 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2460 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2464 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2468 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ;_} -> __fname__name
  
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ;_} -> __fname__typ
  
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____2483 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2495 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2506 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2517 -> false
  
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2546 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2550 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2559 -> false
  
let (__proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2583 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2607 -> false
  
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2657 -> false
  
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee  -> match projectee with | TTuple _0 -> _0 
type program = decl Prims.list[@@deriving show]
type ident = Prims.string[@@deriving show]
type fields_t =
  (Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type branches_t =
  (Prims.string,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type fsdoc = Prims.string[@@deriving show]
type branch = (pattern,expr) FStar_Pervasives_Native.tuple2[@@deriving show]
type branches = (pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type constant = (width,Prims.string) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
type var = Prims.int[@@deriving show]
type lident =
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
[@@deriving show]
type version = Prims.int[@@deriving show]
let (current_version : version) = (Prims.parse_int "27") 
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
[@@deriving show]
let fst3 :
  'Auu____2733 'Auu____2734 'Auu____2735 .
    ('Auu____2733,'Auu____2734,'Auu____2735) FStar_Pervasives_Native.tuple3
      -> 'Auu____2733
  = fun uu____2745  -> match uu____2745 with | (x,uu____2753,uu____2754) -> x 
let snd3 :
  'Auu____2759 'Auu____2760 'Auu____2761 .
    ('Auu____2759,'Auu____2760,'Auu____2761) FStar_Pervasives_Native.tuple3
      -> 'Auu____2760
  = fun uu____2771  -> match uu____2771 with | (uu____2778,x,uu____2780) -> x 
let thd3 :
  'Auu____2785 'Auu____2786 'Auu____2787 .
    ('Auu____2785,'Auu____2786,'Auu____2787) FStar_Pervasives_Native.tuple3
      -> 'Auu____2787
  = fun uu____2797  -> match uu____2797 with | (uu____2804,uu____2805,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___35_2811  ->
    match uu___35_2811 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2814 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___36_2819  ->
    match uu___36_2819 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2822 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___37_2832  ->
    match uu___37_2832 with
    | "add" -> FStar_Pervasives_Native.Some Add
    | "op_Plus_Hat" -> FStar_Pervasives_Native.Some Add
    | "add_mod" -> FStar_Pervasives_Native.Some AddW
    | "op_Plus_Percent_Hat" -> FStar_Pervasives_Native.Some AddW
    | "sub" -> FStar_Pervasives_Native.Some Sub
    | "op_Subtraction_Hat" -> FStar_Pervasives_Native.Some Sub
    | "sub_mod" -> FStar_Pervasives_Native.Some SubW
    | "op_Subtraction_Percent_Hat" -> FStar_Pervasives_Native.Some SubW
    | "mul" -> FStar_Pervasives_Native.Some Mult
    | "op_Star_Hat" -> FStar_Pervasives_Native.Some Mult
    | "mul_mod" -> FStar_Pervasives_Native.Some MultW
    | "op_Star_Percent_Hat" -> FStar_Pervasives_Native.Some MultW
    | "div" -> FStar_Pervasives_Native.Some Div
    | "op_Slash_Hat" -> FStar_Pervasives_Native.Some Div
    | "div_mod" -> FStar_Pervasives_Native.Some DivW
    | "op_Slash_Percent_Hat" -> FStar_Pervasives_Native.Some DivW
    | "rem" -> FStar_Pervasives_Native.Some Mod
    | "op_Percent_Hat" -> FStar_Pervasives_Native.Some Mod
    | "logor" -> FStar_Pervasives_Native.Some BOr
    | "op_Bar_Hat" -> FStar_Pervasives_Native.Some BOr
    | "logxor" -> FStar_Pervasives_Native.Some BXor
    | "op_Hat_Hat" -> FStar_Pervasives_Native.Some BXor
    | "logand" -> FStar_Pervasives_Native.Some BAnd
    | "op_Amp_Hat" -> FStar_Pervasives_Native.Some BAnd
    | "lognot" -> FStar_Pervasives_Native.Some BNot
    | "shift_right" -> FStar_Pervasives_Native.Some BShiftR
    | "op_Greater_Greater_Hat" -> FStar_Pervasives_Native.Some BShiftR
    | "shift_left" -> FStar_Pervasives_Native.Some BShiftL
    | "op_Less_Less_Hat" -> FStar_Pervasives_Native.Some BShiftL
    | "eq" -> FStar_Pervasives_Native.Some Eq
    | "op_Equals_Hat" -> FStar_Pervasives_Native.Some Eq
    | "op_Greater_Hat" -> FStar_Pervasives_Native.Some Gt
    | "gt" -> FStar_Pervasives_Native.Some Gt
    | "op_Greater_Equals_Hat" -> FStar_Pervasives_Native.Some Gte
    | "gte" -> FStar_Pervasives_Native.Some Gte
    | "op_Less_Hat" -> FStar_Pervasives_Native.Some Lt
    | "lt" -> FStar_Pervasives_Native.Some Lt
    | "op_Less_Equals_Hat" -> FStar_Pervasives_Native.Some Lte
    | "lte" -> FStar_Pervasives_Native.Some Lte
    | uu____2835 -> FStar_Pervasives_Native.None
  
let (is_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_op op) <> FStar_Pervasives_Native.None 
let (is_machine_int : Prims.string -> Prims.bool) =
  fun m  -> (mk_width m) <> FStar_Pervasives_Native.None 
type env =
  {
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }[@@deriving show]
and name = {
  pretty: Prims.string }[@@deriving show]
let (__proj__Mkenv__item__names : env -> name Prims.list) =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names
  
let (__proj__Mkenv__item__names_t : env -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names_t
  
let (__proj__Mkenv__item__module_name : env -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__module_name
  
let (__proj__Mkname__item__pretty : name -> Prims.string) =
  fun projectee  ->
    match projectee with | { pretty = __fname__pretty;_} -> __fname__pretty
  
let (empty : Prims.string Prims.list -> env) =
  fun module_name  -> { names = []; names_t = []; module_name } 
let (extend : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___42_2933 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___42_2933.names_t);
        module_name = (uu___42_2933.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___43_2940 = env  in
      {
        names = (uu___43_2940.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___43_2940.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____2947 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____2947 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____2967 ->
          let uu____2968 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2968
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____2983 ->
          let uu____2984 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2984
  
let add_binders :
  'Auu____2988 .
    env ->
      (Prims.string,'Auu____2988) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3018  ->
             match uu____3018 with | (name,uu____3024) -> extend env1 name)
        env binders
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____3165  ->
    match uu____3165 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3213 = m  in
               match uu____3213 with
               | (path,uu____3227,uu____3228) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3250 = translate_module m  in
                FStar_Pervasives_Native.Some uu____3250)
             with
             | e ->
                 ((let uu____3259 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3259);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3260  ->
    match uu____3260 with
    | (module_name,modul,uu____3275) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3306 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___38_3321  ->
         match uu___38_3321 with
         | FStar_Extraction_ML_Syntax.Private  ->
             FStar_Pervasives_Native.Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  ->
             FStar_Pervasives_Native.Some WipeBody
         | FStar_Extraction_ML_Syntax.CInline  ->
             FStar_Pervasives_Native.Some CInline
         | FStar_Extraction_ML_Syntax.Substitute  ->
             FStar_Pervasives_Native.Some Substitute
         | FStar_Extraction_ML_Syntax.GCType  ->
             FStar_Pervasives_Native.Some GCType
         | FStar_Extraction_ML_Syntax.Comment s ->
             FStar_Pervasives_Native.Some (Comment s)
         | FStar_Extraction_ML_Syntax.StackInline  ->
             FStar_Pervasives_Native.Some MustDisappear
         | FStar_Extraction_ML_Syntax.CConst s ->
             FStar_Pervasives_Native.Some (Const s)
         | FStar_Extraction_ML_Syntax.CPrologue s ->
             FStar_Pervasives_Native.Some (Prologue s)
         | FStar_Extraction_ML_Syntax.CEpilogue s ->
             FStar_Pervasives_Native.Some (Epilogue s)
         | uu____3328 -> FStar_Pervasives_Native.None) flags1

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3341 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3343 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3347) ->
          (FStar_Util.print1_warning
             "Skipping the translation of exception: %s\n" m;
           [])

and (translate_let :
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun flavor  ->
      fun lb  ->
        match lb with
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3371;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3374;
                FStar_Extraction_ML_Syntax.loc = uu____3375;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3377;_} ->
            let assumed =
              FStar_Util.for_some
                (fun uu___39_3396  ->
                   match uu___39_3396 with
                   | FStar_Extraction_ML_Syntax.Assumed  -> true
                   | uu____3397 -> false) meta
               in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name
              else env  in
            let env2 =
              FStar_List.fold_left
                (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
               in
            let rec find_return_type eff i uu___40_3418 =
              match uu___40_3418 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3423,eff1,t) when
                  i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t)  in
            let uu____3427 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0
               in
            (match uu____3427 with
             | (eff,t) ->
                 let t1 = translate_type env2 t  in
                 let binders = translate_binders env2 args  in
                 let env3 = add_binders env2 args  in
                 let name1 = ((env3.module_name), name)  in
                 let meta1 =
                   match (eff, t1) with
                   | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3459) ->
                       let uu____3460 = translate_flags meta  in
                       MustDisappear :: uu____3460
                   | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                       let uu____3463 = translate_flags meta  in
                       MustDisappear :: uu____3463
                   | uu____3466 -> translate_flags meta  in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____3475 =
                        let uu____3476 =
                          let uu____3495 = translate_type env3 t0  in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____3495)
                           in
                        DExternal uu____3476  in
                      FStar_Pervasives_Native.Some uu____3475
                    else
                      ((let uu____3508 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath name1
                           in
                        FStar_Util.print1_warning
                          "No writing anything for %s (polymorphic assume)\n"
                          uu____3508);
                       FStar_Pervasives_Native.None))
                 else
                   (try
                      let body1 = translate_expr env3 body  in
                      FStar_Pervasives_Native.Some
                        (DFunction
                           (FStar_Pervasives_Native.None, meta1,
                             (FStar_List.length tvars), t1, name1, binders,
                             body1))
                    with
                    | e ->
                        let msg = FStar_Util.print_exn e  in
                        ((let uu____3541 =
                            let uu____3546 =
                              let uu____3547 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1
                                 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____3547 msg
                               in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____3546)
                             in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____3541);
                         (let msg1 =
                            Prims.strcat "This function was not extracted:\n"
                              msg
                             in
                          FStar_Pervasives_Native.Some
                            (DFunction
                               (FStar_Pervasives_Native.None, meta1,
                                 (FStar_List.length tvars), t1, name1,
                                 binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3564;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3567;
                     FStar_Extraction_ML_Syntax.loc = uu____3568;_},uu____3569,uu____3570);
                FStar_Extraction_ML_Syntax.mlty = uu____3571;
                FStar_Extraction_ML_Syntax.loc = uu____3572;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3574;_} ->
            let assumed =
              FStar_Util.for_some
                (fun uu___39_3593  ->
                   match uu___39_3593 with
                   | FStar_Extraction_ML_Syntax.Assumed  -> true
                   | uu____3594 -> false) meta
               in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name
              else env  in
            let env2 =
              FStar_List.fold_left
                (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
               in
            let rec find_return_type eff i uu___40_3615 =
              match uu___40_3615 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3620,eff1,t) when
                  i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t)  in
            let uu____3624 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0
               in
            (match uu____3624 with
             | (eff,t) ->
                 let t1 = translate_type env2 t  in
                 let binders = translate_binders env2 args  in
                 let env3 = add_binders env2 args  in
                 let name1 = ((env3.module_name), name)  in
                 let meta1 =
                   match (eff, t1) with
                   | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3656) ->
                       let uu____3657 = translate_flags meta  in
                       MustDisappear :: uu____3657
                   | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                       let uu____3660 = translate_flags meta  in
                       MustDisappear :: uu____3660
                   | uu____3663 -> translate_flags meta  in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____3672 =
                        let uu____3673 =
                          let uu____3692 = translate_type env3 t0  in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____3692)
                           in
                        DExternal uu____3673  in
                      FStar_Pervasives_Native.Some uu____3672
                    else
                      ((let uu____3705 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath name1
                           in
                        FStar_Util.print1_warning
                          "No writing anything for %s (polymorphic assume)\n"
                          uu____3705);
                       FStar_Pervasives_Native.None))
                 else
                   (try
                      let body1 = translate_expr env3 body  in
                      FStar_Pervasives_Native.Some
                        (DFunction
                           (FStar_Pervasives_Native.None, meta1,
                             (FStar_List.length tvars), t1, name1, binders,
                             body1))
                    with
                    | e ->
                        let msg = FStar_Util.print_exn e  in
                        ((let uu____3738 =
                            let uu____3743 =
                              let uu____3744 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1
                                 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____3744 msg
                               in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____3743)
                             in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____3738);
                         (let msg1 =
                            Prims.strcat "This function was not extracted:\n"
                              msg
                             in
                          FStar_Pervasives_Native.Some
                            (DFunction
                               (FStar_Pervasives_Native.None, meta1,
                                 (FStar_List.length tvars), t1, name1,
                                 binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3761;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3764;_} ->
            let meta1 = translate_flags meta  in
            let env1 =
              FStar_List.fold_left
                (fun env1  -> fun name1  -> extend_t env1 name1) env tvars
               in
            let t1 = translate_type env1 t  in
            let name1 = ((env1.module_name), name)  in
            (try
               let expr1 = translate_expr env1 expr  in
               FStar_Pervasives_Native.Some
                 (DGlobal
                    (meta1, name1, (FStar_List.length tvars), t1, expr1))
             with
             | e ->
                 ((let uu____3811 =
                     let uu____3816 =
                       let uu____3817 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       let uu____3818 = FStar_Util.print_exn e  in
                       FStar_Util.format2
                         "Not translating definition for %s (%s)\n"
                         uu____3817 uu____3818
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____3816)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____3811);
                  FStar_Pervasives_Native.Some
                    (DGlobal
                       (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3829;
            FStar_Extraction_ML_Syntax.mllb_def = uu____3830;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____3831;
            FStar_Extraction_ML_Syntax.print_typ = uu____3832;_} ->
            ((let uu____3836 =
                let uu____3841 =
                  FStar_Util.format1 "Not translating definition for %s\n"
                    name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____3841)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____3836);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____3849 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____3849
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      match ty with
      | (assumed,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          if assumed
          then
            let name2 = FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
            (FStar_Util.print1_warning
               "Not translating type definition (assumed) for %s\n" name2;
             FStar_Pervasives_Native.None)
          else
            (let uu____3889 =
               let uu____3890 =
                 let uu____3907 = translate_flags flags1  in
                 let uu____3910 = translate_type env1 t  in
                 (name1, uu____3907, (FStar_List.length args), uu____3910)
                  in
               DTypeAlias uu____3890  in
             FStar_Pervasives_Native.Some uu____3889)
      | (uu____3919,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          let uu____3951 =
            let uu____3952 =
              let uu____3979 = translate_flags flags1  in
              let uu____3982 =
                FStar_List.map
                  (fun uu____4009  ->
                     match uu____4009 with
                     | (f,t) ->
                         let uu____4024 =
                           let uu____4029 = translate_type env1 t  in
                           (uu____4029, false)  in
                         (f, uu____4024)) fields
                 in
              (name1, uu____3979, (FStar_List.length args), uu____3982)  in
            DTypeFlat uu____3952  in
          FStar_Pervasives_Native.Some uu____3951
      | (uu____4052,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name)  in
          let flags2 = translate_flags flags1  in
          let env1 = FStar_List.fold_left extend_t env args  in
          let uu____4089 =
            let uu____4090 =
              let uu____4123 =
                FStar_List.map
                  (fun uu____4168  ->
                     match uu____4168 with
                     | (cons1,ts) ->
                         let uu____4207 =
                           FStar_List.map
                             (fun uu____4234  ->
                                match uu____4234 with
                                | (name2,t) ->
                                    let uu____4249 =
                                      let uu____4254 = translate_type env1 t
                                         in
                                      (uu____4254, false)  in
                                    (name2, uu____4249)) ts
                            in
                         (cons1, uu____4207)) branches
                 in
              (name1, flags2, (FStar_List.length args), uu____4123)  in
            DTypeVariant uu____4090  in
          FStar_Pervasives_Native.Some uu____4089
      | (uu____4293,name,_mangled_name,uu____4296,uu____4297,uu____4298) ->
          ((let uu____4308 =
              let uu____4313 =
                FStar_Util.format1 "Not translating type definition for %s\n"
                  name
                 in
              (FStar_Errors.Warning_DefinitionNotTranslated, uu____4313)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____4308);
           FStar_Pervasives_Native.None)

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4317 = find_t env name  in TBound uu____4317
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4319,t2) ->
          let uu____4321 =
            let uu____4326 = translate_type env t1  in
            let uu____4327 = translate_type env t2  in
            (uu____4326, uu____4327)  in
          TArrow uu____4321
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4331 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4331 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4335 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4335 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4347 = FStar_Util.must (mk_width m)  in TInt uu____4347
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4359 = FStar_Util.must (mk_width m)  in TInt uu____4359
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4364 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4364 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4365::arg::uu____4367::[],p) when
          (((let uu____4373 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4373 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4375 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4375 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4377 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4377 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4379 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4379 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4380 = translate_type env arg  in TBuf uu____4380
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4382::[],p) when
          ((((((((((let uu____4388 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4388 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4390 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4390 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4392 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4392 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4394 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4394 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4396 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4396 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4398 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4398 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4400 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4400 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4402 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4402 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4404 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4404 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4406 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4406 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4408 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4408 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4409 = translate_type env arg  in TBuf uu____4409
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          ((((((((((let uu____4416 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4416 = "FStar.Buffer.buffer") ||
                     (let uu____4418 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4418 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4420 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4420 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4422 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4422 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4424 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4424 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4426 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4426 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4428 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4428 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4430 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4430 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4432 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4432 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4434 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4434 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4436 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4436 = "FStar.HyperStack.ST.mmref")
          -> let uu____4437 = translate_type env arg  in TBuf uu____4437
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4438::arg::[],p) when
          (let uu____4445 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4445 = "FStar.HyperStack.s_ref") ||
            (let uu____4447 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4447 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4448 = translate_type env arg  in TBuf uu____4448
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4449::[],p) when
          let uu____4453 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4453 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4491 = FStar_List.map (translate_type env) args  in
          TTuple uu____4491
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4500 =
              let uu____4513 = FStar_List.map (translate_type env) args  in
              (lid, uu____4513)  in
            TApp uu____4500
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4522 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4522

and (translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 Prims.list -> binder Prims.list)
  = fun env  -> fun args  -> FStar_List.map (translate_binder env) args

and (translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 -> binder)
  =
  fun env  ->
    fun uu____4538  ->
      match uu____4538 with
      | (name,typ) ->
          let uu____4545 = translate_type env typ  in
          { name; typ = uu____4545 }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4550 = find env name  in EBound uu____4550
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4555 =
            let uu____4560 = FStar_Util.must (mk_op op)  in
            let uu____4561 = FStar_Util.must (mk_width m)  in
            (uu____4560, uu____4561)  in
          EOp uu____4555
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4565 =
            let uu____4570 = FStar_Util.must (mk_bool_op op)  in
            (uu____4570, Bool)  in
          EOp uu____4565
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                     FStar_Extraction_ML_Syntax.mllb_tysc =
                       FStar_Pervasives_Native.Some ([],typ);
                     FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit;
                     FStar_Extraction_ML_Syntax.mllb_def = body;
                     FStar_Extraction_ML_Syntax.mllb_meta = flags1;
                     FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let binder =
            let uu____4597 = translate_type env typ  in
            { name; typ = uu____4597 }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4623 =
            let uu____4634 = translate_expr env expr  in
            let uu____4635 = translate_branches env branches  in
            (uu____4634, uu____4635)  in
          EMatch uu____4623
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4649;
                  FStar_Extraction_ML_Syntax.loc = uu____4650;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____4652;
             FStar_Extraction_ML_Syntax.loc = uu____4653;_},arg::[])
          when
          let uu____4659 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4659 = "FStar.Dyn.undyn" ->
          let uu____4660 =
            let uu____4665 = translate_expr env arg  in
            let uu____4666 = translate_type env t  in
            (uu____4665, uu____4666)  in
          ECast uu____4660
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4668;
                  FStar_Extraction_ML_Syntax.loc = uu____4669;_},uu____4670);
             FStar_Extraction_ML_Syntax.mlty = uu____4671;
             FStar_Extraction_ML_Syntax.loc = uu____4672;_},uu____4673)
          when
          let uu____4682 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4682 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4684;
                  FStar_Extraction_ML_Syntax.loc = uu____4685;_},uu____4686);
             FStar_Extraction_ML_Syntax.mlty = uu____4687;
             FStar_Extraction_ML_Syntax.loc = uu____4688;_},arg::[])
          when
          ((let uu____4698 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____4698 = "FStar.HyperStack.All.failwith") ||
             (let uu____4700 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4700 = "FStar.Error.unexpected"))
            ||
            (let uu____4702 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4702 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____4704;
               FStar_Extraction_ML_Syntax.loc = uu____4705;_} -> EAbortS msg
           | uu____4706 ->
               let print7 =
                 let uu____4708 =
                   let uu____4709 =
                     let uu____4710 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____4710
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____4709  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____4708
                  in
               let print8 =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_App (print7, [arg]))
                  in
               let t = translate_expr env print8  in ESequence [t; EAbort])
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4716;
                  FStar_Extraction_ML_Syntax.loc = uu____4717;_},uu____4718);
             FStar_Extraction_ML_Syntax.mlty = uu____4719;
             FStar_Extraction_ML_Syntax.loc = uu____4720;_},e1::e2::[])
          when
          (let uu____4731 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4731 = "FStar.Buffer.index") ||
            (let uu____4733 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4733 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4734 =
            let uu____4739 = translate_expr env e1  in
            let uu____4740 = translate_expr env e2  in
            (uu____4739, uu____4740)  in
          EBufRead uu____4734
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4742;
                  FStar_Extraction_ML_Syntax.loc = uu____4743;_},uu____4744);
             FStar_Extraction_ML_Syntax.mlty = uu____4745;
             FStar_Extraction_ML_Syntax.loc = uu____4746;_},e1::[])
          when
          let uu____4754 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4754 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____4755 =
            let uu____4760 = translate_expr env e1  in
            (uu____4760, (EConstant (UInt32, "0")))  in
          EBufRead uu____4755
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4762;
                  FStar_Extraction_ML_Syntax.loc = uu____4763;_},uu____4764);
             FStar_Extraction_ML_Syntax.mlty = uu____4765;
             FStar_Extraction_ML_Syntax.loc = uu____4766;_},e1::e2::[])
          when
          let uu____4775 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4775 = "FStar.Buffer.create" ->
          let uu____4776 =
            let uu____4783 = translate_expr env e1  in
            let uu____4784 = translate_expr env e2  in
            (Stack, uu____4783, uu____4784)  in
          EBufCreate uu____4776
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4786;
                  FStar_Extraction_ML_Syntax.loc = uu____4787;_},uu____4788);
             FStar_Extraction_ML_Syntax.mlty = uu____4789;
             FStar_Extraction_ML_Syntax.loc = uu____4790;_},init1::[])
          when
          let uu____4798 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4798 = "FStar.HyperStack.ST.salloc" ->
          let uu____4799 =
            let uu____4806 = translate_expr env init1  in
            (Stack, uu____4806, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4799
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4808;
                  FStar_Extraction_ML_Syntax.loc = uu____4809;_},uu____4810);
             FStar_Extraction_ML_Syntax.mlty = uu____4811;
             FStar_Extraction_ML_Syntax.loc = uu____4812;_},e2::[])
          when
          let uu____4820 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4820 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4858 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a list literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____4866 =
            let uu____4873 =
              let uu____4876 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____4876  in
            (Stack, uu____4873)  in
          EBufCreateL uu____4866
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4882;
                  FStar_Extraction_ML_Syntax.loc = uu____4883;_},uu____4884);
             FStar_Extraction_ML_Syntax.mlty = uu____4885;
             FStar_Extraction_ML_Syntax.loc = uu____4886;_},_rid::init1::[])
          when
          let uu____4895 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4895 = "FStar.HyperStack.ST.ralloc" ->
          let uu____4896 =
            let uu____4903 = translate_expr env init1  in
            (Eternal, uu____4903, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4896
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4905;
                  FStar_Extraction_ML_Syntax.loc = uu____4906;_},uu____4907);
             FStar_Extraction_ML_Syntax.mlty = uu____4908;
             FStar_Extraction_ML_Syntax.loc = uu____4909;_},_e0::e1::e2::[])
          when
          let uu____4919 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4919 = "FStar.Buffer.rcreate" ->
          let uu____4920 =
            let uu____4927 = translate_expr env e1  in
            let uu____4928 = translate_expr env e2  in
            (Eternal, uu____4927, uu____4928)  in
          EBufCreate uu____4920
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4930;
                  FStar_Extraction_ML_Syntax.loc = uu____4931;_},uu____4932);
             FStar_Extraction_ML_Syntax.mlty = uu____4933;
             FStar_Extraction_ML_Syntax.loc = uu____4934;_},_rid::init1::[])
          when
          let uu____4943 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4943 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____4944 =
            let uu____4951 = translate_expr env init1  in
            (ManuallyManaged, uu____4951, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4944
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4953;
                  FStar_Extraction_ML_Syntax.loc = uu____4954;_},uu____4955);
             FStar_Extraction_ML_Syntax.mlty = uu____4956;
             FStar_Extraction_ML_Syntax.loc = uu____4957;_},_e0::e1::e2::[])
          when
          let uu____4967 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4967 = "FStar.Buffer.rcreate_mm" ->
          let uu____4968 =
            let uu____4975 = translate_expr env e1  in
            let uu____4976 = translate_expr env e2  in
            (ManuallyManaged, uu____4975, uu____4976)  in
          EBufCreate uu____4968
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4978;
                  FStar_Extraction_ML_Syntax.loc = uu____4979;_},uu____4980);
             FStar_Extraction_ML_Syntax.mlty = uu____4981;
             FStar_Extraction_ML_Syntax.loc = uu____4982;_},e2::[])
          when
          let uu____4990 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4990 = "FStar.HyperStack.ST.rfree" ->
          let uu____4991 = translate_expr env e2  in EBufFree uu____4991
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4993;
                  FStar_Extraction_ML_Syntax.loc = uu____4994;_},uu____4995);
             FStar_Extraction_ML_Syntax.mlty = uu____4996;
             FStar_Extraction_ML_Syntax.loc = uu____4997;_},e2::[])
          when
          let uu____5005 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5005 = "FStar.Buffer.rfree" ->
          let uu____5006 = translate_expr env e2  in EBufFree uu____5006
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5008;
                  FStar_Extraction_ML_Syntax.loc = uu____5009;_},uu____5010);
             FStar_Extraction_ML_Syntax.mlty = uu____5011;
             FStar_Extraction_ML_Syntax.loc = uu____5012;_},e1::e2::_e3::[])
          when
          let uu____5022 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5022 = "FStar.Buffer.sub" ->
          let uu____5023 =
            let uu____5028 = translate_expr env e1  in
            let uu____5029 = translate_expr env e2  in
            (uu____5028, uu____5029)  in
          EBufSub uu____5023
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5031;
                  FStar_Extraction_ML_Syntax.loc = uu____5032;_},uu____5033);
             FStar_Extraction_ML_Syntax.mlty = uu____5034;
             FStar_Extraction_ML_Syntax.loc = uu____5035;_},e1::e2::[])
          when
          let uu____5044 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5044 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5046;
                  FStar_Extraction_ML_Syntax.loc = uu____5047;_},uu____5048);
             FStar_Extraction_ML_Syntax.mlty = uu____5049;
             FStar_Extraction_ML_Syntax.loc = uu____5050;_},e1::e2::[])
          when
          let uu____5059 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5059 = "FStar.Buffer.offset" ->
          let uu____5060 =
            let uu____5065 = translate_expr env e1  in
            let uu____5066 = translate_expr env e2  in
            (uu____5065, uu____5066)  in
          EBufSub uu____5060
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5068;
                  FStar_Extraction_ML_Syntax.loc = uu____5069;_},uu____5070);
             FStar_Extraction_ML_Syntax.mlty = uu____5071;
             FStar_Extraction_ML_Syntax.loc = uu____5072;_},e1::e2::e3::[])
          when
          (let uu____5084 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5084 = "FStar.Buffer.upd") ||
            (let uu____5086 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5086 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5087 =
            let uu____5094 = translate_expr env e1  in
            let uu____5095 = translate_expr env e2  in
            let uu____5096 = translate_expr env e3  in
            (uu____5094, uu____5095, uu____5096)  in
          EBufWrite uu____5087
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5098;
                  FStar_Extraction_ML_Syntax.loc = uu____5099;_},uu____5100);
             FStar_Extraction_ML_Syntax.mlty = uu____5101;
             FStar_Extraction_ML_Syntax.loc = uu____5102;_},e1::e2::[])
          when
          let uu____5111 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5111 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5112 =
            let uu____5119 = translate_expr env e1  in
            let uu____5120 = translate_expr env e2  in
            (uu____5119, (EConstant (UInt32, "0")), uu____5120)  in
          EBufWrite uu____5112
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5122;
             FStar_Extraction_ML_Syntax.loc = uu____5123;_},uu____5124::[])
          when
          let uu____5127 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5127 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5129;
             FStar_Extraction_ML_Syntax.loc = uu____5130;_},uu____5131::[])
          when
          let uu____5134 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5134 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5136;
                  FStar_Extraction_ML_Syntax.loc = uu____5137;_},uu____5138);
             FStar_Extraction_ML_Syntax.mlty = uu____5139;
             FStar_Extraction_ML_Syntax.loc = uu____5140;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5152 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5152 = "FStar.Buffer.blit" ->
          let uu____5153 =
            let uu____5164 = translate_expr env e1  in
            let uu____5165 = translate_expr env e2  in
            let uu____5166 = translate_expr env e3  in
            let uu____5167 = translate_expr env e4  in
            let uu____5168 = translate_expr env e5  in
            (uu____5164, uu____5165, uu____5166, uu____5167, uu____5168)  in
          EBufBlit uu____5153
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5170;
                  FStar_Extraction_ML_Syntax.loc = uu____5171;_},uu____5172);
             FStar_Extraction_ML_Syntax.mlty = uu____5173;
             FStar_Extraction_ML_Syntax.loc = uu____5174;_},e1::e2::e3::[])
          when
          let uu____5184 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5184 = "FStar.Buffer.fill" ->
          let uu____5185 =
            let uu____5192 = translate_expr env e1  in
            let uu____5193 = translate_expr env e2  in
            let uu____5194 = translate_expr env e3  in
            (uu____5192, uu____5193, uu____5194)  in
          EBufFill uu____5185
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5196;
             FStar_Extraction_ML_Syntax.loc = uu____5197;_},uu____5198::[])
          when
          let uu____5201 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5201 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5203;
             FStar_Extraction_ML_Syntax.loc = uu____5204;_},e1::[])
          when
          let uu____5208 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5208 = "Obj.repr" ->
          let uu____5209 =
            let uu____5214 = translate_expr env e1  in (uu____5214, TAny)  in
          ECast uu____5209
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5217;
             FStar_Extraction_ML_Syntax.loc = uu____5218;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5226 = FStar_Util.must (mk_width m)  in
          let uu____5227 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5226 uu____5227 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5229;
             FStar_Extraction_ML_Syntax.loc = uu____5230;_},args)
          when is_bool_op op ->
          let uu____5238 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5238 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5240;
             FStar_Extraction_ML_Syntax.loc = uu____5241;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5243;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5244;_}::[])
          when is_machine_int m ->
          let uu____5259 =
            let uu____5264 = FStar_Util.must (mk_width m)  in (uu____5264, c)
             in
          EConstant uu____5259
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5266;
             FStar_Extraction_ML_Syntax.loc = uu____5267;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5269;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5270;_}::[])
          when is_machine_int m ->
          let uu____5285 =
            let uu____5290 = FStar_Util.must (mk_width m)  in (uu____5290, c)
             in
          EConstant uu____5285
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5291;
             FStar_Extraction_ML_Syntax.loc = uu____5292;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5294;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5295;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5301 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5302;
             FStar_Extraction_ML_Syntax.loc = uu____5303;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5305;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5306;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5312 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5314;
             FStar_Extraction_ML_Syntax.loc = uu____5315;_},arg::[])
          ->
          let is_known_type =
            (((((((FStar_Util.starts_with c "uint8") ||
                    (FStar_Util.starts_with c "uint16"))
                   || (FStar_Util.starts_with c "uint32"))
                  || (FStar_Util.starts_with c "uint64"))
                 || (FStar_Util.starts_with c "int8"))
                || (FStar_Util.starts_with c "int16"))
               || (FStar_Util.starts_with c "int32"))
              || (FStar_Util.starts_with c "int64")
             in
          if (FStar_Util.ends_with c "uint64") && is_known_type
          then
            let uu____5322 =
              let uu____5327 = translate_expr env arg  in
              (uu____5327, (TInt UInt64))  in
            ECast uu____5322
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5329 =
                 let uu____5334 = translate_expr env arg  in
                 (uu____5334, (TInt UInt32))  in
               ECast uu____5329)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5336 =
                   let uu____5341 = translate_expr env arg  in
                   (uu____5341, (TInt UInt16))  in
                 ECast uu____5336)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5343 =
                     let uu____5348 = translate_expr env arg  in
                     (uu____5348, (TInt UInt8))  in
                   ECast uu____5343)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5350 =
                       let uu____5355 = translate_expr env arg  in
                       (uu____5355, (TInt Int64))  in
                     ECast uu____5350)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5357 =
                         let uu____5362 = translate_expr env arg  in
                         (uu____5362, (TInt Int32))  in
                       ECast uu____5357)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5364 =
                           let uu____5369 = translate_expr env arg  in
                           (uu____5369, (TInt Int16))  in
                         ECast uu____5364)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5371 =
                             let uu____5376 = translate_expr env arg  in
                             (uu____5376, (TInt Int8))  in
                           ECast uu____5371)
                        else
                          (let uu____5378 =
                             let uu____5385 =
                               let uu____5388 = translate_expr env arg  in
                               [uu____5388]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5385)
                              in
                           EApp uu____5378)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5399 =
            let uu____5406 = translate_expr env head1  in
            let uu____5407 = FStar_List.map (translate_expr env) args  in
            (uu____5406, uu____5407)  in
          EApp uu____5399
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5418 =
            let uu____5425 = translate_expr env head1  in
            let uu____5426 = FStar_List.map (translate_type env) ty_args  in
            (uu____5425, uu____5426)  in
          ETypApp uu____5418
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5434 =
            let uu____5439 = translate_expr env e1  in
            let uu____5440 = translate_type env t_to  in
            (uu____5439, uu____5440)  in
          ECast uu____5434
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5441,fields) ->
          let uu____5459 =
            let uu____5470 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5471 =
              FStar_List.map
                (fun uu____5490  ->
                   match uu____5490 with
                   | (field,expr) ->
                       let uu____5501 = translate_expr env expr  in
                       (field, uu____5501)) fields
               in
            (uu____5470, uu____5471)  in
          EFlat uu____5459
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5510 =
            let uu____5517 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5518 = translate_expr env e1  in
            (uu____5517, uu____5518, (FStar_Pervasives_Native.snd path))  in
          EField uu____5510
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5521 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5533) ->
          let uu____5538 =
            let uu____5539 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5539
             in
          failwith uu____5538
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5545 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5545
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5551 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5551
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5554,cons1),es) ->
          let uu____5571 =
            let uu____5580 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5581 = FStar_List.map (translate_expr env) es  in
            (uu____5580, cons1, uu____5581)  in
          ECons uu____5571
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5604 =
            let uu____5613 = translate_expr env1 body  in
            let uu____5614 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5613, uu____5614)  in
          EFun uu____5604
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5624 =
            let uu____5631 = translate_expr env e1  in
            let uu____5632 = translate_expr env e2  in
            let uu____5633 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5631, uu____5632, uu____5633)  in
          EIfThenElse uu____5624
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5635 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5642 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5657 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5672 =
              let uu____5685 = FStar_List.map (translate_type env) ts  in
              (lid, uu____5685)  in
            TApp uu____5672
          else TQualified lid
      | uu____5691 -> failwith "invalid argument: assert_lid"

and (translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3
      Prims.list -> (pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  -> fun branches  -> FStar_List.map (translate_branch env) branches

and (translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3 ->
      (pattern,expr) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____5717  ->
      match uu____5717 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5743 = translate_pat env pat  in
            (match uu____5743 with
             | (env1,pat1) ->
                 let uu____5754 = translate_expr env1 expr  in
                 (pat1, uu____5754))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___41_5760  ->
    match uu___41_5760 with
    | FStar_Pervasives_Native.None  -> CInt
    | FStar_Pervasives_Native.Some (FStar_Const.Signed ,FStar_Const.Int8 ) ->
        Int8
    | FStar_Pervasives_Native.Some (FStar_Const.Signed ,FStar_Const.Int16 )
        -> Int16
    | FStar_Pervasives_Native.Some (FStar_Const.Signed ,FStar_Const.Int32 )
        -> Int32
    | FStar_Pervasives_Native.Some (FStar_Const.Signed ,FStar_Const.Int64 )
        -> Int64
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned ,FStar_Const.Int8 )
        -> UInt8
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned ,FStar_Const.Int16 )
        -> UInt16
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned ,FStar_Const.Int32 )
        -> UInt32
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned ,FStar_Const.Int64 )
        -> UInt64

and (translate_pat :
  env ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      (env,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit ) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Int (s,sw)) ->
          let uu____5824 =
            let uu____5825 =
              let uu____5830 = translate_width sw  in (uu____5830, s)  in
            PConstant uu____5825  in
          (env, uu____5824)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in (env1, (PVar { name; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5834,cons1),ps) ->
          let uu____5851 =
            FStar_List.fold_left
              (fun uu____5871  ->
                 fun p1  ->
                   match uu____5871 with
                   | (env1,acc) ->
                       let uu____5891 = translate_pat env1 p1  in
                       (match uu____5891 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5851 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5920,ps) ->
          let uu____5938 =
            FStar_List.fold_left
              (fun uu____5972  ->
                 fun uu____5973  ->
                   match (uu____5972, uu____5973) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6042 = translate_pat env1 p1  in
                       (match uu____6042 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____5938 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6104 =
            FStar_List.fold_left
              (fun uu____6124  ->
                 fun p1  ->
                   match uu____6124 with
                   | (env1,acc) ->
                       let uu____6144 = translate_pat env1 p1  in
                       (match uu____6144 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6104 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6171 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6176 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6187 =
            let uu____6188 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6188
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6187
          then
            let uu____6200 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6200
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6212) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6227 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6228 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        EConstant (CInt, s)

and (mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr)
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____6248 =
            let uu____6255 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6255)  in
          EApp uu____6248
