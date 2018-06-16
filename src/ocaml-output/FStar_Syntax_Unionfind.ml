open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }
let (__proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_major
  
let (__proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_minor
  
let (vops : vops_t) =
  let major = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let next_major uu____72 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____119 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____119;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____204 =
    let uu____205 = FStar_ST.op_Bang major  in
    let uu____251 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____205;
      FStar_Syntax_Syntax.minor = uu____251
    }  in
  { next_major; next_minor } 
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf
type uf =
  {
  term_graph: tgraph ;
  univ_graph: ugraph ;
  version: FStar_Syntax_Syntax.version }
let (__proj__Mkuf__item__term_graph : uf -> tgraph) =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__term_graph
  
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__univ_graph
  
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__version
  
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v1  ->
    let uu____383 = FStar_Unionfind.puf_empty ()  in
    let uu____390 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____383; univ_graph = uu____390; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____402 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____403 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____402 uu____403
  
let (state : uf FStar_ST.ref) =
  let uu____417 = let uu____418 = vops.next_major ()  in empty uu____418  in
  FStar_Util.mk_ref uu____417 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____439  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____495  ->
    let v1 = vops.next_major ()  in
    let uu____497 = empty v1  in set uu____497
  
let (new_transaction : unit -> tx) =
  fun uu____502  ->
    let tx = let uu____504 = get ()  in TX uu____504  in
    (let uu____506 =
       let uu___82_507 = get ()  in
       let uu____508 = vops.next_minor ()  in
       {
         term_graph = (uu___82_507.term_graph);
         univ_graph = (uu___82_507.univ_graph);
         version = uu____508
       }  in
     set uu____506);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____518  -> match uu____518 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____578  -> let uu____579 = get ()  in uu____579.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____584  -> let uu____585 = get ()  in uu____585.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____591 =
      let uu___83_592 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___83_592.univ_graph);
        version = (uu___83_592.version)
      }  in
    set uu____591
  
let chk_v :
  'Auu____597 .
    ('Auu____597,FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2
      -> 'Auu____597
  =
  fun uu____606  ->
    match uu____606 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____615 =
             let uu____616 = version_to_string expected  in
             let uu____617 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____616 uu____617
              in
           failwith uu____615)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____623 = get_term_graph ()  in
    let uu____624 = chk_v u  in FStar_Unionfind.puf_id uu____623 uu____624
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____644 =
      let uu____649 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____649 n1  in
    let uu____652 = get_version ()  in (uu____644, uu____652)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____663  ->
    let uu____664 =
      let uu____669 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____669 FStar_Pervasives_Native.None  in
    let uu____672 = get_version ()  in (uu____664, uu____672)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____686 = get_term_graph ()  in
    let uu____687 = chk_v u  in FStar_Unionfind.puf_find uu____686 uu____687
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____712 =
        let uu____717 = get_term_graph ()  in
        let uu____718 = chk_v u  in
        FStar_Unionfind.puf_change uu____717 uu____718
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____712
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____743 = get_term_graph ()  in
      let uu____744 = chk_v u  in
      let uu____757 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____743 uu____744 uu____757
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____782 =
        let uu____787 = get_term_graph ()  in
        let uu____788 = chk_v u  in
        let uu____801 = chk_v v1  in
        FStar_Unionfind.puf_union uu____787 uu____788 uu____801  in
      set_term_graph uu____782
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____820  -> let uu____821 = get ()  in uu____821.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____827 =
      let uu___84_828 = get ()  in
      {
        term_graph = (uu___84_828.term_graph);
        univ_graph = ug;
        version = (uu___84_828.version)
      }  in
    set uu____827
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____834 = get_univ_graph ()  in
    let uu____835 = chk_v u  in FStar_Unionfind.puf_id uu____834 uu____835
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____851 =
      let uu____856 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____856 n1  in
    let uu____859 = get_version ()  in (uu____851, uu____859)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____868  ->
    let uu____869 =
      let uu____874 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____874 FStar_Pervasives_Native.None  in
    let uu____877 = get_version ()  in (uu____869, uu____877)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____889 = get_univ_graph ()  in
    let uu____890 = chk_v u  in FStar_Unionfind.puf_find uu____889 uu____890
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____911 =
        let uu____916 = get_univ_graph ()  in
        let uu____917 = chk_v u  in
        FStar_Unionfind.puf_change uu____916 uu____917
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____911
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____938 = get_univ_graph ()  in
      let uu____939 = chk_v u  in
      let uu____948 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____938 uu____939 uu____948
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____969 =
        let uu____974 = get_univ_graph ()  in
        let uu____975 = chk_v u  in
        let uu____984 = chk_v v1  in
        FStar_Unionfind.puf_union uu____974 uu____975 uu____984  in
      set_univ_graph uu____969
  