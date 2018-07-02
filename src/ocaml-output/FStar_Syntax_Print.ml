open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___201_5  ->
    match uu___201_5 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____7 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_constant_at_level " uu____7
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____9 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_equational_at_level " uu____9
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____11 =
          let uu____12 = delta_depth_to_string d  in
          Prims.strcat uu____12 ")"  in
        Prims.strcat "Delta_abstract (" uu____11
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____18 = FStar_Options.print_real_names ()  in
    if uu____18
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____35 =
      let uu____36 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____36  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____35
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____42 = FStar_Options.print_real_names ()  in
    if uu____42
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____49 =
      let uu____50 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____50  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____49
  
let (infix_prim_ops :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  [(FStar_Parser_Const.op_Addition, "+");
  (FStar_Parser_Const.op_Subtraction, "-");
  (FStar_Parser_Const.op_Multiply, "*");
  (FStar_Parser_Const.op_Division, "/");
  (FStar_Parser_Const.op_Eq, "=");
  (FStar_Parser_Const.op_ColonEq, ":=");
  (FStar_Parser_Const.op_notEq, "<>");
  (FStar_Parser_Const.op_And, "&&");
  (FStar_Parser_Const.op_Or, "||");
  (FStar_Parser_Const.op_LTE, "<=");
  (FStar_Parser_Const.op_GTE, ">=");
  (FStar_Parser_Const.op_LT, "<");
  (FStar_Parser_Const.op_GT, ">");
  (FStar_Parser_Const.op_Modulus, "mod");
  (FStar_Parser_Const.and_lid, "/\\");
  (FStar_Parser_Const.or_lid, "\\/");
  (FStar_Parser_Const.imp_lid, "==>");
  (FStar_Parser_Const.iff_lid, "<==>");
  (FStar_Parser_Const.precedes_lid, "<<");
  (FStar_Parser_Const.eq2_lid, "==");
  (FStar_Parser_Const.eq3_lid, "===")] 
let (unary_prim_ops :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  [(FStar_Parser_Const.op_Negation, "not");
  (FStar_Parser_Const.op_Minus, "-");
  (FStar_Parser_Const.not_lid, "~")] 
let (is_prim_op :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun ps  ->
    fun f  ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____188 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____199 -> failwith "get_lid"
  
let (is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
  
let (is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
  
let (quants :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")] 
type exp = FStar_Syntax_Syntax.term
let (is_b2t : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  -> is_prim_op [FStar_Parser_Const.b2t_lid] t 
let (is_quant : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t
  
let (is_ite : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  -> is_prim_op [FStar_Parser_Const.ite_lid] t 
let (is_lex_cons : exp -> Prims.bool) =
  fun f  -> is_prim_op [FStar_Parser_Const.lexcons_lid] f 
let (is_lex_top : exp -> Prims.bool) =
  fun f  -> is_prim_op [FStar_Parser_Const.lextop_lid] f 
let is_inr :
  'Auu____271 'Auu____272 .
    ('Auu____271,'Auu____272) FStar_Util.either -> Prims.bool
  =
  fun uu___202_281  ->
    match uu___202_281 with
    | FStar_Util.Inl uu____286 -> false
    | FStar_Util.Inr uu____287 -> true
  
let filter_imp :
  'Auu____292 .
    ('Auu____292,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____292,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___203_347  ->
            match uu___203_347 with
            | (uu____354,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____355)) -> false
            | uu____358 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____374 =
      let uu____375 = FStar_Syntax_Subst.compress e  in
      uu____375.FStar_Syntax_Syntax.n  in
    match uu____374 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____436 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____436
        then
          let uu____441 =
            let uu____446 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____446  in
          (match uu____441 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____456 =
                 let uu____459 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____459 :: xs  in
               FStar_Pervasives_Native.Some uu____456
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____469 ->
        let uu____470 = is_lex_top e  in
        if uu____470
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____511 = f hd1  in if uu____511 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____535 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____535
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____559 = get_lid e  in find_lid uu____559 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____569 = get_lid e  in find_lid uu____569 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____579 = get_lid t  in find_lid uu____579 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___204_589  ->
    match uu___204_589 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____597 = FStar_Options.hide_uvar_nums ()  in
    if uu____597
    then "?"
    else
      (let uu____599 =
         let uu____600 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____600 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____599)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____606 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____607 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____606 uu____607
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
     FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun u  ->
    let uu____629 = FStar_Options.hide_uvar_nums ()  in
    if uu____629
    then "?"
    else
      (let uu____631 =
         let uu____632 =
           let uu____633 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____633 FStar_Util.string_of_int  in
         let uu____634 =
           let uu____635 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____635  in
         Prims.strcat uu____632 uu____634  in
       Prims.strcat "?" uu____631)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____656 = FStar_Syntax_Subst.compress_univ u  in
      match uu____656 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____666 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____674 = FStar_Syntax_Subst.compress_univ u  in
    match uu____674 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____684 = univ_uvar_to_string u1  in
        Prims.strcat "U_unif " uu____684
    | FStar_Syntax_Syntax.U_name x ->
        Prims.strcat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____687 = FStar_Util.string_of_int x  in
        Prims.strcat "@" uu____687
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____689 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____689 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____703 = univ_to_string u2  in
             let uu____704 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____703 uu____704)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____708 =
          let uu____709 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____709 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____708
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____719 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____719 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____729 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____729 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___205_740  ->
    match uu___205_740 with
    | FStar_Syntax_Syntax.Assumption  -> "assume"
    | FStar_Syntax_Syntax.New  -> "new"
    | FStar_Syntax_Syntax.Private  -> "private"
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> "unfold"
    | FStar_Syntax_Syntax.Inline_for_extraction  -> "inline"
    | FStar_Syntax_Syntax.NoExtract  -> "noextract"
    | FStar_Syntax_Syntax.Visible_default  -> "visible"
    | FStar_Syntax_Syntax.Irreducible  -> "irreducible"
    | FStar_Syntax_Syntax.Abstract  -> "abstract"
    | FStar_Syntax_Syntax.Noeq  -> "noeq"
    | FStar_Syntax_Syntax.Unopteq  -> "unopteq"
    | FStar_Syntax_Syntax.Logic  -> "logic"
    | FStar_Syntax_Syntax.TotalEffect  -> "total"
    | FStar_Syntax_Syntax.Discriminator l ->
        let uu____742 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____742
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____745 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____745 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____756 =
          let uu____757 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____757  in
        let uu____758 =
          let uu____759 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____759 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____756 uu____758
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____778 =
          let uu____779 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____779  in
        let uu____780 =
          let uu____781 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____781 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____778 uu____780
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____791 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____791
    | FStar_Syntax_Syntax.ExceptionConstructor  -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect  -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect  -> "Effect"
    | FStar_Syntax_Syntax.Reifiable  -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str
    | FStar_Syntax_Syntax.OnlyName  -> "OnlyName"
  
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____802 ->
        let uu____805 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____805 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____823 ->
        let uu____826 = quals_to_string quals  in Prims.strcat uu____826 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____974 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____974
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____976 = nm_to_string x  in Prims.strcat "Tm_name: " uu____976
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____978 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____978
    | FStar_Syntax_Syntax.Tm_uinst uu____979 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____986 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____987 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____988,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____989;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1004,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1005;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1020 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1039 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1054 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1061 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1078 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1101 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1128 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1141 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1154,m) ->
        let uu____1192 = FStar_ST.op_Bang m  in
        (match uu____1192 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1248 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1253,m) ->
        let uu____1259 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1259
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1260 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1262 =
      let uu____1263 = FStar_Options.ugly ()  in Prims.op_Negation uu____1263
       in
    if uu____1262
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1271 = FStar_Options.print_implicits ()  in
         if uu____1271 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1275 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1298,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1322 =
             let uu____1323 =
               let uu____1324 =
                 let uu____1325 =
                   let uu____1334 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1334  in
                 uu____1325 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1324  in
             Prims.strcat uu____1323 "]"  in
           Prims.strcat "[lazy:" uu____1322
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1385;_})
           ->
           let uu____1400 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1400
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1402;_})
           ->
           let uu____1417 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1417
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1437 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1471 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1493  ->
                                 match uu____1493 with
                                 | (t1,uu____1501) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1471
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1437 (FStar_String.concat "\\/")  in
           let uu____1510 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1510
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1522 = tag_of_term t  in
           let uu____1523 = sli m  in
           let uu____1524 = term_to_string t'  in
           let uu____1525 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1522 uu____1523
             uu____1524 uu____1525
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1538 = tag_of_term t  in
           let uu____1539 = term_to_string t'  in
           let uu____1540 = sli m0  in
           let uu____1541 = sli m1  in
           let uu____1542 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1538
             uu____1539 uu____1540 uu____1541 uu____1542
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1551 = FStar_Range.string_of_range r  in
           let uu____1552 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1551
             uu____1552
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1559 = lid_to_string l  in
           let uu____1560 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1561 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1559 uu____1560
             uu____1561
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1563) ->
           let uu____1568 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1568
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1570 = db_to_string x3  in
           let uu____1571 =
             let uu____1572 =
               let uu____1573 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1573 ")"  in
             Prims.strcat ":(" uu____1572  in
           Prims.strcat uu____1570 uu____1571
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1577)) ->
           let uu____1592 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1592
           then ctx_uvar_to_string u
           else
             (let uu____1594 =
                let uu____1595 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1595  in
              Prims.strcat "?" uu____1594)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1614 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1614
           then
             let uu____1615 = ctx_uvar_to_string u  in
             let uu____1616 =
               let uu____1617 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1617 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1615 uu____1616
           else
             (let uu____1629 =
                let uu____1630 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1630  in
              Prims.strcat "?" uu____1629)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1633 = FStar_Options.print_universes ()  in
           if uu____1633
           then
             let uu____1634 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1634
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1658 = binders_to_string " -> " bs  in
           let uu____1659 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1658 uu____1659
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1688 = binders_to_string " " bs  in
                let uu____1689 = term_to_string t2  in
                let uu____1690 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1694 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1694)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1688 uu____1689
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1690
            | uu____1697 ->
                let uu____1700 = binders_to_string " " bs  in
                let uu____1701 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1700 uu____1701)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1708 = bv_to_string xt  in
           let uu____1709 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1710 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1708 uu____1709 uu____1710
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1739 = term_to_string t  in
           let uu____1740 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1739 uu____1740
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1759 = lbs_to_string [] lbs  in
           let uu____1760 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1759 uu____1760
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1821 =
                   let uu____1822 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1822
                     (FStar_Util.dflt "default")
                    in
                 let uu____1827 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1821 uu____1827
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1843 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1843
              in
           let uu____1844 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1844 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1883 = term_to_string head1  in
           let uu____1884 =
             let uu____1885 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string)
                in
             FStar_Util.concat_l "\n\t|" uu____1885  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1883 uu____1884
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1898 = FStar_Options.print_universes ()  in
           if uu____1898
           then
             let uu____1899 = term_to_string t  in
             let uu____1900 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1899 uu____1900
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____1902  ->
    match uu____1902 with
    | (p,wopt,e) ->
        let uu____1922 = FStar_All.pipe_right p pat_to_string  in
        let uu____1923 =
          match wopt with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____1931 = FStar_All.pipe_right w term_to_string  in
              FStar_Util.format1 "when %s" uu____1931
           in
        let uu____1932 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format3 "%s %s -> %s" uu____1922 uu____1923 uu____1932

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1934 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1935 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1936 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1934 uu____1935
      uu____1936

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___206_1937  ->
    match uu___206_1937 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1940 = FStar_Util.string_of_int i  in
        let uu____1941 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1940 uu____1941
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1944 = bv_to_string x  in
        let uu____1945 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1944 uu____1945
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1952 = bv_to_string x  in
        let uu____1953 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____1952 uu____1953
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1956 = FStar_Util.string_of_int i  in
        let uu____1957 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1956 uu____1957
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1960 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1960

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1962 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1962 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1972 =
      let uu____1973 = FStar_Options.ugly ()  in Prims.op_Negation uu____1973
       in
    if uu____1972
    then
      let e =
        let uu____1975 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1975  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1998 = fv_to_string l  in
           let uu____1999 =
             let uu____2000 =
               FStar_List.map
                 (fun uu____2011  ->
                    match uu____2011 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2000 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1998 uu____1999
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2023) ->
           let uu____2028 = FStar_Options.print_bound_var_types ()  in
           if uu____2028
           then
             let uu____2029 = bv_to_string x1  in
             let uu____2030 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2029 uu____2030
           else
             (let uu____2032 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2032)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2034 = FStar_Options.print_bound_var_types ()  in
           if uu____2034
           then
             let uu____2035 = bv_to_string x1  in
             let uu____2036 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2035 uu____2036
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2040 = FStar_Options.print_real_names ()  in
           if uu____2040
           then
             let uu____2041 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2041
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2053 = quals_to_string' quals  in
      let uu____2054 =
        let uu____2055 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2071 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2072 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2073 =
                    let uu____2074 = FStar_Options.print_universes ()  in
                    if uu____2074
                    then
                      let uu____2075 =
                        let uu____2076 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2076 ">"  in
                      Prims.strcat "<" uu____2075
                    else ""  in
                  let uu____2078 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2079 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2071
                    uu____2072 uu____2073 uu____2078 uu____2079))
           in
        FStar_Util.concat_l "\n and " uu____2055  in
      FStar_Util.format3 "%slet %s %s" uu____2053
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2054

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___207_2083  ->
    match uu___207_2083 with
    | [] -> ""
    | tms ->
        let uu____2089 =
          let uu____2090 =
            FStar_List.map
              (fun t  ->
                 let uu____2096 = term_to_string t  in paren uu____2096) tms
             in
          FStar_All.pipe_right uu____2090 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2089

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2100 = FStar_Options.print_effect_args ()  in
    if uu____2100
    then
      let uu____2101 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2101
    else
      (let uu____2103 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2104 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2103 uu____2104)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___208_2105  ->
    match uu___208_2105 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2106 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2109 = aqual_to_string aq  in Prims.strcat uu____2109 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2118 =
        let uu____2119 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2119  in
      if uu____2118
      then
        let uu____2120 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2120 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2126 = b  in
         match uu____2126 with
         | (a,imp) ->
             let uu____2139 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2139
             then
               let uu____2140 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2140
             else
               (let uu____2142 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2144 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2144)
                   in
                if uu____2142
                then
                  let uu____2145 = nm_to_string a  in
                  imp_to_string uu____2145 imp
                else
                  (let uu____2147 =
                     let uu____2148 = nm_to_string a  in
                     let uu____2149 =
                       let uu____2150 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2150  in
                     Prims.strcat uu____2148 uu____2149  in
                   imp_to_string uu____2147 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  = fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2164 = FStar_Options.print_implicits ()  in
        if uu____2164 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2168 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2168 (FStar_String.concat sep)
      else
        (let uu____2190 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2190 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___209_2199  ->
    match uu___209_2199 with
    | (a,imp) ->
        let uu____2206 = term_to_string a  in imp_to_string uu____2206 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2215 = FStar_Options.print_implicits ()  in
      if uu____2215 then args else filter_imp args  in
    let uu____2225 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2225 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2244 = FStar_Options.ugly ()  in
      if uu____2244
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2249 =
      let uu____2250 = FStar_Options.ugly ()  in Prims.op_Negation uu____2250
       in
    if uu____2249
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2264 =
             let uu____2265 = FStar_Syntax_Subst.compress t  in
             uu____2265.FStar_Syntax_Syntax.n  in
           (match uu____2264 with
            | FStar_Syntax_Syntax.Tm_type uu____2268 when
                let uu____2269 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2269 -> term_to_string t
            | uu____2270 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2272 = univ_to_string u  in
                     let uu____2273 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2272 uu____2273
                 | uu____2274 ->
                     let uu____2277 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2277))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2288 =
             let uu____2289 = FStar_Syntax_Subst.compress t  in
             uu____2289.FStar_Syntax_Syntax.n  in
           (match uu____2288 with
            | FStar_Syntax_Syntax.Tm_type uu____2292 when
                let uu____2293 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2293 -> term_to_string t
            | uu____2294 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2296 = univ_to_string u  in
                     let uu____2297 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2296 uu____2297
                 | uu____2298 ->
                     let uu____2301 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2301))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2304 = FStar_Options.print_effect_args ()  in
             if uu____2304
             then
               let uu____2305 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2306 =
                 let uu____2307 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2307 (FStar_String.concat ", ")
                  in
               let uu____2316 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2317 =
                 let uu____2318 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2318 (FStar_String.concat ", ")
                  in
               let uu____2335 =
                 let uu____2336 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2336 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2305
                 uu____2306 uu____2316 uu____2317 uu____2335
             else
               (let uu____2346 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_2350  ->
                           match uu___210_2350 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2351 -> false)))
                    &&
                    (let uu____2353 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2353)
                   in
                if uu____2346
                then
                  let uu____2354 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2354
                else
                  (let uu____2356 =
                     ((let uu____2359 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2359) &&
                        (let uu____2361 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2361))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2356
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2363 =
                        (let uu____2366 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2366) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2370  ->
                                   match uu___211_2370 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2371 -> false)))
                         in
                      if uu____2363
                      then
                        let uu____2372 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2372
                      else
                        (let uu____2374 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2375 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2374 uu____2375))))
              in
           let dec =
             let uu____2377 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2387  ->
                       match uu___212_2387 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2393 =
                             let uu____2394 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2394
                              in
                           [uu____2393]
                       | uu____2395 -> []))
                in
             FStar_All.pipe_right uu____2377 (FStar_String.concat " ")  in
           FStar_Util.format2 "%s%s" basic dec)

and (cflags_to_string : FStar_Syntax_Syntax.cflags -> Prims.string) =
  fun c  ->
    match c with
    | FStar_Syntax_Syntax.TOTAL  -> "total"
    | FStar_Syntax_Syntax.MLEFFECT  -> "ml"
    | FStar_Syntax_Syntax.RETURN  -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN  -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL  -> "sometrivial"
    | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> "trivial_postcondition"
    | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> "should_not_inline"
    | FStar_Syntax_Syntax.LEMMA  -> "lemma"
    | FStar_Syntax_Syntax.CPS  -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____2399 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___213_2405  ->
    match uu___213_2405 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2420 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2454 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2476  ->
                              match uu____2476 with
                              | (t,uu____2484) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2454
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2420 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2494 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2494
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2497) ->
        let uu____2498 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2498
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2506 = sli m  in
        let uu____2507 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2506 uu____2507
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2515 = sli m  in
        let uu____2516 = sli m'  in
        let uu____2517 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2515
          uu____2516 uu____2517

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2528 = FStar_Options.ugly ()  in
      if uu____2528
      then term_to_string x
      else
        (let e = FStar_Syntax_Resugar.resugar_term' env x  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)
  
let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env  ->
    fun b  ->
      let uu____2542 = b  in
      match uu____2542 with
      | (a,imp) ->
          let n1 =
            let uu____2550 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2550
            then FStar_Util.JsonNull
            else
              (let uu____2552 =
                 let uu____2553 = nm_to_string a  in
                 imp_to_string uu____2553 imp  in
               FStar_Util.JsonStr uu____2552)
             in
          let t =
            let uu____2555 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2555  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2578 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2578
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2592 = FStar_Options.print_universes ()  in
    if uu____2592 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2599 =
      let uu____2600 = FStar_Options.ugly ()  in Prims.op_Negation uu____2600
       in
    if uu____2599
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2604 = s  in
       match uu____2604 with
       | (us,t) ->
           let uu____2615 =
             let uu____2616 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2616  in
           let uu____2617 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2615 uu____2617)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2623 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2624 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2625 =
      let uu____2626 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2626  in
    let uu____2627 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2628 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2623 uu____2624 uu____2625
      uu____2627 uu____2628
  
let (eff_decl_to_string' :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string)
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____2653 =
            let uu____2654 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2654  in
          if uu____2653
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2668 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2668 (FStar_String.concat ",\n\t")
                in
             let uu____2677 =
               let uu____2680 =
                 let uu____2683 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2684 =
                   let uu____2687 =
                     let uu____2688 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2688  in
                   let uu____2689 =
                     let uu____2692 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2693 =
                       let uu____2696 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2697 =
                         let uu____2700 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2701 =
                           let uu____2704 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2705 =
                             let uu____2708 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2709 =
                               let uu____2712 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2713 =
                                 let uu____2716 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2717 =
                                   let uu____2720 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2721 =
                                     let uu____2724 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2725 =
                                       let uu____2728 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2729 =
                                         let uu____2732 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2733 =
                                           let uu____2736 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2737 =
                                             let uu____2740 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2741 =
                                               let uu____2744 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2745 =
                                                 let uu____2748 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2749 =
                                                   let uu____2752 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2752]  in
                                                 uu____2748 :: uu____2749  in
                                               uu____2744 :: uu____2745  in
                                             uu____2740 :: uu____2741  in
                                           uu____2736 :: uu____2737  in
                                         uu____2732 :: uu____2733  in
                                       uu____2728 :: uu____2729  in
                                     uu____2724 :: uu____2725  in
                                   uu____2720 :: uu____2721  in
                                 uu____2716 :: uu____2717  in
                               uu____2712 :: uu____2713  in
                             uu____2708 :: uu____2709  in
                           uu____2704 :: uu____2705  in
                         uu____2700 :: uu____2701  in
                       uu____2696 :: uu____2697  in
                     uu____2692 :: uu____2693  in
                   uu____2687 :: uu____2689  in
                 uu____2683 :: uu____2684  in
               (if for_free then "_for_free " else "") :: uu____2680  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2677)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let basic =
      match x.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
          "#light \"off\""
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          (FStar_Pervasives_Native.None )) -> "#reset-options"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          (FStar_Pervasives_Native.Some s)) ->
          FStar_Util.format1 "#reset-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
          FStar_Util.format1 "#set-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.None )) -> "#push-options"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.Some s)) ->
          FStar_Util.format1 "#push-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
          "#pop-options"
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univs1,tps,k,uu____2777,uu____2778) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____2790 = FStar_Options.print_universes ()  in
          if uu____2790
          then
            let uu____2791 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____2791 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____2796,uu____2797,uu____2798) ->
          let uu____2803 = FStar_Options.print_universes ()  in
          if uu____2803
          then
            let uu____2804 = univ_names_to_string univs1  in
            let uu____2805 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____2804
              lid.FStar_Ident.str uu____2805
          else
            (let uu____2807 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____2807)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____2811 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____2812 =
            let uu____2813 = FStar_Options.print_universes ()  in
            if uu____2813
            then
              let uu____2814 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____2814
            else ""  in
          let uu____2816 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____2811
            lid.FStar_Ident.str uu____2812 uu____2816
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____2820 = FStar_Options.print_universes ()  in
          if uu____2820
          then
            let uu____2821 = univ_names_to_string us  in
            let uu____2822 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____2821 uu____2822
          else
            (let uu____2824 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2824)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____2826) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____2832 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____2832
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2834) ->
          let uu____2843 =
            let uu____2844 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____2844 (FStar_String.concat "\n")  in
          Prims.strcat "(* Sig_bundle *)" uu____2843
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          eff_decl_to_string' false x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          eff_decl_to_string' true x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se ->
          let lift_wp =
            match ((se.FStar_Syntax_Syntax.lift_wp),
                    (se.FStar_Syntax_Syntax.lift))
            with
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                -> failwith "impossible"
            | (FStar_Pervasives_Native.Some lift_wp,uu____2880) -> lift_wp
            | (uu____2887,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____2895 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____2895 with
           | (us,t) ->
               let uu____2906 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____2907 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____2908 = univ_names_to_string us  in
               let uu____2909 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2906
                 uu____2907 uu____2908 uu____2909)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
          let uu____2919 = FStar_Options.print_universes ()  in
          if uu____2919
          then
            let uu____2920 =
              let uu____2925 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____2925  in
            (match uu____2920 with
             | (univs2,t) ->
                 let uu____2938 =
                   let uu____2943 =
                     let uu____2944 = FStar_Syntax_Subst.compress t  in
                     uu____2944.FStar_Syntax_Syntax.n  in
                   match uu____2943 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____2973 -> failwith "impossible"  in
                 (match uu____2938 with
                  | (tps1,c1) ->
                      let uu____2980 = sli l  in
                      let uu____2981 = univ_names_to_string univs2  in
                      let uu____2982 = binders_to_string " " tps1  in
                      let uu____2983 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____2980
                        uu____2981 uu____2982 uu____2983))
          else
            (let uu____2985 = sli l  in
             let uu____2986 = binders_to_string " " tps  in
             let uu____2987 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____2985 uu____2986
               uu____2987)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____2994 =
            let uu____2995 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____2995  in
          let uu____3000 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____2994 uu____3000
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____3001 ->
        let uu____3004 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.strcat uu____3004 (Prims.strcat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3015 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3015 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3021,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3023;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3025;
                       FStar_Syntax_Syntax.lbdef = uu____3026;
                       FStar_Syntax_Syntax.lbattrs = uu____3027;
                       FStar_Syntax_Syntax.lbpos = uu____3028;_}::[]),uu____3029)
        ->
        let uu____3050 = lbname_to_string lb  in
        let uu____3051 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3050 uu____3051
    | uu____3052 ->
        let uu____3053 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3053 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3069 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3070 =
      let uu____3071 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3071 (FStar_String.concat "\n")  in
    let uu____3076 =
      let uu____3077 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3077 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3069 uu____3070 uu____3076
  
let (abs_ascription_to_string :
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
    FStar_Pervasives_Native.option -> Prims.string)
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder ()  in
    (match ascription with
     | FStar_Pervasives_Native.None  ->
         FStar_Util.string_builder_append strb "None"
     | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3111 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3111))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3118 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3118)));
    FStar_Util.string_of_string_builder strb
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
           (let uu____3152 = f x  in
            FStar_Util.string_builder_append strb uu____3152);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3159 = f x1  in
                 FStar_Util.string_builder_append strb uu____3159)) xs;
           FStar_Util.string_builder_append strb "]";
           FStar_Util.string_of_string_builder strb)
  
let set_to_string :
  'a . ('a -> Prims.string) -> 'a FStar_Util.set -> Prims.string =
  fun f  ->
    fun s  ->
      let elts = FStar_Util.set_elements s  in
      match elts with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "{";
           (let uu____3197 = f x  in
            FStar_Util.string_builder_append strb uu____3197);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3204 = f x1  in
                 FStar_Util.string_builder_append strb uu____3204)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3220 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3220
  