
open Prims
let intern_string : Prims.string  ->  Prims.string = (let strings = (FStar_Util.smap_create 100)
in (fun s -> (match ((FStar_Util.smap_try_find strings s)) with
| Some (res) -> begin
res
end
| None -> begin
(let _70_6 = (FStar_Util.smap_add strings s s)
in s)
end)))

let default_string_finish = (fun endm b s -> FStar_Parser_Parse.STRING (s))

let call_string_finish = (fun fin buf endm b -> (let _173_19 = (FStar_Bytes.close buf)
in (fin endm b _173_19)))

let add_string : FStar_Bytes.bytebuf  ->  Prims.string  ->  Prims.unit = (fun buf x -> (let _173_24 = (FStar_Bytes.string_as_unicode_bytes x)
in (FStar_Bytes.emit_bytes buf _173_24)))

let add_int_char : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (let _70_19 = (FStar_Bytes.emit_int_as_byte buf (c % 256))
in (FStar_Bytes.emit_int_as_byte buf (c / 256))))

let add_unichar : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (add_int_char buf c))

let add_byte_char : FStar_Bytes.bytebuf  ->  Prims.char  ->  Prims.unit = (fun buf c -> (add_int_char buf ((FStar_Util.int_of_char c) % 256)))

let stringbuf_as_bytes : FStar_Bytes.bytebuf  ->  FStar_Bytes.bytes = (fun buf -> (let bytes = (FStar_Bytes.close buf)
in (let _173_40 = ((FStar_Bytes.length bytes) / 2)
in (FStar_Bytes.make (fun i -> (FStar_Bytes.get bytes (i * 2))) _173_40))))

let stringbuf_is_bytes : FStar_Bytes.bytebuf  ->  Prims.bool = (fun buf -> (let bytes = (FStar_Bytes.close buf)
in (let ok = (FStar_Util.mk_ref true)
in (let _70_32 = (let _173_44 = (((FStar_Bytes.length bytes) / 2) - 1)
in (FStar_Util.for_range 0 _173_44 (fun i -> if ((FStar_Bytes.get bytes ((i * 2) + 1)) <> 0) then begin
(FStar_ST.op_Colon_Equals ok false)
end else begin
()
end)))
in (FStar_ST.read ok)))))

let trigraph : Prims.char  ->  Prims.char  ->  Prims.char  ->  Prims.char = (fun c1 c2 c3 -> (let digit = (fun c -> ((FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0')))
in (FStar_Util.char_of_int (((digit c1) * 100) + (((digit c2) * 10) + (digit c3))))))

let digit : Prims.char  ->  Prims.int = (fun d -> (let dd = (FStar_Util.int_of_char d)
in if ((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9'))) then begin
((FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0'))
end else begin
(FStar_All.failwith "digit")
end))

let hexdigit : Prims.char  ->  Prims.int = (fun d -> (let dd = (FStar_Util.int_of_char d)
in if ((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9'))) then begin
(digit d)
end else begin
if ((dd >= (FStar_Util.int_of_char 'a')) && (dd <= (FStar_Util.int_of_char 'f'))) then begin
((dd - (FStar_Util.int_of_char 'a')) + 10)
end else begin
if ((dd >= (FStar_Util.int_of_char 'A')) && (dd <= (FStar_Util.int_of_char 'F'))) then begin
((dd - (FStar_Util.int_of_char 'A')) + 10)
end else begin
(FStar_All.failwith "hexdigit")
end
end
end))

let unicodegraph_short : Prims.string  ->  Prims.uint16 = (fun s -> if ((FStar_String.length s) <> 4) then begin
(FStar_All.failwith "unicodegraph")
end else begin
(let _173_63 = (((let _173_59 = (FStar_Util.char_at s 0)
in (hexdigit _173_59)) * 4096) + (((let _173_60 = (FStar_Util.char_at s 1)
in (hexdigit _173_60)) * 256) + (((let _173_61 = (FStar_Util.char_at s 2)
in (hexdigit _173_61)) * 16) + (let _173_62 = (FStar_Util.char_at s 3)
in (hexdigit _173_62)))))
in (FStar_Util.uint16_of_int _173_63))
end)

let hexgraph_short : Prims.string  ->  Prims.uint16 = (fun s -> if ((FStar_String.length s) <> 2) then begin
(FStar_All.failwith "hexgraph")
end else begin
(let _173_68 = (((let _173_66 = (FStar_Util.char_at s 0)
in (hexdigit _173_66)) * 16) + (let _173_67 = (FStar_Util.char_at s 1)
in (hexdigit _173_67)))
in (FStar_Util.uint16_of_int _173_68))
end)

let unicodegraph_long : Prims.string  ->  (Prims.uint16 Prims.option * Prims.uint16) = (fun s -> if ((FStar_String.length s) <> 8) then begin
(FStar_All.failwith "unicodegraph_long")
end else begin
(let high = (((let _173_71 = (FStar_Util.char_at s 0)
in (hexdigit _173_71)) * 4096) + (((let _173_72 = (FStar_Util.char_at s 1)
in (hexdigit _173_72)) * 256) + (((let _173_73 = (FStar_Util.char_at s 2)
in (hexdigit _173_73)) * 16) + (let _173_74 = (FStar_Util.char_at s 3)
in (hexdigit _173_74)))))
in (let low = (((let _173_75 = (FStar_Util.char_at s 4)
in (hexdigit _173_75)) * 4096) + (((let _173_76 = (FStar_Util.char_at s 5)
in (hexdigit _173_76)) * 256) + (((let _173_77 = (FStar_Util.char_at s 6)
in (hexdigit _173_77)) * 16) + (let _173_78 = (FStar_Util.char_at s 7)
in (hexdigit _173_78)))))
in if (high = 0) then begin
(None, (FStar_Util.uint16_of_int low))
end else begin
(Some ((FStar_Util.uint16_of_int (0xD800 + (((high * 0x10000) + (low - 0x10000)) / 0x400)))), (FStar_Util.uint16_of_int (0xDF30 + (((high * 0x10000) + (low - 0x10000)) % 0x400))))
end))
end)

let escape : Prims.char  ->  Prims.char = (fun c -> (match (c) with
| '\\' -> begin
'\\'
end
| '\'' -> begin
'\''
end
| 'n' -> begin
'\n'
end
| 't' -> begin
'\t'
end
| 'b' -> begin
'\b'
end
| 'r' -> begin
'\r'
end
| c -> begin
c
end))

type compatibilityMode =
| ALWAYS
| FSHARP

let is_ALWAYS : compatibilityMode  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ALWAYS -> begin
true
end
| _ -> begin
false
end))

let is_FSHARP : compatibilityMode  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| FSHARP -> begin
true
end
| _ -> begin
false
end))

let keywords : (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list = (let _173_84 = (FStar_List.map (fun s -> (FSHARP, s, FStar_Parser_Parse.RESERVED)) (("atomic")::("break")::("checked")::("component")::("constraint")::("constructor")::("continue")::("eager")::("fixed")::("functor")::("global")::("include")::("mixin")::("parallel")::("process")::("protected")::("pure")::("sealed")::("trait")::("tailcall")::("volatile")::[]))
in (FStar_List.append (((ALWAYS, "abstract", FStar_Parser_Parse.ABSTRACT))::((ALWAYS, "and", FStar_Parser_Parse.AND))::((ALWAYS, "as", FStar_Parser_Parse.AS))::((ALWAYS, "assert", FStar_Parser_Parse.ASSERT))::((ALWAYS, "assume", FStar_Parser_Parse.ASSUME))::((ALWAYS, "begin", FStar_Parser_Parse.BEGIN))::((FSHARP, "default", FStar_Parser_Parse.DEFAULT))::((ALWAYS, "effect", FStar_Parser_Parse.EFFECT))::((ALWAYS, "else", FStar_Parser_Parse.ELSE))::((ALWAYS, "end", FStar_Parser_Parse.END))::((ALWAYS, "ensures", FStar_Parser_Parse.ENSURES))::((ALWAYS, "exception", FStar_Parser_Parse.EXCEPTION))::((ALWAYS, "exists", FStar_Parser_Parse.EXISTS))::((ALWAYS, "false", FStar_Parser_Parse.FALSE))::((ALWAYS, "finally", FStar_Parser_Parse.FINALLY))::((ALWAYS, "for", FStar_Parser_Parse.FOR))::((ALWAYS, "forall", FStar_Parser_Parse.FORALL))::((ALWAYS, "fun", FStar_Parser_Parse.FUN))::((ALWAYS, "function", FStar_Parser_Parse.FUNCTION))::((ALWAYS, "if", FStar_Parser_Parse.IF))::((ALWAYS, "kind", FStar_Parser_Parse.KIND))::((ALWAYS, "in", FStar_Parser_Parse.IN))::((ALWAYS, "inline", FStar_Parser_Parse.INLINE))::((ALWAYS, "irreducible", FStar_Parser_Parse.IRREDUCIBLE))::((ALWAYS, "lazy", FStar_Parser_Parse.LAZY))::((ALWAYS, "let", FStar_Parser_Parse.LET (false)))::((ALWAYS, "logic", FStar_Parser_Parse.LOGIC))::((ALWAYS, "match", FStar_Parser_Parse.MATCH))::((ALWAYS, "module", FStar_Parser_Parse.MODULE))::((ALWAYS, "new", FStar_Parser_Parse.NEW))::((ALWAYS, "new_effect", FStar_Parser_Parse.NEW_EFFECT))::((ALWAYS, "of", FStar_Parser_Parse.OF))::((ALWAYS, "open", FStar_Parser_Parse.OPEN))::((ALWAYS, "or", FStar_Parser_Parse.OR))::((ALWAYS, "opaque", FStar_Parser_Parse.OPAQUE))::((ALWAYS, "private", FStar_Parser_Parse.PRIVATE))::((FSHARP, "public", FStar_Parser_Parse.PUBLIC))::((ALWAYS, "rec", FStar_Parser_Parse.REC))::((ALWAYS, "requires", FStar_Parser_Parse.REQUIRES))::((ALWAYS, "sub_effect", FStar_Parser_Parse.SUB_EFFECT))::((ALWAYS, "then", FStar_Parser_Parse.THEN))::((ALWAYS, "to", FStar_Parser_Parse.TO))::((ALWAYS, "total", FStar_Parser_Parse.TOTAL))::((ALWAYS, "true", FStar_Parser_Parse.TRUE))::((ALWAYS, "try", FStar_Parser_Parse.TRY))::((ALWAYS, "type", FStar_Parser_Parse.TYPE))::((ALWAYS, "unfoldable", FStar_Parser_Parse.UNFOLDABLE))::((ALWAYS, "val", FStar_Parser_Parse.VAL))::((ALWAYS, "when", FStar_Parser_Parse.WHEN))::((ALWAYS, "with", FStar_Parser_Parse.WITH))::((ALWAYS, "_", FStar_Parser_Parse.UNDERSCORE))::[]) _173_84))

let stringKeywords : Prims.string Prims.list = (FStar_List.map (fun _70_62 -> (match (_70_62) with
| (_70_58, w, _70_61) -> begin
w
end)) keywords)

let unreserve_words : Prims.string Prims.list = (FStar_List.choose (fun _70_67 -> (match (_70_67) with
| (mode, keyword, _70_66) -> begin
if (mode = FSHARP) then begin
Some (keyword)
end else begin
None
end
end)) keywords)

let kwd_table : FStar_Parser_Parse.token FStar_Util.smap = (let tab = (FStar_Util.smap_create 1000)
in (let _70_73 = (FStar_List.iter (fun _70_72 -> (match (_70_72) with
| (mode, keyword, token) -> begin
(FStar_Util.smap_add tab keyword token)
end)) keywords)
in tab))

let kwd : Prims.string  ->  FStar_Parser_Parse.token Prims.option = (fun s -> (FStar_Util.smap_try_find kwd_table s))

exception ReservedKeyword of ((Prims.string * FStar_Range.range))

let is_ReservedKeyword : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ReservedKeyword (_) -> begin
true
end
| _ -> begin
false
end))

let ___ReservedKeyword____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| ReservedKeyword (_70_77) -> begin
_70_77
end))

exception IndentationProblem of ((Prims.string * FStar_Range.range))

let is_IndentationProblem : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| IndentationProblem (_) -> begin
true
end
| _ -> begin
false
end))

let ___IndentationProblem____0 : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| IndentationProblem (_70_79) -> begin
_70_79
end))

type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; contents : Prims.string}

let is_Mklexargs : lexargs  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklexargs"))))

let mkLexargs = (fun _70_86 -> (match (_70_86) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; contents = contents}
end))

let kwd_or_id : lexargs  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Parser_Parse.token = (fun args r s -> (match ((kwd s)) with
| Some (v) -> begin
if (v = FStar_Parser_Parse.RESERVED) then begin
(let _70_92 = (let _173_127 = (let _173_126 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "The keyword \'%s\' is reserved for future use by F#. (%s)" s _173_126))
in (FStar_Util.print_string _173_127))
in (let _173_128 = (intern_string s)
in FStar_Parser_Parse.IDENT (_173_128)))
end else begin
v
end
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
(let _173_130 = (let _173_129 = (args.getSourceDirectory ())
in (FStar_Bytes.string_as_unicode_bytes _173_129))
in FStar_Parser_Parse.STRING (_173_130))
end
| "__SOURCE_FILE__" -> begin
(let _173_132 = (let _173_131 = (FStar_Range.file_of_range r)
in (FStar_Bytes.string_as_unicode_bytes _173_131))
in FStar_Parser_Parse.STRING (_173_132))
end
| "__LINE__" -> begin
(let _173_136 = (let _173_135 = (let _173_134 = (let _173_133 = (FStar_Range.start_of_range r)
in (FStar_Range.line_of_pos _173_133))
in (FStar_All.pipe_left FStar_Util.string_of_int _173_134))
in (_173_135, false))
in FStar_Parser_Parse.INT (_173_136))
end
| _70_99 -> begin
(let _173_137 = (intern_string s)
in FStar_Parser_Parse.IDENT (_173_137))
end)
end))




