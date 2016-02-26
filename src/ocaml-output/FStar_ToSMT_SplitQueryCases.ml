
open Prims
# 10 "FStar.ToSMT.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _127_14 = (f FStar_ToSMT_Term.mkTrue)
in (true, _127_14, negs, t))
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, g::t::e::_45_7) -> begin
(let _127_19 = (let _127_16 = (let _127_15 = (FStar_ToSMT_Term.mkNot g)
in (negs, _127_15))
in (FStar_ToSMT_Term.mkAnd _127_16))
in (get_next_n_ite (n - 1) e _127_19 (fun x -> (let _127_18 = (FStar_ToSMT_Term.mkITE (g, t, x))
in (f _127_18)))))
end
| FStar_ToSMT_Term.FreeV (_45_18) -> begin
(let _127_20 = (f FStar_ToSMT_Term.mkTrue)
in (true, _127_20, negs, t))
end
| _45_21 -> begin
(false, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse)
end)
end)

# 22 "FStar.ToSMT.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.list  ->  (Prims.bool * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_45_27) -> begin
(let _127_31 = (let _127_30 = (let _127_29 = (FStar_ToSMT_Term.mkNot t)
in (negs, _127_29))
in (FStar_ToSMT_Term.mkAnd _127_30))
in (true, l, _127_31))
end
| _45_30 -> begin
(
# 29 "FStar.ToSMT.SplitQueryCases.fst"
let _45_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_45_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _127_34 = (let _127_33 = (FStar_ToSMT_Term.mkImp (negs, t))
in (_127_33)::l)
in (is_ite_all_the_way n rest negs' _127_34))
end else begin
(false, [], FStar_ToSMT_Term.mkFalse)
end
end))
end)
end)

# 36 "FStar.ToSMT.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _127_61 = (FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _127_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, t1::t2::_45_50) -> begin
(
# 41 "FStar.ToSMT.SplitQueryCases.fst"
let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _45_59, _45_61, _45_63, _45_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _127_69 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _127_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _45_71) -> begin
(
# 47 "FStar.ToSMT.SplitQueryCases.fst"
let _45_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_45_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _127_78 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _127_78))), l, negs))
end))
end
| _45_80 -> begin
(false, ((fun _45_81 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _45_86) -> begin
(
# 55 "FStar.ToSMT.SplitQueryCases.fst"
let _45_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_45_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _45_94 -> begin
(false, ((fun _45_95 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end))

# 60 "FStar.ToSMT.SplitQueryCases.fst"
let strip_not : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, hd::_45_100) -> begin
hd
end
| _45_106 -> begin
t
end))

# 64 "FStar.ToSMT.SplitQueryCases.fst"
let rec check_split_cases : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term Prims.list  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _127_117 = (let _127_116 = (let _127_115 = (let _127_114 = (f t)
in (FStar_ToSMT_Term.mkNot _127_114))
in (_127_115, None))
in FStar_ToSMT_Term.Assume (_127_116))
in (check _127_117))) (FStar_List.rev l)))

# 67 "FStar.ToSMT.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _127_138 = (let _127_137 = (let _127_136 = (let _127_135 = (let _127_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _127_134))
in (FStar_ToSMT_Term.mkNot _127_135))
in (_127_136, None))
in FStar_ToSMT_Term.Assume (_127_137))
in (check _127_138)))

# 70 "FStar.ToSMT.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_ToSMT_Term.decl  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _45_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _45_123 -> begin
(false, ((fun x -> x), [], FStar_ToSMT_Term.mkFalse))
end))

# 75 "FStar.ToSMT.SplitQueryCases.fst"
let handle_query : ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _45_128 check -> (match (_45_128) with
| (f, l, negs) -> begin
(
# 76 "FStar.ToSMT.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




