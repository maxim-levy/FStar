
open Prims
open FStar_Pervasives

type inst_t =
(FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list


let mk : 'Auu____11 'Auu____12 . 'Auu____11 FStar_Syntax_Syntax.syntax  ->  'Auu____12  ->  'Auu____12 FStar_Syntax_Syntax.syntax = (fun t s -> (FStar_Syntax_Syntax.mk s FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))


let rec inst : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let mk1 = (mk t1)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____113) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (uu____138) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____139) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uvar (uu____156) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____173) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_bvar (uu____174) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____175) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_quoted (uu____176) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____183) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_lazy (uu____190) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(s t1 fv)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let bs1 = (inst_binders s bs)
in (

let body1 = (inst s body)
in (

let uu____217 = (

let uu____218 = (

let uu____235 = (inst_lcomp_opt s lopt)
in ((bs1), (body1), (uu____235)))
in FStar_Syntax_Syntax.Tm_abs (uu____218))
in (mk1 uu____217))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (inst_binders s bs)
in (

let c1 = (inst_comp s c)
in (mk1 (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))))))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t2) -> begin
(

let bv1 = (

let uu___28_271 = bv
in (

let uu____272 = (inst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___28_271.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___28_271.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____272}))
in (

let t3 = (inst s t2)
in (mk1 (FStar_Syntax_Syntax.Tm_refine (((bv1), (t3)))))))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____298 = (

let uu____299 = (

let uu____314 = (inst s t2)
in (

let uu____315 = (inst_args s args)
in ((uu____314), (uu____315))))
in FStar_Syntax_Syntax.Tm_app (uu____299))
in (mk1 uu____298))
end
| FStar_Syntax_Syntax.Tm_match (t2, pats) -> begin
(

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____437 -> (match (uu____437) with
| (p, wopt, t3) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____475 = (inst s w)
in FStar_Pervasives_Native.Some (uu____475))
end)
in (

let t4 = (inst s t3)
in ((p), (wopt1), (t4))))
end))))
in (

let uu____481 = (

let uu____482 = (

let uu____505 = (inst s t2)
in ((uu____505), (pats1)))
in FStar_Syntax_Syntax.Tm_match (uu____482))
in (mk1 uu____481)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, asc, f) -> begin
(

let inst_asc = (fun uu____588 -> (match (uu____588) with
| (annot, topt) -> begin
(

let topt1 = (FStar_Util.map_opt topt (inst s))
in (

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____650 = (inst s t2)
in FStar_Util.Inl (uu____650))
end
| FStar_Util.Inr (c) -> begin
(

let uu____658 = (inst_comp s c)
in FStar_Util.Inr (uu____658))
end)
in ((annot1), (topt1))))
end))
in (

let uu____671 = (

let uu____672 = (

let uu____699 = (inst s t11)
in (

let uu____700 = (inst_asc asc)
in ((uu____699), (uu____700), (f))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____672))
in (mk1 uu____671)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let lbs1 = (

let uu____752 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___29_766 = lb
in (

let uu____767 = (inst s lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____770 = (inst s lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___29_766.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___29_766.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____767; FStar_Syntax_Syntax.lbeff = uu___29_766.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____770; FStar_Syntax_Syntax.lbattrs = uu___29_766.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___29_766.FStar_Syntax_Syntax.lbpos}))))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____752)))
in (

let uu____777 = (

let uu____778 = (

let uu____791 = (inst s t2)
in ((lbs1), (uu____791)))
in FStar_Syntax_Syntax.Tm_let (uu____778))
in (mk1 uu____777)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____814 = (

let uu____815 = (

let uu____822 = (inst s t2)
in (

let uu____823 = (

let uu____824 = (FStar_All.pipe_right args (FStar_List.map (inst_args s)))
in FStar_Syntax_Syntax.Meta_pattern (uu____824))
in ((uu____822), (uu____823))))
in FStar_Syntax_Syntax.Tm_meta (uu____815))
in (mk1 uu____814))
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____882 = (

let uu____883 = (

let uu____890 = (inst s t2)
in (

let uu____891 = (

let uu____892 = (

let uu____899 = (inst s t')
in ((m), (uu____899)))
in FStar_Syntax_Syntax.Meta_monadic (uu____892))
in ((uu____890), (uu____891))))
in FStar_Syntax_Syntax.Tm_meta (uu____883))
in (mk1 uu____882))
end
| FStar_Syntax_Syntax.Tm_meta (t2, tag) -> begin
(

let uu____906 = (

let uu____907 = (

let uu____914 = (inst s t2)
in ((uu____914), (tag)))
in FStar_Syntax_Syntax.Tm_meta (uu____907))
in (mk1 uu____906))
end))))
and inst_binders : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.map (fun uu____939 -> (match (uu____939) with
| (x, imp) -> begin
(

let uu____950 = (

let uu___30_951 = x
in (

let uu____952 = (inst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___30_951.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___30_951.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____952}))
in ((uu____950), (imp)))
end)))))
and inst_args : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun s args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____995 -> (match (uu____995) with
| (a, imp) -> begin
(

let uu____1006 = (inst s a)
in ((uu____1006), (imp)))
end)))))
and inst_comp : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun s c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____1027 = (inst s t)
in (FStar_Syntax_Syntax.mk_Total' uu____1027 uopt))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____1038 = (inst s t)
in (FStar_Syntax_Syntax.mk_GTotal' uu____1038 uopt))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___31_1041 = ct
in (

let uu____1042 = (inst s ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____1045 = (inst_args s ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____1054 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___27_1064 -> (match (uu___27_1064) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____1068 = (inst s t)
in FStar_Syntax_Syntax.DECREASES (uu____1068))
end
| f -> begin
f
end))))
in {FStar_Syntax_Syntax.comp_univs = uu___31_1041.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___31_1041.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____1042; FStar_Syntax_Syntax.effect_args = uu____1045; FStar_Syntax_Syntax.flags = uu____1054}))))
in (FStar_Syntax_Syntax.mk_Comp ct1))
end))
and inst_lcomp_opt : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun s l -> (match (l) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____1083 = (

let uu___32_1084 = rc
in (

let uu____1085 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s))
in {FStar_Syntax_Syntax.residual_effect = uu___32_1084.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____1085; FStar_Syntax_Syntax.residual_flags = uu___32_1084.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____1083))
end))


let instantiate : inst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun i t -> (match (i) with
| [] -> begin
t
end
| uu____1102 -> begin
(

let inst_fv = (fun t1 fv -> (

let uu____1110 = (FStar_Util.find_opt (fun uu____1124 -> (match (uu____1124) with
| (x, uu____1130) -> begin
(FStar_Ident.lid_equals x fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)) i)
in (match (uu____1110) with
| FStar_Pervasives_Native.None -> begin
t1
end
| FStar_Pervasives_Native.Some (uu____1135, us) -> begin
(mk t1 (FStar_Syntax_Syntax.Tm_uinst (((t1), (us)))))
end)))
in (inst inst_fv t))
end))




