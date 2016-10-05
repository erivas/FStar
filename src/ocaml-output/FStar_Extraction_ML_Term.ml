
open Prims

exception Un_extractable


let is_Un_extractable = (fun _discr_ -> (match (_discr_) with
| Un_extractable (_) -> begin
true
end
| _ -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let fail = (fun r msg -> (

let _79_17 = (let _173_29 = (let _173_28 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _173_28 msg))
in (FStar_All.pipe_left FStar_Util.print_string _173_29))
in (FStar_All.failwith msg)))


let err_uninst = (fun env t _79_23 -> (match (_79_23) with
| (vars, ty) -> begin
(let _173_37 = (let _173_36 = (FStar_Syntax_Print.term_to_string t)
in (let _173_35 = (let _173_33 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _173_33 (FStar_String.concat ", ")))
in (let _173_34 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _173_36 _173_35 _173_34))))
in (fail t.FStar_Syntax_Syntax.pos _173_37))
end))


let err_ill_typed_application = (fun env t args ty -> (let _173_47 = (let _173_46 = (FStar_Syntax_Print.term_to_string t)
in (let _173_45 = (let _173_43 = (FStar_All.pipe_right args (FStar_List.map (fun _79_31 -> (match (_79_31) with
| (x, _79_30) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _173_43 (FStar_String.concat " ")))
in (let _173_44 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" _173_46 _173_45 _173_44))))
in (fail t.FStar_Syntax_Syntax.pos _173_47)))


let err_value_restriction = (fun t -> (let _173_51 = (let _173_50 = (FStar_Syntax_Print.tag_of_term t)
in (let _173_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" _173_50 _173_49)))
in (fail t.FStar_Syntax_Syntax.pos _173_51)))


let err_unexpected_eff = (fun t f0 f1 -> (let _173_56 = (let _173_55 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _173_55 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _173_56)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(

let res = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)) with
| None -> begin
l
end
| Some (_79_45, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (

let _79_50 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in (fun g l -> (

let l = (delta_norm_eff g l)
in if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid) then begin
FStar_Extraction_ML_Syntax.E_GHOST
end else begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
end))))


type level_t =
| Term_level
| Type_level
| Kind_level


let is_Term_level = (fun _discr_ -> (match (_discr_) with
| Term_level (_) -> begin
true
end
| _ -> begin
false
end))


let is_Type_level = (fun _discr_ -> (match (_discr_) with
| Type_level (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_level = (fun _discr_ -> (match (_discr_) with
| Kind_level (_) -> begin
true
end
| _ -> begin
false
end))


let predecessor = (fun t _79_1 -> (match (_79_1) with
| Term_level -> begin
Term_level
end
| Type_level -> begin
Term_level
end
| Kind_level -> begin
Type_level
end))


let rec level : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  level_t = (fun env t -> (

let predecessor = (fun l -> (predecessor t l))
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _79_67 = (FStar_Extraction_ML_UEnv.debug env (fun _79_65 -> (let _173_78 = (FStar_Syntax_Print.term_to_string t)
in (let _173_77 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "level %s (%s)\n" _173_78 _173_77)))))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_79_70) -> begin
(let _173_83 = (let _173_82 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _173_82))
in (FStar_All.failwith _173_83))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_79_74) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _79_82; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (_79_79); FStar_Syntax_Syntax.fv_qual = _79_77}) -> begin
(

let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (

let _79_87 = (FStar_Extraction_ML_UEnv.debug env (fun _79_86 -> (match (()) with
| () -> begin
(let _173_86 = (FStar_Syntax_Print.term_to_string t)
in (let _173_85 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Normalized %s to %s\n" _173_86 _173_85)))
end)))
in (level env t')))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _173_87 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _173_87))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _173_88 = (level env t)
in (FStar_All.pipe_left predecessor _173_88))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _79_110, _79_112) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_79_116) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _79_120) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _79_125) -> begin
(match ((level env x.FStar_Syntax_Syntax.sort)) with
| Term_level -> begin
Type_level
end
| l -> begin
l
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((level env (FStar_Syntax_Util.comp_result c))) with
| Term_level -> begin
Type_level
end
| l -> begin
l
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _79_139) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_79_143, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_79_148, branches) -> begin
(match (branches) with
| ((_79_155, _79_157, e))::_79_153 -> begin
(level env e)
end
| _79_162 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _79_165) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _79_170) -> begin
(level env head)
end)))))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _79_177 -> begin
true
end))


let is_type_binder = (fun env x -> (match ((level env (Prims.fst x).FStar_Syntax_Syntax.sort)) with
| Term_level -> begin
(FStar_All.failwith "Impossible: Binder is a term")
end
| Type_level -> begin
false
end
| Kind_level -> begin
true
end))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _173_97 = (FStar_Syntax_Subst.compress t)
in _173_97.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _79_203 -> begin
false
end))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _173_100 = (FStar_Syntax_Subst.compress t)
in _173_100.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _79_224 -> (match (_79_224) with
| (te, _79_223) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _79_237 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_258, fields) -> begin
(FStar_Util.for_all (fun _79_265 -> (match (_79_265) with
| (_79_263, e) -> begin
(is_ml_value e)
end)) fields)
end
| _79_267 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _79_280 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (let _173_113 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _173_113))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in if ((FStar_List.length l) <> (Prims.parse_int "2")) then begin
def
end else begin
(

let _79_287 = (FStar_List.hd l)
in (match (_79_287) with
| (p1, w1, e1) -> begin
(

let _79_291 = (let _173_116 = (FStar_List.tl l)
in (FStar_List.hd _173_116))
in (match (_79_291) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| _79_311 -> begin
def
end)
end))
end))
end))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e = if (erasable g f ty) then begin
if (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end
end else begin
e
end
in ((e), (f), (ty))))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _79_332 -> begin
(

let _79_334 = (FStar_Extraction_ML_UEnv.debug g (fun _79_333 -> (match (()) with
| () -> begin
(let _173_146 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _173_145 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _173_144 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _173_146 _173_145 _173_144))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty), (expect))))))
end)))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_79_339, t) -> begin
t
end
| _79_344 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_351) -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| None -> begin
false
end
| Some (t) -> begin
(is_top_ty t)
end)
end
| _79_357 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in if (is_top_ty mlt) then begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t))
end else begin
mlt
end))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _173_169 = (let _173_168 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _173_168))
in (FStar_All.failwith _173_169))
end
| FStar_Syntax_Syntax.Tm_uvar (_79_375) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(term_as_mlty' env t)
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv [])
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _79_411 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_79_411) with
| (bs, c) -> begin
(

let _79_414 = (binders_as_ml_binders env bs)
in (match (_79_414) with
| (mlbs, env) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c))
in (

let ed = (FStar_TypeChecker_Env.get_effect_decl env.FStar_Extraction_ML_UEnv.tcenv eff)
in if (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) then begin
(

let t = (FStar_TypeChecker_Util.reify_comp env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.lcomp_of_comp c) FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env t)
in res))
end else begin
(term_as_mlty' env (FStar_Syntax_Util.comp_result c))
end))
in (

let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (

let _79_431 = (FStar_List.fold_right (fun _79_424 _79_427 -> (match (((_79_424), (_79_427))) with
| ((_79_422, t), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (_79_431) with
| (_79_429, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let res = (match ((let _173_172 = (FStar_Syntax_Util.un_uinst head)
in _173_172.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _173_173 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), ((FStar_List.append args' args))))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _173_173))
end
| _79_445 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _79_450) -> begin
(

let _79_455 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_79_455) with
| (bs, ty) -> begin
(

let _79_458 = (binders_as_ml_binders env bs)
in (match (_79_458) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _79_472 -> (match (_79_472) with
| (a, _79_471) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let _79_478 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_79_478) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs = (

let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(

let _79_484 = (FStar_Util.first_N n_args formals)
in (match (_79_484) with
| (_79_482, rest) -> begin
(let _173_180 = (FStar_List.map (fun _79_485 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _173_180))
end))
end else begin
mlargs
end)
in (let _173_182 = (let _173_181 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((mlargs), (_173_181)))
in FStar_Extraction_ML_Syntax.MLTY_Named (_173_182))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let _79_503 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _79_492 b -> (match (_79_492) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(

let b = (Prims.fst b)
in (

let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _173_187 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_173_187), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env)))))
end else begin
(

let b = (Prims.fst b)
in (

let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (

let env = (FStar_Extraction_ML_UEnv.extend_bv env b (([]), (t)) false false false)
in (

let ml_b = (let _173_188 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_173_188), (t)))
in (((ml_b)::ml_bs), (env))))))
end
end)) (([]), (g))))
in (match (_79_503) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), _79_514) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (_79_517, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| _79_522 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NonRec, quals, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
if (body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) then begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end else begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| _79_538 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| _79_540 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end
end
| _79_542 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| _79_544 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _79_554 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (_79_556, fns)) -> begin
(

let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (

let fs = (FStar_Extraction_ML_Util.record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((p), (fs)))))
end
| _79_564 -> begin
p
end)
end)
end
| _79_566 -> begin
p
end))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let rec extract_one_pat = (fun disjunctive_pat imp g p expected_topt -> (

let ok = (fun t -> (match (expected_topt) with
| None -> begin
true
end
| Some (t') -> begin
(type_leq g t t')
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_79_582) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (let _173_229 = (let _173_228 = (let _173_227 = (let _173_226 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _173_225 = (let _173_224 = (let _173_223 = (let _173_222 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _173_221 -> FStar_Extraction_ML_Syntax.MLE_Const (_173_221)) _173_222))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _173_223))
in (_173_224)::[])
in (_173_226)::_173_225))
in ((FStar_Extraction_ML_Util.prims_op_equality), (_173_227)))
in FStar_Extraction_ML_Syntax.MLE_App (_173_228))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _173_229))
in (let _173_230 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (_173_230))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (let _173_235 = (let _173_233 = (let _173_232 = (let _173_231 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_173_231))
in ((_173_232), ([])))
in Some (_173_233))
in (let _173_234 = (ok mlty)
in ((g), (_173_235), (_173_234))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _173_240 = if imp then begin
None
end else begin
(let _173_238 = (let _173_237 = (let _173_236 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_173_236))
in ((_173_237), ([])))
in Some (_173_238))
end
in (let _173_239 = (ok mlty)
in ((g), (_173_240), (_173_239))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))), (true))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _173_245 = if imp then begin
None
end else begin
(let _173_243 = (let _173_242 = (let _173_241 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_173_241))
in ((_173_242), ([])))
in Some (_173_243))
end
in (let _173_244 = (ok mlty)
in ((g), (_173_245), (_173_244))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_79_607) -> begin
((g), (None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let _79_629 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _79_616; FStar_Extraction_ML_Syntax.loc = _79_614}, ttys, _79_622) -> begin
((n), (ttys))
end
| _79_626 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_79_629) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _79_633 = (FStar_Util.first_N nTyVars pats)
in (match (_79_633) with
| (tysVarPats, restPats) -> begin
(

let pat_ty_compat = (match (expected_topt) with
| None -> begin
true
end
| Some (expected_t) -> begin
try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun _79_646 -> (match (_79_646) with
| (p, _79_645) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (_79_648, t) -> begin
(term_as_mlty g t)
end
| _79_653 -> begin
(Prims.raise Un_extractable)
end)
end))))
in (

let pat_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (type_leq g pat_ty expected_t)))
end)
with
| Un_extractable -> begin
false
end
end)
in (

let _79_668 = (FStar_Util.fold_map (fun g _79_660 -> (match (_79_660) with
| (p, imp) -> begin
(

let _79_665 = (extract_one_pat disjunctive_pat true g p None)
in (match (_79_665) with
| (g, p, _79_664) -> begin
((g), (p))
end))
end)) g tysVarPats)
in (match (_79_668) with
| (g, tyMLPats) -> begin
(

let _79_680 = (FStar_Util.fold_map (fun g _79_672 -> (match (_79_672) with
| (p, imp) -> begin
(

let _79_677 = (extract_one_pat disjunctive_pat false g p None)
in (match (_79_677) with
| (g, p, _79_676) -> begin
((g), (p))
end))
end)) g restPats)
in (match (_79_680) with
| (g, restMLPats) -> begin
(

let _79_688 = (let _173_254 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _79_2 -> (match (_79_2) with
| Some (x) -> begin
(x)::[]
end
| _79_685 -> begin
[]
end))))
in (FStar_All.pipe_right _173_254 FStar_List.split))
in (match (_79_688) with
| (mlPats, when_clauses) -> begin
(let _173_258 = (let _173_257 = (let _173_256 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (let _173_255 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((_173_256), (_173_255))))
in Some (_173_257))
in ((g), (_173_258), (pat_ty_compat)))
end))
end))
end)))
end)))
end))
end)))
in (

let extract_one_pat = (fun disj g p expected_t -> (match ((extract_one_pat disj false g p expected_t)) with
| (g, Some (x, v), b) -> begin
((g), (((x), (v))), (b))
end
| _79_702 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
(let _173_269 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_173_269))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p)::pats) -> begin
(

let _79_718 = (extract_one_pat true g p (Some (expected_t)))
in (match (_79_718) with
| (g, p, b) -> begin
(

let _79_728 = (FStar_Util.fold_map (fun b p -> (

let _79_725 = (extract_one_pat true g p (Some (expected_t)))
in (match (_79_725) with
| (_79_722, p, b') -> begin
(((b && b')), (p))
end))) b pats)
in (match (_79_728) with
| (b, ps) -> begin
(

let ps = (p)::ps
in (

let _79_743 = (FStar_All.pipe_right ps (FStar_List.partition (fun _79_3 -> (match (_79_3) with
| (_79_732, (_79_736)::_79_734) -> begin
true
end
| _79_740 -> begin
false
end))))
in (match (_79_743) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _79_746 -> (match (_79_746) with
| (x, whens) -> begin
(let _173_274 = (mk_when_clause whens)
in ((x), (_173_274)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g), (ps), (b))
end
| rest -> begin
(let _173_278 = (let _173_277 = (let _173_276 = (let _173_275 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_173_275))
in ((_173_276), (None)))
in (_173_277)::ps)
in ((g), (_173_278), (b)))
end)
in res))
end)))
end))
end))
end
| _79_752 -> begin
(

let _79_758 = (extract_one_pat false g p (Some (expected_t)))
in (match (_79_758) with
| (g, (p, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g), ((((p), (when_clause)))::[]), (b)))
end))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _79_769, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _173_293 = (let _173_292 = (let _173_291 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (_173_291)))
in (_173_292)::more_args)
in (eta_args _173_293 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_775, _79_777) -> begin
(((FStar_List.rev more_args)), (t))
end
| _79_781 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_79_786, args), Some (FStar_Syntax_Syntax.Record_ctor (_79_791, fields))) -> begin
(

let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (

let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields)))))))
end
| _79_800 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _79_806 = (eta_args [] residualType)
in (match (_79_806) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _173_302 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _173_302))
end
| _79_809 -> begin
(

let _79_812 = (FStar_List.unzip eargs)
in (match (_79_812) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _173_304 = (let _173_303 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head), ((FStar_List.append args eargs))))))
in (FStar_All.pipe_left (as_record qual) _173_303))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _173_304))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| _79_819 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (_79_821, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _79_827; FStar_Extraction_ML_Syntax.loc = _79_825}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj (((mle), (fn)))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _79_844 -> begin
(let _173_306 = (let _173_305 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((_173_305), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_173_306))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _173_307 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _173_307))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _173_308 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _173_308))
end
| _79_884 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> if ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
f
end)


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let _79_893 = (term_as_mlexpr' g t)
in (match (_79_893) with
| (e, tag, ty) -> begin
(

let tag = (maybe_downgrade_eff g tag ty)
in (

let _79_896 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _173_333 = (let _173_332 = (FStar_Syntax_Print.tag_of_term t)
in (let _173_331 = (FStar_Syntax_Print.term_to_string t)
in (let _173_330 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" _173_332 _173_331 _173_330 (FStar_Extraction_ML_Util.eff_to_string tag)))))
in (FStar_Util.print_string _173_333))))
in (erase g e ty tag)))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let _79_904 = (check_term_as_mlexpr' g t f ty)
in (match (_79_904) with
| (e, t) -> begin
(

let _79_909 = (erase g e t f)
in (match (_79_909) with
| (r, _79_907, t) -> begin
((r), (t))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let _79_917 = (term_as_mlexpr g e0)
in (match (_79_917) with
| (e, tag, t) -> begin
(

let tag = (maybe_downgrade_eff g tag t)
in if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _173_342 = (maybe_coerce g e t ty)
in ((_173_342), (ty)))
end else begin
(err_unexpected_eff e0 f tag)
end)
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (

let _79_922 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _173_349 = (let _173_348 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _173_347 = (FStar_Syntax_Print.tag_of_term top)
in (let _173_346 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" _173_348 _173_347 _173_346))))
in (FStar_Util.print_string _173_349))))
in (

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _173_351 = (let _173_350 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _173_350))
in (FStar_All.failwith _173_351))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(match ((term_as_mlexpr' g t)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| _79_963 -> begin
(FStar_All.failwith "impossible")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, _79_967)) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in if (let _173_352 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _173_352 Prims.op_Negation)) then begin
(term_as_mlexpr' g t)
end else begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let _79_987 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (_79_987) with
| (comp_1, _79_984, _79_986) -> begin
(

let _79_1006 = (

let k = (let _173_355 = (let _173_354 = (let _173_353 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right _173_353 FStar_Syntax_Syntax.mk_binder))
in (_173_354)::[])
in (FStar_Syntax_Util.abs _173_355 body None))
in (

let _79_993 = (term_as_mlexpr g k)
in (match (_79_993) with
| (ml_k, _79_991, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_995, _79_997, m_2) -> begin
m_2
end
| _79_1002 -> begin
(FStar_All.failwith "Impossible")
end)
in ((ml_k), (m_2)))
end)))
in (match (_79_1006) with
| (ml_k, ty) -> begin
(

let bind = (let _173_358 = (let _173_357 = (let _173_356 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right _173_356 Prims.fst))
in FStar_Extraction_ML_Syntax.MLE_Name (_173_357))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _173_358))
in (let _173_359 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App (((bind), ((comp_1)::(ml_k)::[])))))
in ((_173_359), (FStar_Extraction_ML_Syntax.E_IMPURE), (ty))))
end))
end)))
end)
end
| _79_1009 -> begin
(term_as_mlexpr' g t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let _79_1026 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_79_1026) with
| (_79_1022, ty, _79_1025) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (let _173_363 = (let _173_362 = (let _173_361 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _173_360 -> FStar_Extraction_ML_Syntax.MLE_Const (_173_360)) _173_361))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _173_362))
in ((_173_363), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_79_1035), _79_1038) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (x, mltys, _79_1043), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t))
end
| ([], t) -> begin
(let _173_364 = (maybe_eta_data_and_project_record g qual t x)
in ((_173_364), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end
| _79_1055 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let _79_1063 = (FStar_Syntax_Subst.open_term bs body)
in (match (_79_1063) with
| (bs, body) -> begin
(

let _79_1066 = (binders_as_ml_binders g bs)
in (match (_79_1066) with
| (ml_bs, env) -> begin
(

let _79_1070 = (term_as_mlexpr env body)
in (match (_79_1070) with
| (ml_body, f, t) -> begin
(

let _79_1080 = (FStar_List.fold_right (fun _79_1074 _79_1077 -> (match (((_79_1074), (_79_1077))) with
| ((_79_1072, targ), (f, t)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f), (t)))))
end)) ml_bs ((f), (t)))
in (match (_79_1080) with
| (f, tfun) -> begin
(let _173_367 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((_173_367), (f), (tfun)))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _79_1086; FStar_Syntax_Syntax.pos = _79_1084; FStar_Syntax_Syntax.vars = _79_1082}, (t)::[]) -> begin
(

let _79_1097 = (term_as_mlexpr' g (Prims.fst t))
in (match (_79_1097) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_PURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_79_1105)); FStar_Syntax_Syntax.tk = _79_1103; FStar_Syntax_Syntax.pos = _79_1101; FStar_Syntax_Syntax.vars = _79_1099}, (t)::[]) -> begin
(

let _79_1116 = (term_as_mlexpr' g (Prims.fst t))
in (match (_79_1116) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_IMPURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_79_1122) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _79_1126 -> begin
(

let rec extract_app = (fun is_data _79_1131 _79_1134 restArgs -> (match (((_79_1131), (_79_1134))) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match (((restArgs), (t))) with
| ([], _79_1138) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = v; FStar_Syntax_Syntax.ty = _79_1147; FStar_Syntax_Syntax.p = _79_1145}; FStar_Syntax_Syntax.fv_delta = _79_1143; FStar_Syntax_Syntax.fv_qual = _79_1141}) -> begin
((v = FStar_Syntax_Const.op_And) || (v = FStar_Syntax_Const.op_Or))
end
| _79_1153 -> begin
false
end))
in (

let _79_1164 = if evaluation_order_guaranteed then begin
(let _173_376 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (_173_376)))
end else begin
(FStar_List.fold_left (fun _79_1157 _79_1160 -> (match (((_79_1157), (_79_1160))) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
((lbs), ((arg)::out_args))
end else begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _173_380 = (let _173_379 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_173_379)::out_args)
in (((((x), (arg)))::lbs), (_173_380))))
end
end)) (([]), ([])) mlargs_f)
end
in (match (_79_1164) with
| (lbs, mlargs) -> begin
(

let app = (let _173_381 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _173_381))
in (

let l_app = (FStar_List.fold_right (fun _79_1168 out -> (match (_79_1168) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t))))
end)))
end
| (((arg, _79_1174))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _173_385 = (let _173_384 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((_173_384), (t)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) _173_385 rest))
end else begin
(let _173_390 = (let _173_389 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _173_388 = (FStar_Syntax_Print.term_to_string arg)
in (let _173_387 = (FStar_Syntax_Print.tag_of_term arg)
in (let _173_386 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _173_389 _173_388 _173_387 _173_386)))))
in (FStar_All.failwith _173_390))
end
end
| (((e0, _79_1186))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let _79_1199 = (term_as_mlexpr g e0)
in (match (_79_1199) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _173_392 = (let _173_391 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((_173_391), (t)))
in (extract_app is_data ((mlhead), ((((e0), (f0)))::mlargs_f)) _173_392 rest)))
end)))
end
| _79_1202 -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| Some (t) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t)) restArgs)
end
| None -> begin
(err_ill_typed_application g top restArgs t)
end)
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead _79_1211 args -> (match (_79_1211) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_79_1214)) -> begin
(

let rec remove_implicits = (fun args f t -> (match (((args), (t))) with
| (((a0, Some (FStar_Syntax_Syntax.Implicit (_79_1224))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_79_1230, f', t)) -> begin
(let _173_407 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f f')
in (remove_implicits args _173_407 t))
end
| _79_1237 -> begin
((args), (f), (t))
end))
in (

let _79_1241 = (remove_implicits args f t)
in (match (_79_1241) with
| (args, f, t) -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)))
end
| _79_1243 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)
end))
in if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let _79_1264 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
((u), (q))
end
| _79_1256 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_79_1264) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, _79_1269))::_79_1266 -> begin
(is_type g a)
end
| _79_1273 -> begin
false
end)
in (

let _79_1319 = (match (vars) with
| (_79_1278)::_79_1276 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t), (args))
end
| _79_1281 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _79_1285 = (FStar_Util.first_N n args)
in (match (_79_1285) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun _79_1289 -> (match (_79_1289) with
| (x, _79_1288) -> begin
(term_as_mlty g x)
end)) prefix)
in (

let t = (instantiate ((vars), (t)) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _79_1298 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _79_1298.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _79_1298.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _79_1304; FStar_Extraction_ML_Syntax.loc = _79_1302})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let _79_1311 = head
in {FStar_Extraction_ML_Syntax.expr = _79_1311.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t))); FStar_Extraction_ML_Syntax.loc = _79_1311.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _79_1314 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in ((head), (t), (rest)))))
end))
end else begin
(err_uninst g head ((vars), (t)))
end)
end)
in (match (_79_1319) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _173_409 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in ((_173_409), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| _79_1322 -> begin
(extract_app_maybe_projector qual head_ml ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args)
end)
end)))
end))
end
| _79_1324 -> begin
(

let _79_1328 = (term_as_mlexpr g head)
in (match (_79_1328) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head ((f), (t)) args)
end))
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, tc, f) -> begin
(

let t = (match (tc) with
| FStar_Util.Inl (t) -> begin
(term_as_mlty g t)
end
| FStar_Util.Inr (c) -> begin
(term_as_mlty g (FStar_Syntax_Util.comp_result c))
end)
in (

let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (

let _79_1345 = (check_term_as_mlexpr g e0 f t)
in (match (_79_1345) with
| (e, t) -> begin
((e), (f), (t))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let _79_1361 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (e'))
end else begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (let _173_410 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _173_410))
in (

let lb = (

let _79_1355 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _79_1355.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _79_1355.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _79_1355.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _79_1355.FStar_Syntax_Syntax.lbdef})
in (

let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb)::[]), (e'))))))
end
end
in (match (_79_1361) with
| (lbs, e') -> begin
(

let lbs = if top_level then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Primops)::[]) g.FStar_Extraction_ML_UEnv.tcenv lb.FStar_Syntax_Syntax.lbdef)
in (

let _79_1364 = lb
in {FStar_Syntax_Syntax.lbname = _79_1364.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _79_1364.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _79_1364.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _79_1364.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef})))))
end else begin
lbs
end
in (

let maybe_generalize = (fun _79_1374 -> (match (_79_1374) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = _79_1372; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _173_414 = (FStar_List.hd bs)
in (FStar_All.pipe_right _173_414 (is_type_binder g))) -> begin
(

let _79_1383 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_79_1383) with
| (bs, c) -> begin
(

let _79_1393 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
((bs), ((FStar_Syntax_Util.comp_result c)))
end
| Some (bs, b, rest) -> begin
(let _173_416 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in ((bs), (_173_416)))
end)
in (match (_79_1393) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _79_1399) -> begin
(

let _79_1404 = (FStar_Syntax_Subst.open_term bs body)
in (match (_79_1404) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(

let _79_1407 = (FStar_Util.first_N n_tbinders bs)
in (match (_79_1407) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun _79_1411 _79_1415 -> (match (((_79_1411), (_79_1415))) with
| ((x, _79_1410), (y, _79_1414)) -> begin
(let _173_420 = (let _173_419 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_173_419)))
in FStar_Syntax_Syntax.NT (_173_420))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env _79_1422 -> (match (_79_1422) with
| (a, _79_1421) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (let _173_424 = (FStar_All.pipe_right targs (FStar_List.map (fun _79_1428 -> (match (_79_1428) with
| (x, _79_1427) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_173_424), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _79_1432 -> begin
false
end)
in (

let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (

let body = (match (rest_args) with
| [] -> begin
body
end
| _79_1437 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in ((lbname_), (f_e), (((t), (((targs), (polytype))))), (add_unit), (body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let env = (FStar_List.fold_left (fun env _79_1452 -> (match (_79_1452) with
| (a, _79_1451) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (let _173_428 = (FStar_All.pipe_right tbinders (FStar_List.map (fun _79_1458 -> (match (_79_1458) with
| (x, _79_1457) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_173_428), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun _79_1463 -> (match (_79_1463) with
| (bv, _79_1462) -> begin
(let _173_430 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right _173_430 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e), (args)))) None e.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t), (((tbinders), (polytype))))), (false), (e)))))))
end
| _79_1467 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _79_1469 -> begin
(

let expected_t = (term_as_mlty g t)
in ((lbname_), (f_e), (((t), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env _79_1484 -> (match (_79_1484) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env _79_1489 -> (match (_79_1489) with
| (a, _79_1488) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (

let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end else begin
(Prims.snd polytype)
end
in (

let _79_1495 = (check_term_as_mlexpr env e f expected_t)
in (match (_79_1495) with
| (e, _79_1494) -> begin
(

let f = (maybe_downgrade_eff env f expected_t)
in ((f), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let _79_1520 = (FStar_List.fold_right (fun lb _79_1501 -> (match (_79_1501) with
| (env, lbs) -> begin
(

let _79_1514 = lb
in (match (_79_1514) with
| (lbname, _79_1504, (t, (_79_1507, polytype)), add_unit, _79_1513) -> begin
(

let _79_1517 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_79_1517) with
| (env, nm) -> begin
((env), ((((nm), (lb)))::lbs))
end))
end))
end)) lbs ((g), ([])))
in (match (_79_1520) with
| (env_body, lbs) -> begin
(

let env_def = if is_rec then begin
env_body
end else begin
g
end
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'.FStar_Syntax_Syntax.pos
in (

let _79_1527 = (term_as_mlexpr env_body e')
in (match (_79_1527) with
| (e', f', t') -> begin
(

let f = (let _173_440 = (let _173_439 = (FStar_List.map Prims.fst lbs)
in (f')::_173_439)
in (FStar_Extraction_ML_Util.join_l e'_rng _173_440))
in (

let is_rec = if (is_rec = true) then begin
FStar_Extraction_ML_Syntax.Rec
end else begin
FStar_Extraction_ML_Syntax.NonRec
end
in (let _173_445 = (let _173_444 = (let _173_442 = (let _173_441 = (FStar_List.map Prims.snd lbs)
in ((is_rec), ([]), (_173_441)))
in (mk_MLE_Let top_level _173_442 e'))
in (let _173_443 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _173_444 _173_443)))
in ((_173_445), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let _79_1537 = (term_as_mlexpr g scrutinee)
in (match (_79_1537) with
| (e, f_e, t_e) -> begin
(

let _79_1541 = (check_pats_for_ite pats)
in (match (_79_1541) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match (((then_e), (else_e))) with
| (Some (then_e), Some (else_e)) -> begin
(

let _79_1553 = (term_as_mlexpr g then_e)
in (match (_79_1553) with
| (then_mle, f_then, t_then) -> begin
(

let _79_1557 = (term_as_mlexpr g else_e)
in (match (_79_1557) with
| (else_mle, f_else, t_else) -> begin
(

let _79_1560 = if (type_leq g t_then t_else) then begin
((t_else), (no_lift))
end else begin
if (type_leq g t_else t_then) then begin
((t_then), (no_lift))
end else begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end
end
in (match (_79_1560) with
| (t_branch, maybe_lift) -> begin
(let _173_476 = (let _173_474 = (let _173_473 = (let _173_472 = (maybe_lift then_mle t_then)
in (let _173_471 = (let _173_470 = (maybe_lift else_mle t_else)
in Some (_173_470))
in ((e), (_173_472), (_173_471))))
in FStar_Extraction_ML_Syntax.MLE_If (_173_473))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _173_474))
in (let _173_475 = (FStar_Extraction_ML_Util.join then_e.FStar_Syntax_Syntax.pos f_then f_else)
in ((_173_476), (_173_475), (t_branch))))
end))
end))
end))
end
| _79_1562 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let _79_1594 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let _79_1568 = (FStar_Syntax_Subst.open_branch br)
in (match (_79_1568) with
| (pat, when_opt, branch) -> begin
(

let _79_1572 = (extract_pat g pat t_e)
in (match (_79_1572) with
| (env, p, pat_t_compat) -> begin
(

let _79_1583 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let _79_1579 = (term_as_mlexpr env w)
in (match (_79_1579) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w)), (f_w)))
end))
end)
in (match (_79_1583) with
| (when_opt, f_when) -> begin
(

let _79_1587 = (term_as_mlexpr env branch)
in (match (_79_1587) with
| (mlbranch, f_branch, t_branch) -> begin
(let _173_480 = (FStar_All.pipe_right p (FStar_List.map (fun _79_1590 -> (match (_79_1590) with
| (p, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in ((p), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (_173_480)))
end))
end))
end))
end))) true))
in (match (_79_1594) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches = (FStar_List.flatten mlbranches)
in (

let e = if pat_t_compat then begin
e
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))))
end
in (match (mlbranches) with
| [] -> begin
(

let _79_1603 = (let _173_482 = (let _173_481 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _173_481))
in (FStar_All.pipe_left FStar_Util.right _173_482))
in (match (_79_1603) with
| (fw, _79_1600, _79_1602) -> begin
(let _173_487 = (let _173_486 = (let _173_485 = (let _173_484 = (let _173_483 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_173_483)::[])
in ((fw), (_173_484)))
in FStar_Extraction_ML_Syntax.MLE_App (_173_485))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _173_486))
in ((_173_487), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((_79_1606, _79_1608, (_79_1610, f_first, t_first)))::rest -> begin
(

let _79_1636 = (FStar_List.fold_left (fun _79_1618 _79_1628 -> (match (((_79_1618), (_79_1628))) with
| ((topt, f), (_79_1620, _79_1622, (_79_1624, f_branch, t_branch))) -> begin
(

let f = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt = (match (topt) with
| None -> begin
None
end
| Some (t) -> begin
if (type_leq g t t_branch) then begin
Some (t_branch)
end else begin
if (type_leq g t_branch t) then begin
Some (t)
end else begin
None
end
end
end)
in ((topt), (f))))
end)) ((Some (t_first)), (f_first)) rest)
in (match (_79_1636) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _79_1647 -> (match (_79_1647) with
| (p, (wopt, _79_1640), (b, _79_1644, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_79_1650) -> begin
b
end)
in ((p), (wopt), (b)))
end))))
in (

let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _173_491 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e), (mlbranches)))))
in ((_173_491), (f_match), (t_match)))))
end))
end)))
end))
end)
end))
end))
end))))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> (

let _79_1660 = (FStar_Util.incr c)
in (let _173_494 = (FStar_ST.read c)
in ((x), (_173_494))))))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let _79_1668 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_79_1668) with
| (_79_1666, fstar_disc_type) -> begin
(

let wildcards = (match ((let _173_501 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _173_501.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _79_1671) -> begin
(let _173_505 = (FStar_All.pipe_right binders (FStar_List.filter (fun _79_4 -> (match (_79_4) with
| (_79_1676, Some (FStar_Syntax_Syntax.Implicit (_79_1678))) -> begin
true
end
| _79_1683 -> begin
false
end))))
in (FStar_All.pipe_right _173_505 (FStar_List.map (fun _79_1684 -> (let _173_504 = (fresh "_")
in ((_173_504), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| _79_1687 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _173_520 = (let _173_519 = (let _173_518 = (let _173_517 = (let _173_516 = (let _173_515 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), ((FStar_Extraction_ML_Syntax.idsym mlid))))))
in (let _173_514 = (let _173_513 = (let _173_509 = (let _173_507 = (let _173_506 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((_173_506), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (_173_507))
in (let _173_508 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((_173_509), (None), (_173_508))))
in (let _173_512 = (let _173_511 = (let _173_510 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (_173_510)))
in (_173_511)::[])
in (_173_513)::_173_512))
in ((_173_515), (_173_514))))
in FStar_Extraction_ML_Syntax.MLE_Match (_173_516))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _173_517))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (_173_518)))
in FStar_Extraction_ML_Syntax.MLE_Fun (_173_519))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _173_520))
in FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[]))))))))
end)))




