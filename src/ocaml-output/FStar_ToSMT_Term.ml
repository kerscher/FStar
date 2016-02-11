
open Prims
# 26 "FStar.ToSMT.Term.fst"
type sort =
| Bool_sort
| Int_sort
| Kind_sort
| Type_sort
| Term_sort
| String_sort
| Ref_sort
| Fuel_sort
| Array of (sort * sort)
| Arrow of (sort * sort)
| Sort of Prims.string

# 27 "FStar.ToSMT.Term.fst"
let is_Bool_sort = (fun _discr_ -> (match (_discr_) with
| Bool_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.ToSMT.Term.fst"
let is_Int_sort = (fun _discr_ -> (match (_discr_) with
| Int_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.ToSMT.Term.fst"
let is_Kind_sort = (fun _discr_ -> (match (_discr_) with
| Kind_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.ToSMT.Term.fst"
let is_Type_sort = (fun _discr_ -> (match (_discr_) with
| Type_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "FStar.ToSMT.Term.fst"
let is_Term_sort = (fun _discr_ -> (match (_discr_) with
| Term_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 32 "FStar.ToSMT.Term.fst"
let is_String_sort = (fun _discr_ -> (match (_discr_) with
| String_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.ToSMT.Term.fst"
let is_Ref_sort = (fun _discr_ -> (match (_discr_) with
| Ref_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.ToSMT.Term.fst"
let is_Fuel_sort = (fun _discr_ -> (match (_discr_) with
| Fuel_sort (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.ToSMT.Term.fst"
let is_Array = (fun _discr_ -> (match (_discr_) with
| Array (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.ToSMT.Term.fst"
let is_Arrow = (fun _discr_ -> (match (_discr_) with
| Arrow (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "FStar.ToSMT.Term.fst"
let is_Sort = (fun _discr_ -> (match (_discr_) with
| Sort (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.ToSMT.Term.fst"
let ___Array____0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Array (_44_10) -> begin
_44_10
end))

# 36 "FStar.ToSMT.Term.fst"
let ___Arrow____0 : sort  ->  (sort * sort) = (fun projectee -> (match (projectee) with
| Arrow (_44_13) -> begin
_44_13
end))

# 37 "FStar.ToSMT.Term.fst"
let ___Sort____0 : sort  ->  Prims.string = (fun projectee -> (match (projectee) with
| Sort (_44_16) -> begin
_44_16
end))

# 39 "FStar.ToSMT.Term.fst"
let rec strSort : sort  ->  Prims.string = (fun x -> (match (x) with
| Bool_sort -> begin
"Bool"
end
| Int_sort -> begin
"Int"
end
| Kind_sort -> begin
"Kind"
end
| Type_sort -> begin
"Type"
end
| Term_sort -> begin
"Term"
end
| String_sort -> begin
"String"
end
| Ref_sort -> begin
"Ref"
end
| Fuel_sort -> begin
"Fuel"
end
| Array (s1, s2) -> begin
(let _123_54 = (strSort s1)
in (let _123_53 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _123_54 _123_53)))
end
| Arrow (s1, s2) -> begin
(let _123_56 = (strSort s1)
in (let _123_55 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _123_56 _123_55)))
end
| Sort (s) -> begin
s
end))

# 52 "FStar.ToSMT.Term.fst"
type op =
| True
| False
| Not
| And
| Or
| Imp
| Iff
| Eq
| LT
| LTE
| GT
| GTE
| Add
| Sub
| Div
| Mul
| Minus
| Mod
| ITE
| Var of Prims.string

# 53 "FStar.ToSMT.Term.fst"
let is_True = (fun _discr_ -> (match (_discr_) with
| True (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.ToSMT.Term.fst"
let is_False = (fun _discr_ -> (match (_discr_) with
| False (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.ToSMT.Term.fst"
let is_Not = (fun _discr_ -> (match (_discr_) with
| Not (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.ToSMT.Term.fst"
let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.ToSMT.Term.fst"
let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "FStar.ToSMT.Term.fst"
let is_Imp = (fun _discr_ -> (match (_discr_) with
| Imp (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.ToSMT.Term.fst"
let is_Iff = (fun _discr_ -> (match (_discr_) with
| Iff (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.ToSMT.Term.fst"
let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.ToSMT.Term.fst"
let is_LT = (fun _discr_ -> (match (_discr_) with
| LT (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.ToSMT.Term.fst"
let is_LTE = (fun _discr_ -> (match (_discr_) with
| LTE (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.ToSMT.Term.fst"
let is_GT = (fun _discr_ -> (match (_discr_) with
| GT (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.ToSMT.Term.fst"
let is_GTE = (fun _discr_ -> (match (_discr_) with
| GTE (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.ToSMT.Term.fst"
let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.ToSMT.Term.fst"
let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.ToSMT.Term.fst"
let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))

# 68 "FStar.ToSMT.Term.fst"
let is_Mul = (fun _discr_ -> (match (_discr_) with
| Mul (_) -> begin
true
end
| _ -> begin
false
end))

# 69 "FStar.ToSMT.Term.fst"
let is_Minus = (fun _discr_ -> (match (_discr_) with
| Minus (_) -> begin
true
end
| _ -> begin
false
end))

# 70 "FStar.ToSMT.Term.fst"
let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "FStar.ToSMT.Term.fst"
let is_ITE = (fun _discr_ -> (match (_discr_) with
| ITE (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.ToSMT.Term.fst"
let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.ToSMT.Term.fst"
let ___Var____0 : op  ->  Prims.string = (fun projectee -> (match (projectee) with
| Var (_44_38) -> begin
_44_38
end))

# 74 "FStar.ToSMT.Term.fst"
type qop =
| Forall
| Exists

# 75 "FStar.ToSMT.Term.fst"
let is_Forall = (fun _discr_ -> (match (_discr_) with
| Forall (_) -> begin
true
end
| _ -> begin
false
end))

# 76 "FStar.ToSMT.Term.fst"
let is_Exists = (fun _discr_ -> (match (_discr_) with
| Exists (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "FStar.ToSMT.Term.fst"
type term' =
| Integer of Prims.string
| BoundV of Prims.int
| FreeV of fv
| App of (op * term Prims.list)
| Quant of (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term) 
 and term =
{tm : term'; hash : Prims.string; freevars : fvs FStar_Absyn_Syntax.memo} 
 and pat =
term 
 and fv =
(Prims.string * sort) 
 and fvs =
fv Prims.list

# 80 "FStar.ToSMT.Term.fst"
let is_Integer = (fun _discr_ -> (match (_discr_) with
| Integer (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "FStar.ToSMT.Term.fst"
let is_BoundV = (fun _discr_ -> (match (_discr_) with
| BoundV (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.ToSMT.Term.fst"
let is_FreeV = (fun _discr_ -> (match (_discr_) with
| FreeV (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.ToSMT.Term.fst"
let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.ToSMT.Term.fst"
let is_Quant = (fun _discr_ -> (match (_discr_) with
| Quant (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.ToSMT.Term.fst"
let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

# 80 "FStar.ToSMT.Term.fst"
let ___Integer____0 : term'  ->  Prims.string = (fun projectee -> (match (projectee) with
| Integer (_44_44) -> begin
_44_44
end))

# 81 "FStar.ToSMT.Term.fst"
let ___BoundV____0 : term'  ->  Prims.int = (fun projectee -> (match (projectee) with
| BoundV (_44_47) -> begin
_44_47
end))

# 82 "FStar.ToSMT.Term.fst"
let ___FreeV____0 : term'  ->  fv = (fun projectee -> (match (projectee) with
| FreeV (_44_50) -> begin
_44_50
end))

# 83 "FStar.ToSMT.Term.fst"
let ___App____0 : term'  ->  (op * term Prims.list) = (fun projectee -> (match (projectee) with
| App (_44_53) -> begin
_44_53
end))

# 84 "FStar.ToSMT.Term.fst"
let ___Quant____0 : term'  ->  (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term) = (fun projectee -> (match (projectee) with
| Quant (_44_56) -> begin
_44_56
end))

# 95 "FStar.ToSMT.Term.fst"
type caption =
Prims.string Prims.option

# 96 "FStar.ToSMT.Term.fst"
type binders =
(Prims.string * sort) Prims.list

# 97 "FStar.ToSMT.Term.fst"
type projector =
(Prims.string * sort)

# 98 "FStar.ToSMT.Term.fst"
type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int)

# 99 "FStar.ToSMT.Term.fst"
type constructors =
constructor_t Prims.list

# 100 "FStar.ToSMT.Term.fst"
type decl =
| DefPrelude
| DeclFun of (Prims.string * sort Prims.list * sort * caption)
| DefineFun of (Prims.string * sort Prims.list * sort * term * caption)
| Assume of (term * caption)
| Caption of Prims.string
| Eval of term
| Echo of Prims.string
| Push
| Pop
| CheckSat

# 101 "FStar.ToSMT.Term.fst"
let is_DefPrelude = (fun _discr_ -> (match (_discr_) with
| DefPrelude (_) -> begin
true
end
| _ -> begin
false
end))

# 102 "FStar.ToSMT.Term.fst"
let is_DeclFun = (fun _discr_ -> (match (_discr_) with
| DeclFun (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.ToSMT.Term.fst"
let is_DefineFun = (fun _discr_ -> (match (_discr_) with
| DefineFun (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.ToSMT.Term.fst"
let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "FStar.ToSMT.Term.fst"
let is_Caption = (fun _discr_ -> (match (_discr_) with
| Caption (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "FStar.ToSMT.Term.fst"
let is_Eval = (fun _discr_ -> (match (_discr_) with
| Eval (_) -> begin
true
end
| _ -> begin
false
end))

# 107 "FStar.ToSMT.Term.fst"
let is_Echo = (fun _discr_ -> (match (_discr_) with
| Echo (_) -> begin
true
end
| _ -> begin
false
end))

# 108 "FStar.ToSMT.Term.fst"
let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

# 109 "FStar.ToSMT.Term.fst"
let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

# 110 "FStar.ToSMT.Term.fst"
let is_CheckSat = (fun _discr_ -> (match (_discr_) with
| CheckSat (_) -> begin
true
end
| _ -> begin
false
end))

# 102 "FStar.ToSMT.Term.fst"
let ___DeclFun____0 : decl  ->  (Prims.string * sort Prims.list * sort * caption) = (fun projectee -> (match (projectee) with
| DeclFun (_44_60) -> begin
_44_60
end))

# 103 "FStar.ToSMT.Term.fst"
let ___DefineFun____0 : decl  ->  (Prims.string * sort Prims.list * sort * term * caption) = (fun projectee -> (match (projectee) with
| DefineFun (_44_63) -> begin
_44_63
end))

# 104 "FStar.ToSMT.Term.fst"
let ___Assume____0 : decl  ->  (term * caption) = (fun projectee -> (match (projectee) with
| Assume (_44_66) -> begin
_44_66
end))

# 105 "FStar.ToSMT.Term.fst"
let ___Caption____0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Caption (_44_69) -> begin
_44_69
end))

# 106 "FStar.ToSMT.Term.fst"
let ___Eval____0 : decl  ->  term = (fun projectee -> (match (projectee) with
| Eval (_44_72) -> begin
_44_72
end))

# 107 "FStar.ToSMT.Term.fst"
let ___Echo____0 : decl  ->  Prims.string = (fun projectee -> (match (projectee) with
| Echo (_44_75) -> begin
_44_75
end))

# 111 "FStar.ToSMT.Term.fst"
type decls_t =
decl Prims.list

# 195 "FStar.ToSMT.Term.fst"
let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))

# 196 "FStar.ToSMT.Term.fst"
let fv_sort = (fun x -> (Prims.snd x))

# 197 "FStar.ToSMT.Term.fst"
let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match ((x.tm, y.tm)) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _44_87 -> begin
false
end))

# 200 "FStar.ToSMT.Term.fst"
let freevar_sort : term  ->  sort = (fun _44_1 -> (match (_44_1) with
| {tm = FreeV (x); hash = _44_92; freevars = _44_90} -> begin
(fv_sort x)
end
| _44_97 -> begin
(FStar_All.failwith "impossible")
end))

# 203 "FStar.ToSMT.Term.fst"
let fv_of_term : term  ->  fv = (fun _44_2 -> (match (_44_2) with
| {tm = FreeV (fv); hash = _44_102; freevars = _44_100} -> begin
fv
end
| _44_107 -> begin
(FStar_All.failwith "impossible")
end))

# 206 "FStar.ToSMT.Term.fst"
let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_44_118, tms) -> begin
(FStar_List.collect freevars tms)
end
| Quant (_44_123, _44_125, _44_127, _44_129, t) -> begin
(freevars t)
end))

# 214 "FStar.ToSMT.Term.fst"
let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(
# 217 "FStar.ToSMT.Term.fst"
let fvs = (let _123_277 = (freevars t)
in (FStar_Util.remove_dups fv_eq _123_277))
in (
# 218 "FStar.ToSMT.Term.fst"
let _44_138 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))

# 224 "FStar.ToSMT.Term.fst"
let qop_to_string : qop  ->  Prims.string = (fun _44_3 -> (match (_44_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))

# 228 "FStar.ToSMT.Term.fst"
let op_to_string : op  ->  Prims.string = (fun _44_4 -> (match (_44_4) with
| True -> begin
"true"
end
| False -> begin
"false"
end
| Not -> begin
"not"
end
| And -> begin
"and"
end
| Or -> begin
"or"
end
| Imp -> begin
"implies"
end
| Iff -> begin
"iff"
end
| Eq -> begin
"="
end
| LT -> begin
"<"
end
| LTE -> begin
"<="
end
| GT -> begin
">"
end
| GTE -> begin
">="
end
| Add -> begin
"+"
end
| Sub -> begin
"-"
end
| Div -> begin
"div"
end
| Mul -> begin
"*"
end
| Minus -> begin
"-"
end
| Mod -> begin
"mod"
end
| ITE -> begin
"ite"
end
| Var (s) -> begin
s
end))

# 250 "FStar.ToSMT.Term.fst"
let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _44_5 -> (match (_44_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _123_284 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _123_284))
end))

# 254 "FStar.ToSMT.Term.fst"
let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _123_287 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _123_287))
end
| FreeV (x) -> begin
(let _123_288 = (strSort (Prims.snd x))
in (Prims.strcat (Prims.strcat (Prims.fst x) ":") _123_288))
end
| App (op, tms) -> begin
(let _123_292 = (let _123_291 = (let _123_290 = (FStar_List.map (fun t -> t.hash) tms)
in (FStar_All.pipe_right _123_290 (FStar_String.concat " ")))
in (Prims.strcat (Prims.strcat "(" (op_to_string op)) _123_291))
in (Prims.strcat _123_292 ")"))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _123_300 = (let _123_293 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _123_293 (FStar_String.concat " ")))
in (let _123_299 = (weightToSmt wopt)
in (let _123_298 = (let _123_297 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _123_296 = (FStar_List.map (fun p -> p.hash) pats)
in (FStar_All.pipe_right _123_296 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _123_297 (FStar_String.concat "; ")))
in (FStar_Util.format5 "(%s (%s)(! %s %s %s))" (qop_to_string qop) _123_300 body.hash _123_299 _123_298))))
end))

# 268 "FStar.ToSMT.Term.fst"
let __all_terms : term FStar_Util.smap FStar_ST.ref = (let _123_301 = (FStar_Util.smap_create 10000)
in (FStar_ST.alloc _123_301))

# 269 "FStar.ToSMT.Term.fst"
let all_terms : Prims.unit  ->  term FStar_Util.smap = (fun _44_190 -> (match (()) with
| () -> begin
(FStar_ST.read __all_terms)
end))

# 270 "FStar.ToSMT.Term.fst"
let mk : term'  ->  term = (fun t -> (
# 271 "FStar.ToSMT.Term.fst"
let key = (hash_of_term' t)
in (match ((let _123_306 = (all_terms ())
in (FStar_Util.smap_try_find _123_306 key))) with
| Some (tm) -> begin
tm
end
| None -> begin
(
# 275 "FStar.ToSMT.Term.fst"
let tm = (let _123_307 = (FStar_Util.mk_ref None)
in {tm = t; hash = key; freevars = _123_307})
in (
# 276 "FStar.ToSMT.Term.fst"
let _44_197 = (let _123_308 = (all_terms ())
in (FStar_Util.smap_add _123_308 key tm))
in tm))
end)))

# 279 "FStar.ToSMT.Term.fst"
let mkTrue : term = (mk (App ((True, []))))

# 280 "FStar.ToSMT.Term.fst"
let mkFalse : term = (mk (App ((False, []))))

# 281 "FStar.ToSMT.Term.fst"
let mkInteger : Prims.string  ->  term = (fun i -> (mk (Integer (i))))

# 282 "FStar.ToSMT.Term.fst"
let mkInteger32 : Prims.int32  ->  term = (fun i -> (mkInteger (FStar_Util.string_of_int32 i)))

# 283 "FStar.ToSMT.Term.fst"
let mkInteger' : Prims.int  ->  term = (fun i -> (let _123_315 = (FStar_Util.string_of_int i)
in (mkInteger _123_315)))

# 284 "FStar.ToSMT.Term.fst"
let mkBoundV : Prims.int  ->  term = (fun i -> (mk (BoundV (i))))

# 285 "FStar.ToSMT.Term.fst"
let mkFreeV : (Prims.string * sort)  ->  term = (fun x -> (mk (FreeV (x))))

# 286 "FStar.ToSMT.Term.fst"
let mkApp' : (op * term Prims.list)  ->  term = (fun f -> (mk (App (f))))

# 287 "FStar.ToSMT.Term.fst"
let mkApp : (Prims.string * term Prims.list)  ->  term = (fun _44_207 -> (match (_44_207) with
| (s, args) -> begin
(mk (App ((Var (s), args))))
end))

# 288 "FStar.ToSMT.Term.fst"
let mkNot : term  ->  term = (fun t -> (match (t.tm) with
| App (True, _44_211) -> begin
mkFalse
end
| App (False, _44_216) -> begin
mkTrue
end
| _44_220 -> begin
(mkApp' (Not, (t)::[]))
end))

# 292 "FStar.ToSMT.Term.fst"
let mkAnd : (term * term)  ->  term = (fun _44_223 -> (match (_44_223) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (App (True, _44_226), _44_230) -> begin
t2
end
| (_44_233, App (True, _44_236)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
mkFalse
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' (And, (FStar_List.append ts1 ts2)))
end
| (_44_266, App (And, ts2)) -> begin
(mkApp' (And, (t1)::ts2))
end
| (App (And, ts1), _44_277) -> begin
(mkApp' (And, (FStar_List.append ts1 ((t2)::[]))))
end
| _44_280 -> begin
(mkApp' (And, (t1)::(t2)::[]))
end)
end))

# 301 "FStar.ToSMT.Term.fst"
let mkOr : (term * term)  ->  term = (fun _44_283 -> (match (_44_283) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
mkTrue
end
| (App (False, _44_302), _44_306) -> begin
t2
end
| (_44_309, App (False, _44_312)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' (Or, (FStar_List.append ts1 ts2)))
end
| (_44_326, App (Or, ts2)) -> begin
(mkApp' (Or, (t1)::ts2))
end
| (App (Or, ts1), _44_337) -> begin
(mkApp' (Or, (FStar_List.append ts1 ((t2)::[]))))
end
| _44_340 -> begin
(mkApp' (Or, (t1)::(t2)::[]))
end)
end))

# 310 "FStar.ToSMT.Term.fst"
let mkImp : (term * term)  ->  term = (fun _44_343 -> (match (_44_343) with
| (t1, t2) -> begin
(match ((t1.tm, t2.tm)) with
| (_44_345, App (True, _44_348)) -> begin
mkTrue
end
| (App (True, _44_354), _44_358) -> begin
t2
end
| (_44_361, App (Imp, t1'::t2'::[])) -> begin
(let _123_334 = (let _123_333 = (let _123_332 = (mkAnd (t1, t1'))
in (_123_332)::(t2')::[])
in (Imp, _123_333))
in (mkApp' _123_334))
end
| _44_370 -> begin
(mkApp' (Imp, (t1)::(t2)::[]))
end)
end))

# 316 "FStar.ToSMT.Term.fst"
let mk_bin_op : op  ->  (term * term)  ->  term = (fun op _44_374 -> (match (_44_374) with
| (t1, t2) -> begin
(mkApp' (op, (t1)::(t2)::[]))
end))

# 317 "FStar.ToSMT.Term.fst"
let mkMinus : term  ->  term = (fun t -> (mkApp' (Minus, (t)::[])))

# 318 "FStar.ToSMT.Term.fst"
let mkIff : (term * term)  ->  term = (mk_bin_op Iff)

# 319 "FStar.ToSMT.Term.fst"
let mkEq : (term * term)  ->  term = (mk_bin_op Eq)

# 320 "FStar.ToSMT.Term.fst"
let mkLT : (term * term)  ->  term = (mk_bin_op LT)

# 321 "FStar.ToSMT.Term.fst"
let mkLTE : (term * term)  ->  term = (mk_bin_op LTE)

# 322 "FStar.ToSMT.Term.fst"
let mkGT : (term * term)  ->  term = (mk_bin_op GT)

# 323 "FStar.ToSMT.Term.fst"
let mkGTE : (term * term)  ->  term = (mk_bin_op GTE)

# 324 "FStar.ToSMT.Term.fst"
let mkAdd : (term * term)  ->  term = (mk_bin_op Add)

# 325 "FStar.ToSMT.Term.fst"
let mkSub : (term * term)  ->  term = (mk_bin_op Sub)

# 326 "FStar.ToSMT.Term.fst"
let mkDiv : (term * term)  ->  term = (mk_bin_op Div)

# 327 "FStar.ToSMT.Term.fst"
let mkMul : (term * term)  ->  term = (mk_bin_op Mul)

# 328 "FStar.ToSMT.Term.fst"
let mkMod : (term * term)  ->  term = (mk_bin_op Mod)

# 329 "FStar.ToSMT.Term.fst"
let mkITE : (term * term * term)  ->  term = (fun _44_379 -> (match (_44_379) with
| (t1, t2, t3) -> begin
(match ((t2.tm, t3.tm)) with
| (App (True, _44_382), App (True, _44_387)) -> begin
mkTrue
end
| (App (True, _44_393), _44_397) -> begin
(let _123_355 = (let _123_354 = (mkNot t1)
in (_123_354, t3))
in (mkImp _123_355))
end
| (_44_400, App (True, _44_403)) -> begin
(mkImp (t1, t2))
end
| (_44_408, _44_410) -> begin
(mkApp' (ITE, (t1)::(t2)::(t3)::[]))
end)
end))

# 335 "FStar.ToSMT.Term.fst"
let mkCases : term Prims.list  ->  term = (fun t -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| hd::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd (out, t))) hd tl)
end))

# 339 "FStar.ToSMT.Term.fst"
let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _44_424 -> (match (_44_424) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = 0) then begin
body
end else begin
(match (body.tm) with
| App (True, _44_427) -> begin
body
end
| _44_431 -> begin
(mk (Quant ((qop, pats, wopt, vars, body))))
end)
end
end))

# 348 "FStar.ToSMT.Term.fst"
let abstr : fvs  ->  term  ->  term = (fun fvs t -> (
# 349 "FStar.ToSMT.Term.fst"
let nvars = (FStar_List.length fvs)
in (
# 350 "FStar.ToSMT.Term.fst"
let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + 1)))
end))
in (
# 353 "FStar.ToSMT.Term.fst"
let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _44_446 -> begin
(match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
t
end
| FreeV (x) -> begin
(match ((index_of x)) with
| None -> begin
t
end
| Some (i) -> begin
(mkBoundV (i + ix))
end)
end
| App (op, tms) -> begin
(let _123_373 = (let _123_372 = (FStar_List.map (aux ix) tms)
in (op, _123_372))
in (mkApp' _123_373))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 367 "FStar.ToSMT.Term.fst"
let n = (FStar_List.length vars)
in (let _123_376 = (let _123_375 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _123_374 = (aux (ix + n) body)
in (qop, _123_375, wopt, vars, _123_374)))
in (mkQuant _123_376)))
end)
end))
in (aux 0 t)))))

# 372 "FStar.ToSMT.Term.fst"
let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (
# 373 "FStar.ToSMT.Term.fst"
let n = (FStar_List.length tms)
in (
# 374 "FStar.ToSMT.Term.fst"
let rec aux = (fun shift t -> (match (t.tm) with
| (Integer (_)) | (FreeV (_)) -> begin
t
end
| BoundV (i) -> begin
if ((0 <= (i - shift)) && ((i - shift) < n)) then begin
(FStar_List.nth tms (i - shift))
end else begin
t
end
end
| App (op, tms) -> begin
(let _123_386 = (let _123_385 = (FStar_List.map (aux shift) tms)
in (op, _123_385))
in (mkApp' _123_386))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(
# 383 "FStar.ToSMT.Term.fst"
let m = (FStar_List.length vars)
in (
# 384 "FStar.ToSMT.Term.fst"
let shift = (shift + m)
in (let _123_389 = (let _123_388 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _123_387 = (aux shift body)
in (qop, _123_388, wopt, vars, _123_387)))
in (mkQuant _123_389))))
end))
in (aux 0 t))))

# 388 "FStar.ToSMT.Term.fst"
let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _44_502 -> (match (_44_502) with
| (qop, pats, wopt, vars, body) -> begin
(let _123_395 = (let _123_394 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _123_393 = (FStar_List.map fv_sort vars)
in (let _123_392 = (abstr vars body)
in (qop, _123_394, wopt, _123_393, _123_392))))
in (mkQuant _123_395))
end))

# 389 "FStar.ToSMT.Term.fst"
let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  term = (fun _44_507 -> (match (_44_507) with
| (pats, wopt, sorts, body) -> begin
(mkQuant (Forall, pats, wopt, sorts, body))
end))

# 390 "FStar.ToSMT.Term.fst"
let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  term = (fun _44_512 -> (match (_44_512) with
| (pats, wopt, vars, body) -> begin
(mkQuant' (Forall, pats, wopt, vars, body))
end))

# 393 "FStar.ToSMT.Term.fst"
let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _44_516 -> (match (_44_516) with
| (pats, vars, body) -> begin
(mkQuant' (Forall, pats, None, vars, body))
end))

# 394 "FStar.ToSMT.Term.fst"
let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  term = (fun _44_520 -> (match (_44_520) with
| (pats, vars, body) -> begin
(mkQuant' (Exists, pats, None, vars, body))
end))

# 395 "FStar.ToSMT.Term.fst"
let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _44_526 -> (match (_44_526) with
| (nm, vars, s, tm, c) -> begin
(let _123_408 = (let _123_407 = (FStar_List.map fv_sort vars)
in (let _123_406 = (abstr vars tm)
in (nm, _123_407, s, _123_406, c)))
in DefineFun (_123_408))
end))

# 396 "FStar.ToSMT.Term.fst"
let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _123_411 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _123_411)))

# 397 "FStar.ToSMT.Term.fst"
let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _44_530 id -> (match (_44_530) with
| (tok_name, sort) -> begin
(let _123_424 = (let _123_423 = (let _123_422 = (let _123_421 = (mkInteger' id)
in (let _123_420 = (let _123_419 = (let _123_418 = (constr_id_of_sort sort)
in (let _123_417 = (let _123_416 = (mkApp (tok_name, []))
in (_123_416)::[])
in (_123_418, _123_417)))
in (mkApp _123_419))
in (_123_421, _123_420)))
in (mkEq _123_422))
in (_123_423, Some ("fresh token")))
in Assume (_123_424))
end))

# 400 "FStar.ToSMT.Term.fst"
let constructor_to_decl : constructor_t  ->  decls_t = (fun _44_536 -> (match (_44_536) with
| (name, projectors, sort, id) -> begin
(
# 401 "FStar.ToSMT.Term.fst"
let id = (FStar_Util.string_of_int id)
in (
# 402 "FStar.ToSMT.Term.fst"
let cdecl = (let _123_428 = (let _123_427 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in (name, _123_427, sort, Some ("Constructor")))
in DeclFun (_123_428))
in (
# 403 "FStar.ToSMT.Term.fst"
let n_bvars = (FStar_List.length projectors)
in (
# 404 "FStar.ToSMT.Term.fst"
let bvar_name = (fun i -> (let _123_431 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _123_431)))
in (
# 405 "FStar.ToSMT.Term.fst"
let bvar_index = (fun i -> (n_bvars - (i + 1)))
in (
# 406 "FStar.ToSMT.Term.fst"
let bvar = (fun i s -> (let _123_439 = (let _123_438 = (bvar_name i)
in (_123_438, s))
in (mkFreeV _123_439)))
in (
# 407 "FStar.ToSMT.Term.fst"
let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _44_551 -> (match (_44_551) with
| (_44_549, s) -> begin
(bvar i s)
end))))
in (
# 408 "FStar.ToSMT.Term.fst"
let bvar_names = (FStar_List.map fv_of_term bvars)
in (
# 409 "FStar.ToSMT.Term.fst"
let capp = (mkApp (name, bvars))
in (
# 410 "FStar.ToSMT.Term.fst"
let cid_app = (let _123_443 = (let _123_442 = (constr_id_of_sort sort)
in (_123_442, (capp)::[]))
in (mkApp _123_443))
in (
# 411 "FStar.ToSMT.Term.fst"
let cid = (let _123_449 = (let _123_448 = (let _123_447 = (let _123_446 = (let _123_445 = (let _123_444 = (mkInteger id)
in (_123_444, cid_app))
in (mkEq _123_445))
in (((capp)::[])::[], bvar_names, _123_446))
in (mkForall _123_447))
in (_123_448, Some ("Constructor distinct")))
in Assume (_123_449))
in (
# 412 "FStar.ToSMT.Term.fst"
let disc_name = (Prims.strcat "is-" name)
in (
# 413 "FStar.ToSMT.Term.fst"
let xfv = ("x", sort)
in (
# 414 "FStar.ToSMT.Term.fst"
let xx = (mkFreeV xfv)
in (
# 415 "FStar.ToSMT.Term.fst"
let disc_eq = (let _123_454 = (let _123_453 = (let _123_451 = (let _123_450 = (constr_id_of_sort sort)
in (_123_450, (xx)::[]))
in (mkApp _123_451))
in (let _123_452 = (mkInteger id)
in (_123_453, _123_452)))
in (mkEq _123_454))
in (
# 416 "FStar.ToSMT.Term.fst"
let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _44_563 -> (match (_44_563) with
| (proj, s) -> begin
(mkApp (proj, (xx)::[]))
end))))
in (
# 417 "FStar.ToSMT.Term.fst"
let disc_inv_body = (let _123_457 = (let _123_456 = (mkApp (name, proj_terms))
in (xx, _123_456))
in (mkEq _123_457))
in (
# 418 "FStar.ToSMT.Term.fst"
let disc_ax = (mkAnd (disc_eq, disc_inv_body))
in (
# 419 "FStar.ToSMT.Term.fst"
let disc = (mkDefineFun (disc_name, (xfv)::[], Bool_sort, disc_ax, Some ("Discriminator definition")))
in (
# 422 "FStar.ToSMT.Term.fst"
let projs = (let _123_468 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _44_571 -> (match (_44_571) with
| (name, s) -> begin
(
# 423 "FStar.ToSMT.Term.fst"
let cproj_app = (mkApp (name, (capp)::[]))
in (let _123_467 = (let _123_466 = (let _123_465 = (let _123_464 = (let _123_463 = (let _123_462 = (let _123_461 = (let _123_460 = (bvar i s)
in (cproj_app, _123_460))
in (mkEq _123_461))
in (((capp)::[])::[], bvar_names, _123_462))
in (mkForall _123_463))
in (_123_464, Some ("Projection inverse")))
in Assume (_123_465))
in (_123_466)::[])
in (DeclFun ((name, (sort)::[], s, Some ("Projector"))))::_123_467))
end))))
in (FStar_All.pipe_right _123_468 FStar_List.flatten))
in (let _123_475 = (let _123_471 = (let _123_470 = (let _123_469 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_123_469))
in (_123_470)::(cdecl)::(cid)::projs)
in (FStar_List.append _123_471 ((disc)::[])))
in (let _123_474 = (let _123_473 = (let _123_472 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_123_472))
in (_123_473)::[])
in (FStar_List.append _123_475 _123_474)))))))))))))))))))))))
end))

# 432 "FStar.ToSMT.Term.fst"
let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (
# 433 "FStar.ToSMT.Term.fst"
let _44_593 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _44_580 s -> (match (_44_580) with
| (names, binders, n) -> begin
(
# 434 "FStar.ToSMT.Term.fst"
let prefix = (match (s) with
| Type_sort -> begin
"@a"
end
| Term_sort -> begin
"@x"
end
| _44_585 -> begin
"@u"
end)
in (
# 438 "FStar.ToSMT.Term.fst"
let nm = (let _123_484 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _123_484))
in (
# 439 "FStar.ToSMT.Term.fst"
let names = ((nm, s))::names
in (
# 440 "FStar.ToSMT.Term.fst"
let b = (let _123_485 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _123_485))
in (names, (b)::binders, (n + 1))))))
end)) (outer_names, [], start)))
in (match (_44_593) with
| (names, binders, n) -> begin
(names, (FStar_List.rev binders), n)
end)))

# 445 "FStar.ToSMT.Term.fst"
let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (
# 446 "FStar.ToSMT.Term.fst"
let _44_598 = (name_binders_inner [] 0 sorts)
in (match (_44_598) with
| (names, binders, n) -> begin
((FStar_List.rev names), binders)
end)))

# 449 "FStar.ToSMT.Term.fst"
let termToSmt : term  ->  Prims.string = (fun t -> (
# 450 "FStar.ToSMT.Term.fst"
let rec aux = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _123_496 = (FStar_List.nth names i)
in (FStar_All.pipe_right _123_496 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _123_498 = (let _123_497 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _123_497 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _123_498))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(
# 458 "FStar.ToSMT.Term.fst"
let _44_628 = (name_binders_inner names n sorts)
in (match (_44_628) with
| (names, binders, n) -> begin
(
# 459 "FStar.ToSMT.Term.fst"
let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (
# 460 "FStar.ToSMT.Term.fst"
let pats_str = (match (pats) with
| ([]::[]) | ([]) -> begin
""
end
| _44_634 -> begin
(let _123_504 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _123_503 = (let _123_502 = (FStar_List.map (fun p -> (let _123_501 = (aux n names p)
in (FStar_Util.format1 "%s" _123_501))) pats)
in (FStar_String.concat " " _123_502))
in (FStar_Util.format1 "\n:pattern (%s)" _123_503)))))
in (FStar_All.pipe_right _123_504 (FStar_String.concat "\n")))
end)
in (match ((pats, wopt)) with
| (([]::[], None)) | (([], None)) -> begin
(let _123_505 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _123_505))
end
| _44_646 -> begin
(let _123_507 = (aux n names body)
in (let _123_506 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _123_507 _123_506 pats_str)))
end)))
end))
end))
in (aux 0 [] t)))

# 472 "FStar.ToSMT.Term.fst"
let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _44_6 -> (match (_44_6) with
| None -> begin
""
end
| Some (c) -> begin
(
# 475 "FStar.ToSMT.Term.fst"
let _44_653 = (FStar_Util.splitlines c)
in (match (_44_653) with
| hd::tl -> begin
(
# 476 "FStar.ToSMT.Term.fst"
let suffix = (match (tl) with
| [] -> begin
""
end
| _44_656 -> begin
"..."
end)
in (FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix))
end))
end))

# 481 "FStar.ToSMT.Term.fst"
let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _123_516 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _44_7 -> (match (_44_7) with
| [] -> begin
""
end
| h::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _123_516))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(
# 486 "FStar.ToSMT.Term.fst"
let l = (FStar_List.map strSort argsorts)
in (let _123_518 = (caption_to_string c)
in (let _123_517 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _123_518 f (FStar_String.concat " " l) _123_517))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(
# 489 "FStar.ToSMT.Term.fst"
let _44_684 = (name_binders arg_sorts)
in (match (_44_684) with
| (names, binders) -> begin
(
# 490 "FStar.ToSMT.Term.fst"
let body = (let _123_519 = (FStar_List.map mkFreeV names)
in (inst _123_519 body))
in (let _123_522 = (caption_to_string c)
in (let _123_521 = (strSort retsort)
in (let _123_520 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _123_522 f (FStar_String.concat " " binders) _123_521 _123_520)))))
end))
end
| Assume (t, c) -> begin
(let _123_524 = (caption_to_string c)
in (let _123_523 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _123_524 _123_523)))
end
| Eval (t) -> begin
(let _123_525 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _123_525))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| CheckSat -> begin
"(check-sat)"
end
| Push -> begin
"(push)"
end
| Pop -> begin
"(pop)"
end))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (
# 503 "FStar.ToSMT.Term.fst"
let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort String)\n(declare-fun String_constr_id (String) Int)\n\n(declare-sort Kind)\n(declare-fun Kind_constr_id (Kind) Int)\n\n(declare-sort Type)\n(declare-fun Type_constr_id (Type) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreKind (Type) Kind)\n(declare-fun PreType (Term) Type)\n(declare-fun Valid (Type) Bool)\n(declare-fun HasKind (Type Kind) Bool)\n(declare-fun HasTypeFuel (Fuel Term Type) Bool)\n(define-fun HasTypeZ ((x Term) (t Type)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Type)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Type))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Type)) (HasTypeZ x t)))\n(declare-fun ApplyEF (Term Fuel) Term)\n(declare-fun ApplyEE (Term Term) Term)\n(declare-fun ApplyET (Term Type) Term)\n(declare-fun ApplyTE (Type Term) Type)\n(declare-fun ApplyTT (Type Type) Type)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsType (Type Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Type)\n(assert (forall ((t Type))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type\n(Precedes t1 t2))\n")
in (
# 560 "FStar.ToSMT.Term.fst"
let constrs = (("String_const", (("String_const_proj_0", Int_sort))::[], String_sort, 0))::(("Kind_type", [], Kind_sort, 0))::(("Kind_arrow", (("Kind_arrow_id", Int_sort))::[], Kind_sort, 1))::(("Kind_uvar", (("Kind_uvar_fst", Int_sort))::[], Kind_sort, 2))::(("Typ_fun", (("Typ_fun_id", Int_sort))::[], Type_sort, 1))::(("Typ_app", (("Typ_app_fst", Type_sort))::(("Typ_app_snd", Type_sort))::[], Type_sort, 2))::(("Typ_dep", (("Typ_dep_fst", Type_sort))::(("Typ_dep_snd", Term_sort))::[], Type_sort, 3))::(("Typ_uvar", (("Typ_uvar_fst", Int_sort))::[], Type_sort, 4))::(("Term_unit", [], Term_sort, 0))::(("BoxInt", (("BoxInt_proj_0", Int_sort))::[], Term_sort, 1))::(("BoxBool", (("BoxBool_proj_0", Bool_sort))::[], Term_sort, 2))::(("BoxString", (("BoxString_proj_0", String_sort))::[], Term_sort, 3))::(("BoxRef", (("BoxRef_proj_0", Ref_sort))::[], Term_sort, 4))::(("Exp_uvar", (("Exp_uvar_fst", Int_sort))::[], Term_sort, 5))::(("LexCons", (("LexCons_0", Term_sort))::(("LexCons_1", Term_sort))::[], Term_sort, 6))::[]
in (
# 577 "FStar.ToSMT.Term.fst"
let bcons = (let _123_528 = (let _123_527 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _123_527 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _123_528 (FStar_String.concat "\n")))
in (
# 578 "FStar.ToSMT.Term.fst"
let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat (Prims.strcat basic bcons) lex_ordering))))))

# 587 "FStar.ToSMT.Term.fst"
let mk_Kind_type : term = (mkApp ("Kind_type", []))

# 588 "FStar.ToSMT.Term.fst"
let mk_Kind_uvar : Prims.int  ->  term = (fun i -> (let _123_533 = (let _123_532 = (let _123_531 = (mkInteger' i)
in (_123_531)::[])
in ("Kind_uvar", _123_532))
in (mkApp _123_533)))

# 589 "FStar.ToSMT.Term.fst"
let mk_Typ_app : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Typ_app", (t1)::(t2)::[])))

# 590 "FStar.ToSMT.Term.fst"
let mk_Typ_dep : term  ->  term  ->  term = (fun t1 t2 -> (mkApp ("Typ_dep", (t1)::(t2)::[])))

# 591 "FStar.ToSMT.Term.fst"
let mk_Typ_uvar : Prims.int  ->  term = (fun i -> (let _123_546 = (let _123_545 = (let _123_544 = (mkInteger' i)
in (_123_544)::[])
in ("Typ_uvar", _123_545))
in (mkApp _123_546)))

# 592 "FStar.ToSMT.Term.fst"
let mk_Exp_uvar : Prims.int  ->  term = (fun i -> (let _123_551 = (let _123_550 = (let _123_549 = (mkInteger' i)
in (_123_549)::[])
in ("Exp_uvar", _123_550))
in (mkApp _123_551)))

# 594 "FStar.ToSMT.Term.fst"
let mk_Term_unit : term = (mkApp ("Term_unit", []))

# 595 "FStar.ToSMT.Term.fst"
let boxInt : term  ->  term = (fun t -> (mkApp ("BoxInt", (t)::[])))

# 596 "FStar.ToSMT.Term.fst"
let unboxInt : term  ->  term = (fun t -> (mkApp ("BoxInt_proj_0", (t)::[])))

# 597 "FStar.ToSMT.Term.fst"
let boxBool : term  ->  term = (fun t -> (mkApp ("BoxBool", (t)::[])))

# 598 "FStar.ToSMT.Term.fst"
let unboxBool : term  ->  term = (fun t -> (mkApp ("BoxBool_proj_0", (t)::[])))

# 599 "FStar.ToSMT.Term.fst"
let boxString : term  ->  term = (fun t -> (mkApp ("BoxString", (t)::[])))

# 600 "FStar.ToSMT.Term.fst"
let unboxString : term  ->  term = (fun t -> (mkApp ("BoxString_proj_0", (t)::[])))

# 601 "FStar.ToSMT.Term.fst"
let boxRef : term  ->  term = (fun t -> (mkApp ("BoxRef", (t)::[])))

# 602 "FStar.ToSMT.Term.fst"
let unboxRef : term  ->  term = (fun t -> (mkApp ("BoxRef_proj_0", (t)::[])))

# 603 "FStar.ToSMT.Term.fst"
let boxTerm : sort  ->  term  ->  term = (fun sort t -> (match (sort) with
| Int_sort -> begin
(boxInt t)
end
| Bool_sort -> begin
(boxBool t)
end
| String_sort -> begin
(boxString t)
end
| Ref_sort -> begin
(boxRef t)
end
| _44_724 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 609 "FStar.ToSMT.Term.fst"
let unboxTerm : sort  ->  term  ->  term = (fun sort t -> (match (sort) with
| Int_sort -> begin
(unboxInt t)
end
| Bool_sort -> begin
(unboxBool t)
end
| String_sort -> begin
(unboxString t)
end
| Ref_sort -> begin
(unboxRef t)
end
| _44_732 -> begin
(Prims.raise FStar_Util.Impos)
end))

# 616 "FStar.ToSMT.Term.fst"
let mk_PreKind : term  ->  term = (fun t -> (mkApp ("PreKind", (t)::[])))

# 617 "FStar.ToSMT.Term.fst"
let mk_PreType : term  ->  term = (fun t -> (mkApp ("PreType", (t)::[])))

# 618 "FStar.ToSMT.Term.fst"
let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Equality"), _44_747::t1::t2::[]); hash = _44_741; freevars = _44_739}::[]) -> begin
(mkEq (t1, t2))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_disEquality"), _44_766::t1::t2::[]); hash = _44_760; freevars = _44_758}::[]) -> begin
(let _123_582 = (mkEq (t1, t2))
in (mkNot _123_582))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThanOrEqual"), t1::t2::[]); hash = _44_779; freevars = _44_777}::[]) -> begin
(let _123_585 = (let _123_584 = (unboxInt t1)
in (let _123_583 = (unboxInt t2)
in (_123_584, _123_583)))
in (mkLTE _123_585))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_LessThan"), t1::t2::[]); hash = _44_796; freevars = _44_794}::[]) -> begin
(let _123_588 = (let _123_587 = (unboxInt t1)
in (let _123_586 = (unboxInt t2)
in (_123_587, _123_586)))
in (mkLT _123_588))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThanOrEqual"), t1::t2::[]); hash = _44_813; freevars = _44_811}::[]) -> begin
(let _123_591 = (let _123_590 = (unboxInt t1)
in (let _123_589 = (unboxInt t2)
in (_123_590, _123_589)))
in (mkGTE _123_591))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_GreaterThan"), t1::t2::[]); hash = _44_830; freevars = _44_828}::[]) -> begin
(let _123_594 = (let _123_593 = (unboxInt t1)
in (let _123_592 = (unboxInt t2)
in (_123_593, _123_592)))
in (mkGT _123_594))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_AmpAmp"), t1::t2::[]); hash = _44_847; freevars = _44_845}::[]) -> begin
(let _123_597 = (let _123_596 = (unboxBool t1)
in (let _123_595 = (unboxBool t2)
in (_123_596, _123_595)))
in (mkAnd _123_597))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_BarBar"), t1::t2::[]); hash = _44_864; freevars = _44_862}::[]) -> begin
(let _123_600 = (let _123_599 = (unboxBool t1)
in (let _123_598 = (unboxBool t2)
in (_123_599, _123_598)))
in (mkOr _123_600))
end
| App (Var ("Prims.b2t"), {tm = App (Var ("Prims.op_Negation"), t::[]); hash = _44_881; freevars = _44_879}::[]) -> begin
(let _123_601 = (unboxBool t)
in (mkNot _123_601))
end
| App (Var ("Prims.b2t"), t::[]) -> begin
(unboxBool t)
end
| _44_899 -> begin
(mkApp ("Valid", (t)::[]))
end))

# 630 "FStar.ToSMT.Term.fst"
let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp ("HasType", (v)::(t)::[])))

# 631 "FStar.ToSMT.Term.fst"
let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp ("HasTypeZ", (v)::(t)::[])))

# 632 "FStar.ToSMT.Term.fst"
let mk_IsTyped : term  ->  term = (fun v -> (mkApp ("IsTyped", (v)::[])))

# 633 "FStar.ToSMT.Term.fst"
let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(mk_HasType v t)
end else begin
(mkApp ("HasTypeFuel", (f)::(v)::(t)::[]))
end)

# 637 "FStar.ToSMT.Term.fst"
let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))

# 640 "FStar.ToSMT.Term.fst"
let mk_Destruct : term  ->  term = (fun v -> (mkApp ("Destruct", (v)::[])))

# 641 "FStar.ToSMT.Term.fst"
let mk_HasKind : term  ->  term  ->  term = (fun t k -> (mkApp ("HasKind", (t)::(k)::[])))

# 642 "FStar.ToSMT.Term.fst"
let mk_Rank : term  ->  term = (fun x -> (mkApp ("Rank", (x)::[])))

# 643 "FStar.ToSMT.Term.fst"
let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp ((Prims.strcat "is-" n), (t)::[])))

# 644 "FStar.ToSMT.Term.fst"
let mk_ApplyTE : term  ->  term  ->  term = (fun t e -> (mkApp ("ApplyTE", (t)::(e)::[])))

# 645 "FStar.ToSMT.Term.fst"
let mk_ApplyTT : term  ->  term  ->  term = (fun t t' -> (mkApp ("ApplyTT", (t)::(t')::[])))

# 646 "FStar.ToSMT.Term.fst"
let mk_ApplyET : term  ->  term  ->  term = (fun e t -> (mkApp ("ApplyET", (e)::(t)::[])))

# 647 "FStar.ToSMT.Term.fst"
let mk_ApplyEE : term  ->  term  ->  term = (fun e e' -> (mkApp ("ApplyEE", (e)::(e')::[])))

# 648 "FStar.ToSMT.Term.fst"
let mk_ApplyEF : term  ->  term  ->  term = (fun e f -> (mkApp ("ApplyEF", (e)::(f)::[])))

# 649 "FStar.ToSMT.Term.fst"
let mk_String_const : Prims.int  ->  term = (fun i -> (let _123_660 = (let _123_659 = (let _123_658 = (mkInteger' i)
in (_123_658)::[])
in ("String_const", _123_659))
in (mkApp _123_660)))

# 650 "FStar.ToSMT.Term.fst"
let mk_Precedes : term  ->  term  ->  term = (fun x1 x2 -> (let _123_665 = (mkApp ("Precedes", (x1)::(x2)::[]))
in (FStar_All.pipe_right _123_665 mk_Valid)))

# 651 "FStar.ToSMT.Term.fst"
let mk_LexCons : term  ->  term  ->  term = (fun x1 x2 -> (mkApp ("LexCons", (x1)::(x2)::[])))

# 652 "FStar.ToSMT.Term.fst"
let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = 0) then begin
(mkApp ("ZFuel", []))
end else begin
(let _123_674 = (let _123_673 = (let _123_672 = (n_fuel (n - 1))
in (_123_672)::[])
in ("SFuel", _123_673))
in (mkApp _123_674))
end)

# 655 "FStar.ToSMT.Term.fst"
let fuel_2 : term = (n_fuel 2)

# 656 "FStar.ToSMT.Term.fst"
let fuel_100 : term = (n_fuel 100)

# 658 "FStar.ToSMT.Term.fst"
let mk_and_opt : term Prims.option  ->  term Prims.option  ->  term Prims.option = (fun p1 p2 -> (match ((p1, p2)) with
| (Some (p1), Some (p2)) -> begin
(let _123_679 = (mkAnd (p1, p2))
in Some (_123_679))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))

# 664 "FStar.ToSMT.Term.fst"
let mk_and_opt_l : term Prims.option Prims.list  ->  term Prims.option = (fun pl -> (FStar_List.fold_left (fun out p -> (mk_and_opt p out)) None pl))

# 667 "FStar.ToSMT.Term.fst"
let mk_and_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkTrue
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkAnd (p1, p2))) hd tl)
end))

# 671 "FStar.ToSMT.Term.fst"
let mk_or_l : term Prims.list  ->  term = (fun l -> (match (l) with
| [] -> begin
mkFalse
end
| hd::tl -> begin
(FStar_List.fold_left (fun p1 p2 -> (mkOr (p1, p2))) hd tl)
end))

# 676 "FStar.ToSMT.Term.fst"
let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "Integer %s" n)
end
| BoundV (n) -> begin
(let _123_696 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "BoundV %s" _123_696))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "FreeV %s" (Prims.fst fv))
end
| App (op, l) -> begin
(let _123_697 = (print_smt_term_list l)
in (FStar_Util.format2 "App %s [ %s ]" (op_to_string op) _123_697))
end
| Quant (qop, l, _44_984, _44_986, t) -> begin
(let _123_699 = (print_smt_term_list_list l)
in (let _123_698 = (print_smt_term t)
in (FStar_Util.format3 "Quant %s %s %s" (qop_to_string qop) _123_699 _123_698)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s t -> (let _123_703 = (print_smt_term t)
in (Prims.strcat (Prims.strcat s "; ") _123_703))) "" l))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _123_708 = (let _123_707 = (print_smt_term_list l)
in (Prims.strcat (Prims.strcat s "; [ ") _123_707))
in (Prims.strcat _123_708 " ] "))) "" l))




