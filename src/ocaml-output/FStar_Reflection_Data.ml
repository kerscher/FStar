open Prims
type name = Prims.string Prims.list[@@deriving show]
type typ = FStar_Syntax_Syntax.term[@@deriving show]
type binders = FStar_Syntax_Syntax.binder Prims.list[@@deriving show]
type vconst =
  | C_Unit 
  | C_Int of FStar_BigInt.t 
  | C_True 
  | C_False 
  | C_String of Prims.string [@@deriving show]
let (uu___is_C_Unit : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____16 -> false
  
let (uu___is_C_Int : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____21 -> false
  
let (__proj__C_Int__item___0 : vconst -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | C_Int _0 -> _0 
let (uu___is_C_True : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_True  -> true | uu____32 -> false
  
let (uu___is_C_False : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_False  -> true | uu____36 -> false
  
let (uu___is_C_String : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_String _0 -> true | uu____41 -> false
  
let (__proj__C_String__item___0 : vconst -> Prims.string) =
  fun projectee  -> match projectee with | C_String _0 -> _0 
type pattern =
  | Pat_Constant of vconst 
  | Pat_Cons of (FStar_Syntax_Syntax.fv,pattern Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Pat_Var of FStar_Syntax_Syntax.bv 
  | Pat_Wild of FStar_Syntax_Syntax.bv [@@deriving show]
let (uu___is_Pat_Constant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Constant _0 -> true | uu____75 -> false
  
let (__proj__Pat_Constant__item___0 : pattern -> vconst) =
  fun projectee  -> match projectee with | Pat_Constant _0 -> _0 
let (uu___is_Pat_Cons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Cons _0 -> true | uu____93 -> false
  
let (__proj__Pat_Cons__item___0 :
  pattern ->
    (FStar_Syntax_Syntax.fv,pattern Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Pat_Cons _0 -> _0 
let (uu___is_Pat_Var : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Var _0 -> true | uu____123 -> false
  
let (__proj__Pat_Var__item___0 : pattern -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Pat_Var _0 -> _0 
let (uu___is_Pat_Wild : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Wild _0 -> true | uu____135 -> false
  
let (__proj__Pat_Wild__item___0 : pattern -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Pat_Wild _0 -> _0 
type branch =
  (pattern,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
type aqualv =
  | Q_Implicit 
  | Q_Explicit [@@deriving show]
let (uu___is_Q_Implicit : aqualv -> Prims.bool) =
  fun projectee  ->
    match projectee with | Q_Implicit  -> true | uu____150 -> false
  
let (uu___is_Q_Explicit : aqualv -> Prims.bool) =
  fun projectee  ->
    match projectee with | Q_Explicit  -> true | uu____154 -> false
  
type argv = (FStar_Syntax_Syntax.term,aqualv) FStar_Pervasives_Native.tuple2
[@@deriving show]
type term_view =
  | Tv_Var of FStar_Syntax_Syntax.binder 
  | Tv_FVar of FStar_Syntax_Syntax.fv 
  | Tv_App of (FStar_Syntax_Syntax.term,argv) FStar_Pervasives_Native.tuple2
  
  | Tv_Abs of (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | Tv_Arrow of (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
  FStar_Pervasives_Native.tuple2 
  | Tv_Type of Prims.unit 
  | Tv_Refine of (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | Tv_Const of vconst 
  | Tv_Uvar of (FStar_BigInt.t,typ) FStar_Pervasives_Native.tuple2 
  | Tv_Let of
  (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple3 
  | Tv_Match of (FStar_Syntax_Syntax.term,branch Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Tv_Unknown [@@deriving show]
let (uu___is_Tv_Var : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____239 -> false
  
let (__proj__Tv_Var__item___0 : term_view -> FStar_Syntax_Syntax.binder) =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0 
let (uu___is_Tv_FVar : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____251 -> false
  
let (__proj__Tv_FVar__item___0 : term_view -> FStar_Syntax_Syntax.fv) =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0 
let (uu___is_Tv_App : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____267 -> false
  
let (__proj__Tv_App__item___0 :
  term_view -> (FStar_Syntax_Syntax.term,argv) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_App _0 -> _0 
let (uu___is_Tv_Abs : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____295 -> false
  
let (__proj__Tv_Abs__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_Abs _0 -> _0 
let (uu___is_Tv_Arrow : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____323 -> false
  
let (__proj__Tv_Arrow__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_Arrow _0 -> _0 
let (uu___is_Tv_Type : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____347 -> false
  
let (__proj__Tv_Type__item___0 : term_view -> Prims.unit) =
  fun projectee  -> () 
let (uu___is_Tv_Refine : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____363 -> false
  
let (__proj__Tv_Refine__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_Refine _0 -> _0 
let (uu___is_Tv_Const : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____387 -> false
  
let (__proj__Tv_Const__item___0 : term_view -> vconst) =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0 
let (uu___is_Tv_Uvar : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Uvar _0 -> true | uu____403 -> false
  
let (__proj__Tv_Uvar__item___0 :
  term_view -> (FStar_BigInt.t,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Tv_Uvar _0 -> _0 
let (uu___is_Tv_Let : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Let _0 -> true | uu____433 -> false
  
let (__proj__Tv_Let__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Tv_Let _0 -> _0 
let (uu___is_Tv_Match : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Match _0 -> true | uu____469 -> false
  
let (__proj__Tv_Match__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.term,branch Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_Match _0 -> _0 
let (uu___is_Tv_Unknown : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Unknown  -> true | uu____498 -> false
  
type comp_view =
  | C_Total of typ 
  | C_Lemma of (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C_Unknown [@@deriving show]
let (uu___is_C_Total : comp_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Total _0 -> true | uu____515 -> false
  
let (__proj__C_Total__item___0 : comp_view -> typ) =
  fun projectee  -> match projectee with | C_Total _0 -> _0 
let (uu___is_C_Lemma : comp_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Lemma _0 -> true | uu____531 -> false
  
let (__proj__C_Lemma__item___0 :
  comp_view ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | C_Lemma _0 -> _0 
let (uu___is_C_Unknown : comp_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Unknown  -> true | uu____554 -> false
  
type ctor =
  | Ctor of (name,typ) FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Ctor : ctor -> Prims.bool) = fun projectee  -> true 
let (__proj__Ctor__item___0 :
  ctor -> (name,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Ctor _0 -> _0 
type sigelt_view =
  | Sg_Inductive of
  (name,FStar_Syntax_Syntax.binder Prims.list,typ,ctor Prims.list)
  FStar_Pervasives_Native.tuple4 
  | Sg_Let of (FStar_Syntax_Syntax.fv,typ,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple3 
  | Unk [@@deriving show]
let (uu___is_Sg_Inductive : sigelt_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sg_Inductive _0 -> true | uu____624 -> false
  
let (__proj__Sg_Inductive__item___0 :
  sigelt_view ->
    (name,FStar_Syntax_Syntax.binder Prims.list,typ,ctor Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Sg_Inductive _0 -> _0 
let (uu___is_Sg_Let : sigelt_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sg_Let _0 -> true | uu____678 -> false
  
let (__proj__Sg_Let__item___0 :
  sigelt_view ->
    (FStar_Syntax_Syntax.fv,typ,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Sg_Let _0 -> _0 
let (uu___is_Unk : sigelt_view -> Prims.bool) =
  fun projectee  -> match projectee with | Unk  -> true | uu____707 -> false 
type refl_constant = {
  lid: FStar_Ident.lid ;
  t: FStar_Syntax_Syntax.term }[@@deriving show]
let (__proj__Mkrefl_constant__item__lid : refl_constant -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with
    | { lid = __fname__lid; t = __fname__t;_} -> __fname__lid
  
let (__proj__Mkrefl_constant__item__t :
  refl_constant -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { lid = __fname__lid; t = __fname__t;_} -> __fname__t
  
type expr =
  | Lit of FStar_BigInt.t 
  | Atom of (FStar_BigInt.t,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | Plus of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Mult of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Minus of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Land of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Lxor of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Lor of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Ladd of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Lsub of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Shl of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Shr of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Neg of expr 
  | Udiv of (expr,expr) FStar_Pervasives_Native.tuple2 
  | Umod of (expr,expr) FStar_Pervasives_Native.tuple2 
  | MulMod of (expr,expr) FStar_Pervasives_Native.tuple2 
  | NatToBv of expr [@@deriving show]
let (uu___is_Lit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lit _0 -> true | uu____854 -> false
  
let (__proj__Lit__item___0 : expr -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Lit _0 -> _0 
let (uu___is_Atom : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Atom _0 -> true | uu____870 -> false
  
let (__proj__Atom__item___0 :
  expr ->
    (FStar_BigInt.t,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Atom _0 -> _0 
let (uu___is_Plus : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plus _0 -> true | uu____898 -> false
  
let (__proj__Plus__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Plus _0 -> _0 
let (uu___is_Mult : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult _0 -> true | uu____926 -> false
  
let (__proj__Mult__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Mult _0 -> _0 
let (uu___is_Minus : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Minus _0 -> true | uu____954 -> false
  
let (__proj__Minus__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Minus _0 -> _0 
let (uu___is_Land : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Land _0 -> true | uu____982 -> false
  
let (__proj__Land__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Land _0 -> _0 
let (uu___is_Lxor : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lxor _0 -> true | uu____1010 -> false
  
let (__proj__Lxor__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Lxor _0 -> _0 
let (uu___is_Lor : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lor _0 -> true | uu____1038 -> false
  
let (__proj__Lor__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Lor _0 -> _0 
let (uu___is_Ladd : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Ladd _0 -> true | uu____1066 -> false
  
let (__proj__Ladd__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Ladd _0 -> _0 
let (uu___is_Lsub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lsub _0 -> true | uu____1094 -> false
  
let (__proj__Lsub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Lsub _0 -> _0 
let (uu___is_Shl : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Shl _0 -> true | uu____1122 -> false
  
let (__proj__Shl__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Shl _0 -> _0 
let (uu___is_Shr : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Shr _0 -> true | uu____1150 -> false
  
let (__proj__Shr__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Shr _0 -> _0 
let (uu___is_Neg : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Neg _0 -> true | uu____1174 -> false
  
let (__proj__Neg__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | Neg _0 -> _0 
let (uu___is_Udiv : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Udiv _0 -> true | uu____1190 -> false
  
let (__proj__Udiv__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Udiv _0 -> _0 
let (uu___is_Umod : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | Umod _0 -> true | uu____1218 -> false
  
let (__proj__Umod__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Umod _0 -> _0 
let (uu___is_MulMod : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | MulMod _0 -> true | uu____1246 -> false
  
let (__proj__MulMod__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | MulMod _0 -> _0 
let (uu___is_NatToBv : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | NatToBv _0 -> true | uu____1270 -> false
  
let (__proj__NatToBv__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | NatToBv _0 -> _0 
let (fstar_refl_lid : Prims.string Prims.list -> FStar_Ident.lident) =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Reflection"] s)
      FStar_Range.dummyRange
  
let (fstar_refl_basic_lid : Prims.string -> FStar_Ident.lident) =
  fun s  -> fstar_refl_lid ["Basic"; s] 
let (fstar_refl_syntax_lid : Prims.string -> FStar_Ident.lident) =
  fun s  -> fstar_refl_lid ["Syntax"; s] 
let (fstar_refl_types_lid : Prims.string -> FStar_Ident.lident) =
  fun s  -> fstar_refl_lid ["Types"; s] 
let (fstar_refl_data_lid : Prims.string -> FStar_Ident.lident) =
  fun s  -> fstar_refl_lid ["Data"; s] 
let (fstar_refl_data_const : Prims.string -> refl_constant) =
  fun s  ->
    let lid = fstar_refl_data_lid s  in
    let uu____1301 = FStar_Syntax_Syntax.tdataconstr lid  in
    { lid; t = uu____1301 }
  
let (mk_refl_types_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____1305 = fstar_refl_types_lid s  in
    FStar_Syntax_Syntax.tconst uu____1305
  
let (mk_refl_syntax_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____1309 = fstar_refl_syntax_lid s  in
    FStar_Syntax_Syntax.tconst uu____1309
  
let (mk_refl_data_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____1313 = fstar_refl_data_lid s  in
    FStar_Syntax_Syntax.tconst uu____1313
  
let (fstar_refl_inspect_lid : FStar_Ident.lident) =
  fstar_refl_basic_lid "inspect" 
let (fstar_refl_inspect : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar fstar_refl_inspect_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (fstar_refl_pack_lid : FStar_Ident.lident) = fstar_refl_basic_lid "pack" 
let (fstar_refl_pack : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar fstar_refl_pack_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (fstar_refl_pack_fv_lid : FStar_Ident.lident) =
  fstar_refl_basic_lid "pack_fv" 
let (fstar_refl_pack_fv : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar fstar_refl_pack_fv_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (fstar_refl_aqualv : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "aqualv" 
let (fstar_refl_env : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "env" 
let (fstar_refl_fv : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "fv" 
let (fstar_refl_comp : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "comp" 
let (fstar_refl_comp_view : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "comp_view" 
let (fstar_refl_binder : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "binder" 
let (fstar_refl_term_view : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "term_view" 
let (fstar_refl_ctor : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "ctor" 
let (fstar_refl_pattern : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "pattern" 
let (fstar_refl_branch : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "branch" 
let (ref_Q_Explicit : refl_constant) = fstar_refl_data_const "Q_Explicit" 
let (ref_Q_Implicit : refl_constant) = fstar_refl_data_const "Q_Implicit" 
let (ref_C_Unit : refl_constant) = fstar_refl_data_const "C_Unit" 
let (ref_C_True : refl_constant) = fstar_refl_data_const "C_True" 
let (ref_C_False : refl_constant) = fstar_refl_data_const "C_False" 
let (ref_C_Int : refl_constant) = fstar_refl_data_const "C_Int" 
let (ref_C_String : refl_constant) = fstar_refl_data_const "C_String" 
let (ref_Pat_Constant : refl_constant) = fstar_refl_data_const "Pat_Constant" 
let (ref_Pat_Cons : refl_constant) = fstar_refl_data_const "Pat_Cons" 
let (ref_Pat_Var : refl_constant) = fstar_refl_data_const "Pat_Var" 
let (ref_Pat_Wild : refl_constant) = fstar_refl_data_const "Pat_Wild" 
let (ref_Tv_Var : refl_constant) = fstar_refl_data_const "Tv_Var" 
let (ref_Tv_FVar : refl_constant) = fstar_refl_data_const "Tv_FVar" 
let (ref_Tv_App : refl_constant) = fstar_refl_data_const "Tv_App" 
let (ref_Tv_Abs : refl_constant) = fstar_refl_data_const "Tv_Abs" 
let (ref_Tv_Arrow : refl_constant) = fstar_refl_data_const "Tv_Arrow" 
let (ref_Tv_Type : refl_constant) = fstar_refl_data_const "Tv_Type" 
let (ref_Tv_Refine : refl_constant) = fstar_refl_data_const "Tv_Refine" 
let (ref_Tv_Const : refl_constant) = fstar_refl_data_const "Tv_Const" 
let (ref_Tv_Uvar : refl_constant) = fstar_refl_data_const "Tv_Uvar" 
let (ref_Tv_Let : refl_constant) = fstar_refl_data_const "Tv_Let" 
let (ref_Tv_Match : refl_constant) = fstar_refl_data_const "Tv_Match" 
let (ref_Tv_Unknown : refl_constant) = fstar_refl_data_const "Tv_Unknown" 
let (ref_C_Total : refl_constant) = fstar_refl_data_const "C_Total" 
let (ref_C_Lemma : refl_constant) = fstar_refl_data_const "C_Lemma" 
let (ref_C_Unknown : refl_constant) = fstar_refl_data_const "C_Unknown" 
let (ref_Sg_Inductive : refl_constant) = fstar_refl_data_const "Sg_Inductive" 
let (ref_Sg_Let : refl_constant) = fstar_refl_data_const "Sg_Let" 
let (ref_Unk : refl_constant) = fstar_refl_data_const "Unk" 
let (ref_Ctor : refl_constant) = fstar_refl_data_const "Ctor" 
let (ord_Lt_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Lt"] FStar_Range.dummyRange 
let (ord_Eq_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Eq"] FStar_Range.dummyRange 
let (ord_Gt_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Gt"] FStar_Range.dummyRange 
let (ord_Lt : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr ord_Lt_lid 
let (ord_Eq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr ord_Eq_lid 
let (ord_Gt : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr ord_Gt_lid 
let (ref_E_Lit : refl_constant) = fstar_refl_data_const "Lit" 
let (ref_E_Atom : refl_constant) = fstar_refl_data_const "Atom" 
let (ref_E_Plus : refl_constant) = fstar_refl_data_const "Plus" 
let (ref_E_Mult : refl_constant) = fstar_refl_data_const "Mult" 
let (ref_E_Minus : refl_constant) = fstar_refl_data_const "Minus" 
let (ref_E_Land : refl_constant) = fstar_refl_data_const "Land" 
let (ref_E_Lxor : refl_constant) = fstar_refl_data_const "Lxor" 
let (ref_E_Lor : refl_constant) = fstar_refl_data_const "Lor" 
let (ref_E_Ladd : refl_constant) = fstar_refl_data_const "Ladd" 
let (ref_E_Lsub : refl_constant) = fstar_refl_data_const "Lsub" 
let (ref_E_Shl : refl_constant) = fstar_refl_data_const "Shl" 
let (ref_E_Shr : refl_constant) = fstar_refl_data_const "Shr" 
let (ref_E_Neg : refl_constant) = fstar_refl_data_const "Neg" 
let (ref_E_Udiv : refl_constant) = fstar_refl_data_const "Udiv" 
let (ref_E_Umod : refl_constant) = fstar_refl_data_const "Umod" 
let (ref_E_MulMod : refl_constant) = fstar_refl_data_const "MulMod" 
let (ref_E_NatToBv : refl_constant) = fstar_refl_data_const "NatToBv" 