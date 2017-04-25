(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module FStar.Parser.AST
open FStar.All
open FStar.Errors
module C = FStar.Syntax.Const
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module S = FStar.Syntax.Syntax
open FStar.Range
open FStar.Ident
open FStar
open FStar.Util
open FStar.Const

(* AST produced by the parser, before desugaring
   It is not stratified: a single type called "term" containing
   expressions, formulas, types, and so on
 *)

(* Application type *)
type imp =
  (* F# compatible <> type application *)
  | FsTypApp
  (* Implict argument application *)
  | Hash
  (* explicit universe application *)
  | UnivApp
  (* normal application *)
  | Nothing

(* Qualifier for a binder *)
type arg_qualifier =
  (* If the binder correspond to an implicit *)
  | Implicit
  (* If we should use unification rather than subtyping on the type of this argument *)
  | Equality

type aqual = option<arg_qualifier>

type let_qualifier =
  | NoLetQualifier
  | Rec
  | Mutable

type term' =
  | Wild
  | Const     of sconst
  | Op        of ident * list<term>
  (* Assignment operation x <- t *)
  | Assign    of ident * term

  (* Type variable (F# compatibility ?) *)
  | Tvar      of ident

  (* universe variable *)
  | Uvar      of ident

  (* a qualified identifier that starts with a lowercase (Foo.Bar.baz) *)
  | Var       of lid

  (* a qualified identifier that starts with an uppercase (Foo.Bar.Baz) *)
  | Name      of lid

  (* a data constructor followed by one of its formal parameters, or an effect *)
  (* followed by one of its actions or "fields" *)
  | Projector of lid * ident

  (* Discriminator of a datatype i.e. Some? *)
  | Discrim   of lid

  (* data, type: bool in each arg records an implicit *)
  | Construct of lid * list<(term*imp)>

  (* function space *)
  | Product   of list<binder> * term
  | Abs       of list<pattern> * term

  (* aqual marks an explicitly provided implicit parameter *)
  | App       of term * term * imp
  | Let       of let_qualifier * list<(pattern * term)> * term
  | Seq       of term * term
  | If        of term * term * term
  | Match     of term * list<branch>
  | TryWith   of term * list<branch>

  (* A type anotation optionally accompanied by a tactic *)
  | Ascribed  of term * term * option<term>
  | Record    of option<term> * list<(lid * term)>

  (* Projection out of a record i.e. t.x *)
  | Project   of term * lid

  (* dependent tuple *)
  | Sum       of list<binder> * term
  | QForall   of list<binder> * list<list<term>> * term
  | QExists   of list<binder> * list<list<term>> * term
  | Refine    of binder * term

  (* A type with a bound identifier x:t *)
  | NamedTyp  of ident * term
  | Paren     of term
  | LetOpen   of lid * term

  | Requires  of term * option<string>
  | Ensures   of term * option<string>

  (* attributes decorating a term *)
  | Attributes of list<term>

and term = {tm:term'; range:range}

and binder' =
  | Variable of ident
  | TVariable of ident
  | Annotated of ident * term
  | TAnnotated of ident * term
  | NoName of term

and binder = {b:binder'; brange:range; aqual:aqual}

and pattern' =
  | PatWild
  | PatConst    of sconst
  | PatApp      of pattern * list<pattern>
  | PatVar      of ident * option<arg_qualifier>
  | PatName     of lid
  | PatTvar     of ident * option<arg_qualifier>
  | PatList     of list<pattern>
  (* dependent if flag is set *)
  | PatTuple    of list<pattern> * bool
  | PatRecord   of list<(lid * pattern)>
  | PatAscribed of pattern * term
  | PatOr       of list<pattern>
  | PatOp       of ident
and pattern = {pat:pattern'; prange:range}

and branch = (pattern * option<term> * term)

type typ = term
type expr = term

// Documentation comment. May appear appear as follows:
//  - Immediately before a top-level declaration
//  - Immediately before a type constructor or record field
//  - In the middle of a file, as a standalone documentation declaration
type fsdoc = {
  comment:string;
  key_val_map:list<(string * string)>;
  fsdrange: range
}

type record_field = {
  field_id:ident ;
  field_type:term ;
  field_doc:list<fsdoc> ;
  field_range : range
}

type variant_constr = {
  variant_id : ident ;
  variant_type : option<term> ;
  variant_doc : list<fsdoc> ;
  variant_range : range
}

type tycon' =
  | TyconAbstract
  | TyconAbbrev   of term
  | TyconRecord   of list<record_field>
  (* if true, uses 'of' instead of ':' *)
  | TyconVariant  of list<variant_constr> * bool

type tycon = {
  tycon_id: ident ;
  typarams: list<binder> ;
  tydata : tycon' ;
  tydoc : list<fsdoc> ;
  tyrange : range
}

type letbinding = {
  letbindingpat : pattern ;
  letbindingdef : term ;
  letbindingrange : range ;
  letbindingdoc : list<fsdoc>
}

(* TODO (KM) : these should be fsdocs and not comments *)
type qualifier =
  (* * a declaration only visible to the current module *)
  | Private
  (* * a declaration whose definition won't be visible outside current module *)
  | Abstract
  (* * an inductive definition for which we don't try to generate decidable equality *)
  | Noeq
  (* * an inductive definition for which we generate the naive decidable equality *)
  | Unopteq
  (* * a declaration which is assumed to hold without a definition (axiom) *)
  | Assumption
  | DefaultEffect
  | TotalEffect
  | Effect_qual
  | New
  (* * a definition that *should* always be unfolded by the normalizer *)
  | Inline
  (* * a definition that may be unfolded by the normalizer, but only if necessary (default) *)
  | Visible
  (* * a definition that will be unfolded by the normalizer, during unification and for SMT queries *)
  | Unfold_for_unification_and_vcgen
  (* * a definition that will be inlined only during compilation *)
  | Inline_for_extraction
  (* * a definition that can never be unfolded by the normalizer *)
  | Irreducible
  (* * a definition whose contents won't be extracted (currently, by KreMLin only) *)
  | NoExtract
  (* * An effect definition which comes with a reify operation *)
  | Reifiable
  (* * An effect definition which comes with a reflect operation *)
  | Reflectable

  (* old qualifiers *)
  | Opaque
  | Logic

type qualifiers = list<qualifier>

type attributes_ = list<term>
type decoration =
  | Qualifier of qualifier
  | DeclAttributes of list<term>

type lift_op =
  | NonReifiableLift of term
  | ReifiableLift    of term * term //lift_wp, lift
  | LiftForFree      of term

type lift = {
  msource: lid;
  mdest:   lid;
  lift_op: lift_op;
}

type pragma =
  | SetOptions of string
  | ResetOptions of option<string>
  | LightOff

type decl' =
  | TopLevelModule of lid
  | Open of lid
  | Include of lid
  | ModuleAbbrev of ident * lid
  | TopLevelLet of let_qualifier * list<letbinding>
  | Main of term
  (* If the bool is true then it is an effect definition (so the list contains only one element) *)
  | Tycon of bool * list<tycon>
  | Val of ident * term
  | Exception of ident * option<term>
  | NewEffect of effect_decl
  | SubEffect of lift
  | Pragma of pragma
  | Fsdoc of fsdoc
  | Assume of ident * term

and decl = {
  d:decl';
  drange:range;
  doc:list<fsdoc>;
  quals: qualifiers;
  attrs: attributes_
}

and effect_decl =
  (* KM : Is there really a need for the generality of decl here instead of e.g. lid * term ? *)
  | DefineEffect   of ident * list<binder> * term * list<decl>
  | RedefineEffect of ident * list<binder> * term

type modul =
  | Module of lid * list<decl>
  (* flag to mark admitted interfaces *)
  | Interface of lid * list<decl> * bool
type file = list<modul>
type inputFragment = either<file,list<decl>>

(********************************************************************************)

let at_most_one s r l = match l with
  | [ x ] -> Some x
  | [] -> None
  | _ -> raise (Error (Util.format1 "At most one %s is allowed on declarations" s, r))

let mk_decl d r decorations =
  let attributes_ = at_most_one "attribute set" r (
    List.choose (function DeclAttributes a -> Some a | _ -> None) decorations
  ) in
  let attributes_ = Util.dflt [] attributes_ in
  let qualifiers = List.choose (function Qualifier q -> Some q | _ -> None) decorations in
  { d=d; drange=r; quals=qualifiers; attrs=attributes_ ; doc=[]}

let mk_binder b r i = {b=b; brange=r; aqual=i}
let mk_term t r = {tm=t; range=r}
let mk_uminus t rminus r =
  let t =
    match t.tm with
    | Const (Const_int (s, Some (Signed, width))) ->
      Const (Const_int ("-" ^ s, Some (Signed, width)))
    | _ ->
      Op(mk_ident ("-", rminus), [t])
  in
  mk_term t r

let mk_pattern p r = {pat=p; prange=r}

(* TODO : only used in tosyntax *)
let un_curry_abs ps body = match body.tm with
  | Abs(p', body') -> Abs(ps@p', body')
  | _ -> Abs(ps, body)

let mk_function branches r1 r2 =
  let x =
    let i = FStar.Syntax.Syntax.next_id () in
    Ident.gen r1
  in
  mk_term (Abs([mk_pattern (PatVar(x,None)) r1],
               mk_term (Match(mk_term (Var(lid_of_ids [x])) r1, branches)) r2))
    r2

let un_function p tm = match p.pat, tm.tm with
  | PatVar _, Abs(pats, body) -> Some (mk_pattern (PatApp(p, pats)) p.prange, body)
  | _ -> None

let lid_with_range lid r = lid_of_path (path_of_lid lid) r

let consPat r hd tl = PatApp(mk_pattern (PatName C.cons_lid) r, [hd;tl])
let consTerm r hd tl = mk_term (Construct(C.cons_lid, [(hd, Nothing);(tl, Nothing)])) r
let lexConsTerm r hd tl = mk_term (Construct(C.lexcons_lid, [(hd, Nothing);(tl, Nothing)])) r

let mkConsList r elts =
  let nil = mk_term (Construct(C.nil_lid, [])) r in
  List.fold_right (fun e tl -> consTerm r e tl) elts nil

let mkLexList r elts =
  let nil = mk_term (Construct(C.lextop_lid, [])) r in
  List.fold_right (fun e tl -> lexConsTerm r e tl) elts nil

let ml_comp t =
  let ml = mk_term (Name FStar.Syntax.Const.effect_ML_lid) t.range in
  let t = mk_term (App(ml, t, Nothing)) t.range in
  t

let tot_comp t =
  let ml = mk_term (Name FStar.Syntax.Const.effect_Tot_lid) t.range in
  let t = mk_term (App(ml, t, Nothing)) t.range in
  t

let mkApp t args r = match args with
  | [] -> t
  | _ -> match t.tm with
    | Name s -> mk_term (Construct(s, args)) r
    | _ -> List.fold_left (fun t (a,imp) -> mk_term (App(t, a, imp)) r) t args

let mkRefSet r elts =
  let empty_lid, singleton_lid, union_lid =
    C.tset_empty, C.tset_singleton, C.tset_union
  in
  let empty = mk_term (Var(set_lid_range empty_lid r)) r in
  let ref_constr = mk_term (Var (set_lid_range C.heap_ref r)) r in
  let singleton = mk_term (Var (set_lid_range singleton_lid r)) r in
  let union = mk_term (Var(set_lid_range union_lid r)) r in
  List.fold_right (fun e tl ->
    let e = mkApp ref_constr [(e, Nothing)] r in
    let single_e = mkApp singleton [(e, Nothing)] r in
    mkApp union [(single_e, Nothing); (tl, Nothing)] r) elts empty

let mkExplicitApp t args r = match args with
  | [] -> t
  | _ -> match t.tm with
    | Name s -> mk_term (Construct(s, (List.map (fun a -> (a, Nothing)) args))) r
    | _ -> List.fold_left (fun t a -> mk_term (App(t, a, Nothing)) r) t args

let mkAdmitMagic r =
  let unit_const = mk_term(Const Const_unit) r in
  let admit =
    let admit_name = mk_term(Var(set_lid_range C.admit_lid r)) r in
    mkExplicitApp admit_name [unit_const] r
  in
  let magic =
    let magic_name = mk_term(Var(set_lid_range C.magic_lid r)) r in
    mkExplicitApp magic_name [unit_const] r
  in
  let admit_magic = mk_term(Seq(admit, magic)) r in
  admit_magic

let mkWildAdmitMagic r = (mk_pattern PatWild r, None, mkAdmitMagic r)

let focusBranches branches r =
  let should_filter = Util.for_some fst branches in
  if should_filter then
    let _ = Errors.warn r "Focusing on only some cases" in
    let focussed = List.filter fst branches |> List.map snd in
    focussed@[mkWildAdmitMagic r]
  else branches |> List.map snd

let focusLetBindings lbs r =
  let should_filter = Util.for_some fst lbs in
  if should_filter
  then
    let _ = Errors.warn r "Focusing on only some cases in this (mutually) recursive definition" in
    List.map (fun (f, lb) ->
      if f then lb
      else (fst lb, mkAdmitMagic r)) lbs
  else lbs |> List.map snd

let mkFsTypApp t args r =
  mkApp t (List.map (fun a -> (a, FsTypApp)) args) r

let mkTuple args r =
  let cons = U.mk_tuple_data_lid (List.length args) r in
  mkExplicitApp (mk_term (Name cons) r) args r

let mkDTuple args r =
  let cons = U.mk_dtuple_data_lid (List.length args) r in
  mkExplicitApp (mk_term (Name cons) r) args r

(* Creates a binder id:t with aqual implicit optionally refined by refopt. *)
(* If should_bind_var is true then it binds id in the refinement if any. *)
(* Otherwise the refinement is assumed not to depend on id *)
let mkRefinedBinder id t should_bind_var refopt r implicit =
  let b = mk_binder (Annotated(id, t)) r implicit in
  match refopt with
  | None -> b
  | Some phi ->
    if should_bind_var
    then mk_binder (Annotated(id, mk_term (Refine(b, phi)) r)) r implicit
    else
      let x = gen t.range in
      let b = mk_binder (Annotated (x, t)) r implicit in
      mk_binder (Annotated(id, mk_term (Refine(b, phi)) r)) r implicit

let mkRefinedPattern pat t should_bind_pat phi_opt t_range range =
  let t = match phi_opt with
    | None     -> t
    | Some phi ->
      if not <| should_bind_pat
      then
        let x = gen t.range in
        mk_term (Refine(mk_binder (Annotated (x, t)) t_range  None, phi)) range
      else
        match pat.pat with
        | PatVar (x,_) ->
          mk_term (Refine(mk_binder (Annotated(x, t)) t_range  None, phi)) range
        | _ ->
          let x = gen t_range in
          let phi =
            (* match x with | pat -> phi | _ -> False *)
            let x_var = mk_term (Var (lid_of_ids [x])) phi.range in
            let pat_branch = (pat, None, phi)in
            let otherwise_branch =
                (mk_pattern PatWild phi.range, None,
                  mk_term (Name (lid_of_path ["False"] phi.range)) phi.range)
            in
            mk_term (Match (x_var, [pat_branch ; otherwise_branch])) phi.range
          in
          mk_term (Refine(mk_binder (Annotated(x, t)) t_range  None, phi)) range
  in
  mk_pattern (PatAscribed(pat, t)) range

let rec extract_named_refinement t1  =
  match t1.tm with
  | NamedTyp(x, t) -> Some (x, t, None)
  | Refine({b=Annotated(x, t)}, t') ->  Some (x, t, Some t')
  | Paren t -> extract_named_refinement t
  | _ -> None

(* Some helpers that parse.mly and parse.fsy will want too *)

(* JP: what does this function do? A comment would be welcome, or at the very
   least a type annotation...
   JP: ok, here's my understanding.
   This function peeks at the first top-level declaration;
   - if this is NOT a TopLevelModule, then we're in interactive mode and return
     [Inr list-of-declarations]
   - if this IS a TopLevelModule, then we do a forward search and group
     declarations together with the preceding [TopLevelModule] and return a [Inl
     list-of-modules] where each "module" [Module (lid, list-of-declarations)], with the
     unspecified invariant that the first declaration is a [TopLevelModule]
   JP: TODO actually forbid multiple modules and remove all of this. *)

//NS: needed to hoist this to workaround a bootstrapping bug
//    leaving it within as_frag causes the type-checker to take a very long time, perhaps looping
let rec as_mlist (out:list<modul>) (cur: (lid * decl) * list<decl>) (ds:list<decl>) : list<modul> =
  let ((m_name, m_decl), cur) = cur in
  match ds with
  | [] -> List.rev (Module(m_name, m_decl :: List.rev cur)::out)
  | d :: ds ->
    match d.d with
    | TopLevelModule m' ->
      as_mlist (Module(m_name, m_decl :: List.rev cur)::out) ((m', d), []) ds
    | _ ->
      as_mlist out ((m_name, m_decl), d::cur) ds

let as_frag is_light (light_range:Range.range) (ds:list<decl>) : either<(list<modul>),(list<decl>)> =
  let d, ds = match ds with
    | d :: ds -> d, ds
    (* If the fragment is empty we raise an exception which will be caught by by the parser driver *)
    | [] -> raise Empty_frag
  in
  match d.d with
  | TopLevelModule m ->
    let ds = if is_light then mk_decl (Pragma LightOff) light_range [] :: ds else ds in
    (* TODO : remove this annoying feature allowing multiple modules per-file (the *)
    (* code would be so much simpler...) *)
    let ms = as_mlist [] ((m,d), []) ds in
    begin match List.tl ms with
    | Module (m', _) :: _ ->
      (* This check is coded to hard-fail in dep.num_of_toplevelmods. *)
      let msg = "Support for more than one module in a file is deprecated" in
      print2_warning "%s (Warning): %s\n" (string_of_range (range_of_lid m')) msg
    | _ -> ()
    end;
    Inl ms
  | _ ->
    let ds = d::ds in
    List.iter (function
      | {d=TopLevelModule _; drange=r} -> raise (Error("Unexpected module declaration", r))
      | _ -> ()
    ) ds;
    Inr ds

let compile_op arity s =
  let name_of_char = function
    |'&' -> "Amp"
    |'@'  -> "At"
    |'+' -> "Plus"
    |'-' when (arity=1) -> "Minus"
    |'-' -> "Subtraction"
    |'/' -> "Slash"
    |'<' -> "Less"
    |'=' -> "Equals"
    |'>' -> "Greater"
    |'_' -> "Underscore"
    |'|' -> "Bar"
    |'!' -> "Bang"
    |'^' -> "Hat"
    |'%' -> "Percent"
    |'*' -> "Star"
    |'?' -> "Question"
    |':' -> "Colon"
    | _ -> "UNKNOWN"
  in
  match s with
  | ".[]<-" -> "op_String_Assignment"
  | ".()<-" -> "op_Array_Assignment"
  | ".[]" -> "op_String_Access"
  | ".()" -> "op_Array_Access"
  | _ -> "op_"^ (String.concat "_" (List.map name_of_char (String.list_of_string s)))

let compile_op' s =
  compile_op (-1) s


//////////////////////////////////////////////////////////////////////////////////////////////
// Place fsdoc node
//////////////////////////////////////////////////////////////////////////////////////////////

let to_fsdoc (comment, kwd_args, range) =
  {
    comment = comment ;
    key_val_map = kwd_args;
    fsdrange = range
  }

let is_nil = function | [] -> true | _ -> false

let comments_before r1 (_, _, r) =
  line_of_pos (end_of_range r) <= line_of_pos (end_of_range r1)

let fold_and_retrieve (f:list<'a> -> 'b -> list<'a> * 'b) (resources:list<'a>) (lfolded:list<'b>) =
  let fold_map_adaptator (acc, l) y = let acc, y = f acc y in acc, y::l in
  let rest, rev_folded = List.fold_left fold_map_adaptator (resources, []) lfolded in
  rest, List.rev rev_folded

let place_fsdoc_in_record_field fsdocs field =
  let current_fsdocs, other_fsdocs = take (comments_before field.field_range) fsdocs in
  assert (is_nil field.field_doc) ;
  other_fsdocs, {field with field_doc = List.map to_fsdoc current_fsdocs}

let place_fsdoc_in_variant fsdocs variant =
  let current_fsdocs, other_fsdocs = take (comments_before variant.variant_range) fsdocs in
  assert (is_nil variant.variant_doc) ;
  other_fsdocs, {variant with variant_doc = List.map to_fsdoc current_fsdocs}

let place_fsdoc_in_tycon fsdocs tyc =
  let contained_fsdocs, fsdocs = take (comments_before tyc.tyrange) fsdocs in
  assert (is_nil tyc.tydoc) ;
  let tyc = match tyc.tydata with
    | TyconAbstract | TyconAbbrev _ -> { tyc with tydoc = List.map to_fsdoc contained_fsdocs }
    | TyconRecord fields ->
      let type_fsdocs, fields_fsdocs = take (comments_before tyc.tycon_id.idRange) contained_fsdocs in
      let residual_fsdocs, fields = fold_and_retrieve place_fsdoc_in_record_field fields_fsdocs fields in
      assert (is_nil residual_fsdocs) ;
      {tyc with tydoc = List.map to_fsdoc type_fsdocs ; tydata = TyconRecord fields}
    | TyconVariant (variants, b) ->
      let type_fsdocs, variants_fsdocs = take (comments_before tyc.tycon_id.idRange) contained_fsdocs in
      let residual_fsdocs, variants = fold_and_retrieve place_fsdoc_in_variant variants_fsdocs variants in
      assert (is_nil residual_fsdocs) ;
      {tyc with tydoc = List.map to_fsdoc type_fsdocs ; tydata = TyconVariant (variants, b)}
  in
  fsdocs, tyc

let place_fsdoc_in_toplevellet fsdocs lb =
  let contained_fsdocs, fsdocs = take (comments_before lb.letbindingrange) fsdocs in
  assert (is_nil lb.letbindingdoc) ;
  fsdocs, {lb with letbindingdoc = List.map to_fsdoc contained_fsdocs}

let place_fsdoc_in_decl fsdocs decl =
  let contained_fsdocs, fsdocs = take (comments_before decl.drange) fsdocs in
  assert (is_nil decl.doc) ;
  (* If we are placing documents in a let or a type declaration then we put the documentation at the next level *)
  let decl = match decl.d with
    | Tycon (b, tycons) ->
      let residual_fsdocs, tycons = fold_and_retrieve place_fsdoc_in_tycon contained_fsdocs tycons in
      (* TODO : have a real error in that case *)
      assert (is_nil residual_fsdocs) ;
      { decl with d = Tycon (b, tycons) }
    | TopLevelLet (lq, defs) ->
      let residual_fsdocs, defs = fold_and_retrieve place_fsdoc_in_toplevellet contained_fsdocs defs in
      assert (is_nil residual_fsdocs) ;
      {decl with d = TopLevelLet (lq, defs) }
    | _ ->
      { decl with doc = List.map to_fsdoc fsdocs }
  in
  fsdocs, decl

let place_fsdoc_before_decl (fsdocs, l) decl =
  let decl_line = line_of_pos (end_of_range decl.drange) in
  let is_standalone_fsdoc (_, _, r) = line_of_pos (end_of_range r) + 2 <= decl_line in
  let standalone_fsdocs, fsdocs = take is_standalone_fsdoc fsdocs in
  let standalone_fsdocs =
    List.map (fun c -> let d = to_fsdoc c in mk_decl (Fsdoc d) d.fsdrange []) standalone_fsdocs
  in
  let fsdocs, decl = place_fsdoc_in_decl fsdocs decl in
  fsdocs, decl:: standalone_fsdocs @ l

let place_fsdoc_in_decls fsdocs decls =
  let fsdocs, rev_decls = List.fold_left  place_fsdoc_before_decl (fsdocs, []) decls in
  fsdocs, List.rev rev_decls

let place_fsdoc_in_modul fsdocs modul =
  match modul with
  | Module (m, decls) ->
    let fsdocs, decls = place_fsdoc_in_decls fsdocs decls in
    fsdocs, Module (m, decls)
  | Interface (m, decls, b) ->
    let fsdocs, decls = place_fsdoc_in_decls fsdocs decls in
    fsdocs, Interface (m, decls, b)

let place_fsdoc_in_frag fsdocs frag =
  match frag with
  | Inr moduls ->
    let fsdocs, moduls = fold_and_retrieve place_fsdoc_in_modul fsdocs moduls in
    fsdocs, Inr moduls
  | Inl decls ->
    let fsdocs, decls = place_fsdoc_in_decls fsdocs decls in
    fsdocs, Inl decls

//////////////////////////////////////////////////////////////////////////////////////////////
// Printing ASTs, mostly for debugging
//////////////////////////////////////////////////////////////////////////////////////////////

(* KM (04/17) : Do we still need these functions since we have toDocument ? *)

let string_of_fsdoc (comment,keywords) =
  comment ^ (String.concat "," (List.map (fun (k,v) -> k ^ "->" ^ v) keywords))

let string_of_let_qualifier = function
  | NoLetQualifier -> ""
  | Rec -> "rec"
  | Mutable -> "mutable"

let to_string_l sep f l =
  String.concat sep (List.map f l)

let imp_to_string = function
  | Hash -> "#"
  | UnivApp -> "u#"
  | _ -> ""

let rec term_to_string (x:term) = match x.tm with
  | Wild -> "_"
  | Requires (t, _) -> Util.format1 "(requires %s)" (term_to_string t)
  | Ensures (t, _) -> Util.format1 "(ensures %s)" (term_to_string t)
  | Const c -> P.const_to_string c
  | Op(s, xs) ->
      Util.format2 "%s(%s)" (text_of_id s) (String.concat ", " (List.map (fun x -> x|> term_to_string) xs))
  | Tvar id
  | Uvar id -> id.idText
  | Var l
  | Name l -> l.str
  | Construct (l, args) ->
    Util.format2 "(%s %s)" l.str (to_string_l " " (fun (a,imp) -> Util.format2 "%s%s" (imp_to_string imp) (term_to_string a)) args)
  | Abs(pats, t) ->
    Util.format2 "(fun %s -> %s)" (to_string_l " " pat_to_string pats) (t|> term_to_string)
  | App(t1, t2, imp) -> Util.format3 "%s %s%s" (t1|> term_to_string) (imp_to_string imp) (t2|> term_to_string)
  | Let (Rec, lbs, body) ->
    Util.format2 "let rec %s in %s" (to_string_l " and " (fun (p,b) -> Util.format2 "%s=%s" (p|> pat_to_string) (b|> term_to_string)) lbs) (body|> term_to_string)
  | Let (q, [(pat,tm)], body) ->
    Util.format4 "let %s %s = %s in %s" (string_of_let_qualifier q) (pat|> pat_to_string) (tm|> term_to_string) (body|> term_to_string)
  | Seq(t1, t2) ->
    Util.format2 "%s; %s" (t1|> term_to_string) (t2|> term_to_string)
  | If(t1, t2, t3) ->
    Util.format3 "if %s then %s else %s" (t1|> term_to_string) (t2|> term_to_string) (t3|> term_to_string)
  | Match(t, branches) ->
    Util.format2 "match %s with %s"
      (t|> term_to_string)
      (to_string_l " | " (fun (p,w,e) -> Util.format3 "%s %s -> %s"
        (p |> pat_to_string)
        (match w with | None -> "" | Some e -> Util.format1 "when %s" (term_to_string e))
        (e |> term_to_string)) branches)
  | Ascribed(t1, t2, None) ->
    Util.format2 "(%s : %s)" (t1|> term_to_string) (t2|> term_to_string)
  | Ascribed(t1, t2, Some tac) ->
    Util.format3 "(%s : %s by %s)" (t1|> term_to_string) (t2|> term_to_string) (tac |> term_to_string)
  | Record(Some e, fields) ->
    Util.format2 "{%s with %s}" (e|> term_to_string) (to_string_l " " (fun (l,e) -> Util.format2 "%s=%s" (l.str) (e|> term_to_string)) fields)
  | Record(None, fields) ->
    Util.format1 "{%s}" (to_string_l " " (fun (l,e) -> Util.format2 "%s=%s" (l.str) (e|> term_to_string)) fields)
  | Project(e,l) ->
    Util.format2 "%s.%s" (e|> term_to_string) (l.str)
  | Product([], t) ->
    term_to_string t
  | Product(b::hd::tl, t) ->
    term_to_string (mk_term (Product([b], mk_term (Product(hd::tl, t)) x.range)) x.range)
  | Product([b], t) ->
    Util.format2 "%s -> %s" (b|> binder_to_string) (t|> term_to_string)
  | Sum(binders, t) ->
    Util.format2 "%s * %s" (binders |> (List.map binder_to_string) |> String.concat " * " ) (t|> term_to_string)
  | QForall(bs, pats, t) ->
    Util.format3 "forall %s.{:pattern %s} %s"
      (to_string_l " " binder_to_string bs)
      (to_string_l " \/ " (to_string_l "; " term_to_string) pats)
      (t|> term_to_string)
  | QExists(bs, pats, t) ->
    Util.format3 "exists %s.{:pattern %s} %s"
      (to_string_l " " binder_to_string bs)
      (to_string_l " \/ " (to_string_l "; " term_to_string) pats)
      (t|> term_to_string)
  | Refine(b, t) ->
    Util.format2 "%s:{%s}" (b|> binder_to_string) (t|> term_to_string)
  | NamedTyp(x, t) ->
    Util.format2 "%s:%s" x.idText  (t|> term_to_string)
  | Paren t -> Util.format1 "(%s)" (t|> term_to_string)
  | Product(bs, t) ->
        Util.format2 "Unidentified product: [%s] %s"
          (bs |> List.map binder_to_string |> String.concat ",") (t|> term_to_string)
  | t -> "_"

and binder_to_string x =
  let s = match x.b with
  | Variable i -> i.idText
  | TVariable i -> Util.format1 "%s:_" (i.idText)
  | TAnnotated(i,t)
  | Annotated(i,t) -> Util.format2 "%s:%s" (i.idText) (t |> term_to_string)
  | NoName t -> t |> term_to_string in
  Util.format2 "%s%s" (aqual_to_string x.aqual) s

and aqual_to_string = function
  | Some Equality -> "$"
  | Some Implicit -> "#"
  | _ -> ""

and pat_to_string x = match x.pat with
  | PatWild -> "_"
  | PatConst c -> P.const_to_string c
  | PatApp(p, ps) -> Util.format2 "(%s %s)" (p |> pat_to_string) (to_string_l " " pat_to_string ps)
  | PatTvar (i, aq)
  | PatVar (i,  aq) -> Util.format2 "%s%s" (aqual_to_string aq) i.idText
  | PatName l -> l.str
  | PatList l -> Util.format1 "[%s]" (to_string_l "; " pat_to_string l)
  | PatTuple (l, false) -> Util.format1 "(%s)" (to_string_l ", " pat_to_string l)
  | PatTuple (l, true) -> Util.format1 "(|%s|)" (to_string_l ", " pat_to_string l)
  | PatRecord l -> Util.format1 "{%s}" (to_string_l "; " (fun (f,e) -> Util.format2 "%s=%s" (f.str) (e |> pat_to_string)) l)
  | PatOr l ->  to_string_l "|\n " pat_to_string l
  | PatOp op ->  Util.format1 "(%s)" (Ident.text_of_id op)
  | PatAscribed(p,t) -> Util.format2 "(%s:%s)" (p |> pat_to_string) (t |> term_to_string)

let rec head_id_of_pat p = match p.pat with
  | PatName l -> [l]
  | PatVar (i, _) -> [FStar.Ident.lid_of_ids [i]]
  | PatApp(p, _) -> head_id_of_pat p
  | PatAscribed(p, _) -> head_id_of_pat p
  | _ -> []

let lids_of_let defs =  defs |> List.collect (fun lb -> head_id_of_pat lb.letbindingpat)

let id_of_tycon  tyc = tyc.tycon_id.idText

let decl_to_string (d:decl) = match d.d with
  | TopLevelModule l -> "module " ^ l.str
  | Open l -> "open " ^ l.str
  | Include l -> "include " ^ l.str
  | ModuleAbbrev (i, l) -> Util.format2 "module %s = %s" i.idText l.str
  | TopLevelLet(_, pats) -> "let " ^ (lids_of_let pats |> List.map (fun l -> l.str) |> String.concat ", ")
  | Main _ -> "main ..."
  | Assume(i, _) -> "assume " ^ i.idText
  | Tycon(_, tys) -> "type " ^ (tys |> List.map id_of_tycon |> String.concat ", ")
  | Val(i, _) -> "val " ^ i.idText
  | Exception(i, _) -> "exception " ^ i.idText
  | NewEffect(DefineEffect(i, _, _, _))
  | NewEffect(RedefineEffect(i, _, _)) -> "new_effect " ^ i.idText
  | SubEffect _ -> "sub_effect"
  | Pragma _ -> "pragma"
  | Fsdoc _ -> "fsdoc"

let modul_to_string (m:modul) = match m with
    | Module (_, decls)
    | Interface (_, decls, _) ->
      decls |> List.map decl_to_string |> String.concat "\n"


//////////////////////////////////////////////////////////////////////////////////////////////
// Error reporting
//////////////////////////////////////////////////////////////////////////////////////////////

let error msg tm r =
 let tm = tm |> term_to_string in
 let tm = if String.length tm >= 80 then Util.substring tm 0 77 ^ "..." else tm in
 raise (Error(msg^"\n"^tm, r))
