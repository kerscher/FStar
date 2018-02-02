open Prims
type step =
  | Beta
  | Iota
  | Zeta
  | Exclude of step
  | Weak
  | HNF
  | Primops
  | Eager_unfolding
  | Inlining
  | NoDeltaSteps
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth
  | UnfoldOnly of FStar_Ident.lid Prims.list
  | UnfoldTac
  | PureSubtermsWithinComputations
  | Simplify
  | EraseUniverses
  | AllowUnboundUniverses
  | Reify
  | CompressUvars
  | NoFullNorm
  | CheckNoUvars
  | Unmeta[@@deriving show]
let uu___is_Beta: step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____18 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____22 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____26 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____31 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_Weak: step -> Prims.bool =
  fun projectee  -> match projectee with | Weak  -> true | uu____42 -> false
let uu___is_HNF: step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____46 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____50 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____54 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____58 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____62 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____67 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____81 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____98 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____102 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____106 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____110 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____114 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____118 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____122 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____126 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____130 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____134 -> false
type steps = step Prims.list[@@deriving show]
type psc =
  {
  psc_range: FStar_Range.range;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t;}[@@deriving show]
let __proj__Mkpsc__item__psc_range: psc -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
let __proj__Mkpsc__item__psc_subst:
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
let null_psc: psc =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____168  -> []) }
let psc_range: psc -> FStar_Range.range = fun psc  -> psc.psc_range
let psc_subst: psc -> FStar_Syntax_Syntax.subst_t =
  fun psc  -> psc.psc_subst ()
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  requires_binder_substitution: Prims.bool;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
let __proj__Mkprimitive_step__item__name: primitive_step -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
let __proj__Mkprimitive_step__item__arity: primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
let __proj__Mkprimitive_step__item__strong_reduction_ok:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
let __proj__Mkprimitive_step__item__requires_binder_substitution:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
let __proj__Mkprimitive_step__item__interpretation:
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy[@@deriving show]
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____369 -> false
let __proj__Clos__item___0:
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____471 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____482 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___74_501  ->
    match uu___74_501 with
    | Clos (uu____502,t,uu____504,uu____505) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____550 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;
  strong: Prims.bool;
  memoize_lazy: Prims.bool;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__primitive_steps
let __proj__Mkcfg__item__strong: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__strong
let __proj__Mkcfg__item__memoize_lazy: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__memoize_lazy
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Cfg of cfg
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____806 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____842 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____878 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____947 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____989 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1045 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1085 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1117 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1153 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1169 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1194 .
    'Auu____1194 ->
      FStar_Range.range -> 'Auu____1194 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1248 = FStar_ST.op_Bang r in
          match uu____1248 with
          | FStar_Pervasives_Native.Some uu____1296 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1350 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1350 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___75_1357  ->
    match uu___75_1357 with
    | Arg (c,uu____1359,uu____1360) ->
        let uu____1361 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1361
    | MemoLazy uu____1362 -> "MemoLazy"
    | Abs (uu____1369,bs,uu____1371,uu____1372,uu____1373) ->
        let uu____1378 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1378
    | UnivArgs uu____1383 -> "UnivArgs"
    | Match uu____1390 -> "Match"
    | App (uu____1397,t,uu____1399,uu____1400) ->
        let uu____1401 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1401
    | Meta (m,uu____1403) -> "Meta"
    | Let uu____1404 -> "Let"
    | Cfg uu____1413 -> "Cfg"
    | Debug (t,uu____1415) ->
        let uu____1416 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1416
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1424 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1424 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1440 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1440 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1453 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1453 then f () else ()
let is_empty: 'Auu____1457 . 'Auu____1457 Prims.list -> Prims.bool =
  fun uu___76_1463  ->
    match uu___76_1463 with | [] -> true | uu____1466 -> false
let lookup_bvar:
  'Auu____1473 'Auu____1474 .
    ('Auu____1474,'Auu____1473) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1473
  =
  fun env  ->
    fun x  ->
      try
        let uu____1498 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1498
      with
      | uu____1511 ->
          let uu____1512 =
            let uu____1513 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1513 in
          failwith uu____1512
let downgrade_ghost_effect_name:
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
let norm_universe:
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____1550 =
            FStar_List.fold_left
              (fun uu____1576  ->
                 fun u1  ->
                   match uu____1576 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1601 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1601 with
                        | (k_u,n1) ->
                            let uu____1616 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1616
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1550 with
          | (uu____1634,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1659 =
                   let uu____1660 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1660 in
                 match uu____1659 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1678 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1687 ->
                   let uu____1688 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1688
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1694 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1703 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1712 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1719 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1719 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1736 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1736 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1744 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1752 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1752 with
                                  | (uu____1757,m) -> n1 <= m)) in
                        if uu____1744 then rest1 else us1
                    | uu____1762 -> us1)
               | uu____1767 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1771 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1771 in
        let uu____1774 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1774
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1776 = aux u in
           match uu____1776 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec closure_as_term:
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____1880  ->
             let uu____1881 = FStar_Syntax_Print.tag_of_term t in
             let uu____1882 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1881
               uu____1882);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1889 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1891 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1916 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1917 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1918 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1919 ->
                  let uu____1936 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1936
                  then
                    let uu____1937 =
                      let uu____1938 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1939 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1938 uu____1939 in
                    failwith uu____1937
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1942 =
                    let uu____1943 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1943 in
                  mk uu____1942 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1950 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1950
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1952 = lookup_bvar env x in
                  (match uu____1952 with
                   | Univ uu____1955 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____1958,uu____1959) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2071 = closures_as_binders_delayed cfg env bs in
                  (match uu____2071 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2099 =
                         let uu____2100 =
                           let uu____2117 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2117) in
                         FStar_Syntax_Syntax.Tm_abs uu____2100 in
                       mk uu____2099 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2148 = closures_as_binders_delayed cfg env bs in
                  (match uu____2148 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2190 =
                    let uu____2201 =
                      let uu____2208 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2208] in
                    closures_as_binders_delayed cfg env uu____2201 in
                  (match uu____2190 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2226 =
                         let uu____2227 =
                           let uu____2234 =
                             let uu____2235 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2235
                               FStar_Pervasives_Native.fst in
                           (uu____2234, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2227 in
                       mk uu____2226 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2326 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2326
                    | FStar_Util.Inr c ->
                        let uu____2340 = close_comp cfg env c in
                        FStar_Util.Inr uu____2340 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2356 =
                    let uu____2357 =
                      let uu____2384 = closure_as_term_delayed cfg env t11 in
                      (uu____2384, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2357 in
                  mk uu____2356 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2435 =
                    let uu____2436 =
                      let uu____2443 = closure_as_term_delayed cfg env t' in
                      let uu____2446 =
                        let uu____2447 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2447 in
                      (uu____2443, uu____2446) in
                    FStar_Syntax_Syntax.Tm_meta uu____2436 in
                  mk uu____2435 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2507 =
                    let uu____2508 =
                      let uu____2515 = closure_as_term_delayed cfg env t' in
                      let uu____2518 =
                        let uu____2519 =
                          let uu____2526 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2526) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2519 in
                      (uu____2515, uu____2518) in
                    FStar_Syntax_Syntax.Tm_meta uu____2508 in
                  mk uu____2507 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2545 =
                    let uu____2546 =
                      let uu____2553 = closure_as_term_delayed cfg env t' in
                      let uu____2556 =
                        let uu____2557 =
                          let uu____2566 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2566) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2557 in
                      (uu____2553, uu____2556) in
                    FStar_Syntax_Syntax.Tm_meta uu____2546 in
                  mk uu____2545 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2579 =
                    let uu____2580 =
                      let uu____2587 = closure_as_term_delayed cfg env t' in
                      (uu____2587, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2580 in
                  mk uu____2579 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2627  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2646 =
                    let uu____2657 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2657
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2676 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___97_2688 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___97_2688.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___97_2688.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2676)) in
                  (match uu____2646 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___98_2704 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___98_2704.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___98_2704.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2715,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2774  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2799 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2799
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2819  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2841 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2841
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___99_2853 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___99_2853.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___99_2853.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___100_2854 = lb in
                    let uu____2855 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___100_2854.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___100_2854.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2855
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2885  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2974 =
                    match uu____2974 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3029 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3050 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3110  ->
                                        fun uu____3111  ->
                                          match (uu____3110, uu____3111) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3202 =
                                                norm_pat env3 p1 in
                                              (match uu____3202 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3050 with
                               | (pats1,env3) ->
                                   ((let uu___101_3284 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___101_3284.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___102_3303 = x in
                                let uu____3304 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3303.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3303.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3304
                                } in
                              ((let uu___103_3318 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3318.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___104_3329 = x in
                                let uu____3330 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___104_3329.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___104_3329.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3330
                                } in
                              ((let uu___105_3344 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___105_3344.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___106_3360 = x in
                                let uu____3361 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___106_3360.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___106_3360.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3361
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___107_3368 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___107_3368.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3371 = norm_pat env1 pat in
                        (match uu____3371 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3400 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3400 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3406 =
                    let uu____3407 =
                      let uu____3430 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3430) in
                    FStar_Syntax_Syntax.Tm_match uu____3407 in
                  mk uu____3406 t1.FStar_Syntax_Syntax.pos))
and closure_as_term_delayed:
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
        | uu____3516 -> closure_as_term cfg env t
and closures_as_args_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> args
        | uu____3542 ->
            FStar_List.map
              (fun uu____3559  ->
                 match uu____3559 with
                 | (x,imp) ->
                     let uu____3578 = closure_as_term_delayed cfg env x in
                     (uu____3578, imp)) args
and closures_as_binders_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____3592 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3641  ->
                  fun uu____3642  ->
                    match (uu____3641, uu____3642) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___108_3712 = b in
                          let uu____3713 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___108_3712.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___108_3712.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3713
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3592 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
and close_comp:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> c
        | uu____3806 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3819 = closure_as_term_delayed cfg env t in
                 let uu____3820 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3819 uu____3820
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3833 = closure_as_term_delayed cfg env t in
                 let uu____3834 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3833 uu____3834
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___77_3860  ->
                           match uu___77_3860 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3864 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3864
                           | f -> f)) in
                 let uu____3868 =
                   let uu___109_3869 = c1 in
                   let uu____3870 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3870;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___109_3869.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3868)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___78_3880  ->
            match uu___78_3880 with
            | FStar_Syntax_Syntax.DECREASES uu____3881 -> false
            | uu____3884 -> true))
and close_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___79_3902  ->
                      match uu___79_3902 with
                      | FStar_Syntax_Syntax.DECREASES uu____3903 -> false
                      | uu____3906 -> true)) in
            let rc1 =
              let uu___110_3908 = rc in
              let uu____3909 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___110_3908.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3909;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3916 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe in
  let arg_as_list a u a =
    let uu____4001 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4001 in
  let arg_as_bounded_int uu____4029 =
    match uu____4029 with
    | (a,uu____4041) ->
        let uu____4048 =
          let uu____4049 = FStar_Syntax_Subst.compress a in
          uu____4049.FStar_Syntax_Syntax.n in
        (match uu____4048 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4059;
                FStar_Syntax_Syntax.vars = uu____4060;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4062;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4063;_},uu____4064)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4103 =
               let uu____4108 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4108) in
             FStar_Pervasives_Native.Some uu____4103
         | uu____4113 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4153 = f a in FStar_Pervasives_Native.Some uu____4153
    | uu____4154 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4202 = f a0 a1 in FStar_Pervasives_Native.Some uu____4202
    | uu____4203 -> FStar_Pervasives_Native.None in
  let unary_op a413 a414 a415 a416 a417 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4245 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a412  -> (Obj.magic (f res.psc_range)) a412)
                    uu____4245)) a413 a414 a415 a416 a417 in
  let binary_op a420 a421 a422 a423 a424 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4294 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a418  ->
                       fun a419  -> (Obj.magic (f res.psc_range)) a418 a419)
                    uu____4294)) a420 a421 a422 a423 a424 in
  let as_primitive_step uu____4318 =
    match uu____4318 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        } in
  let unary_int_op f =
    unary_op () (fun a425  -> (Obj.magic arg_as_int) a425)
      (fun a426  ->
         fun a427  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4366 = f x in
                   FStar_Syntax_Embeddings.embed_int r uu____4366)) a426 a427) in
  let binary_int_op f =
    binary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           fun a431  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4394 = f x y in
                       FStar_Syntax_Embeddings.embed_int r uu____4394)) a429
               a430 a431) in
  let unary_bool_op f =
    unary_op () (fun a432  -> (Obj.magic arg_as_bool) a432)
      (fun a433  ->
         fun a434  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4415 = f x in
                   FStar_Syntax_Embeddings.embed_bool r uu____4415)) a433
             a434) in
  let binary_bool_op f =
    binary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           fun a438  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4443 = f x y in
                       FStar_Syntax_Embeddings.embed_bool r uu____4443)) a436
               a437 a438) in
  let binary_string_op f =
    binary_op () (fun a439  -> (Obj.magic arg_as_string) a439)
      (fun a440  ->
         fun a441  ->
           fun a442  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4471 = f x y in
                       FStar_Syntax_Embeddings.embed_string r uu____4471))
               a440 a441 a442) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4579 =
          let uu____4588 = as_a a in
          let uu____4591 = as_b b in (uu____4588, uu____4591) in
        (match uu____4579 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4606 =
               let uu____4607 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4607 in
             FStar_Pervasives_Native.Some uu____4606
         | uu____4608 -> FStar_Pervasives_Native.None)
    | uu____4617 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4631 =
        let uu____4632 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4632 in
      mk uu____4631 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4642 =
      let uu____4645 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4645 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4642 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4677 =
      let uu____4678 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4678 in
    FStar_Syntax_Embeddings.embed_int rng uu____4677 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4696 = arg_as_string a1 in
        (match uu____4696 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4702 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2) in
             (match uu____4702 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4715 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4715
              | uu____4716 -> FStar_Pervasives_Native.None)
         | uu____4721 -> FStar_Pervasives_Native.None)
    | uu____4724 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4734 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4734 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4758 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4769 =
          let uu____4790 = arg_as_string fn in
          let uu____4793 = arg_as_int from_line in
          let uu____4796 = arg_as_int from_col in
          let uu____4799 = arg_as_int to_line in
          let uu____4802 = arg_as_int to_col in
          (uu____4790, uu____4793, uu____4796, uu____4799, uu____4802) in
        (match uu____4769 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4833 =
                 let uu____4834 = FStar_BigInt.to_int_fs from_l in
                 let uu____4835 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4834 uu____4835 in
               let uu____4836 =
                 let uu____4837 = FStar_BigInt.to_int_fs to_l in
                 let uu____4838 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4837 uu____4838 in
               FStar_Range.mk_range fn1 uu____4833 uu____4836 in
             let uu____4839 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4839
         | uu____4844 -> FStar_Pervasives_Native.None)
    | uu____4865 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4892)::(a1,uu____4894)::(a2,uu____4896)::[] ->
        let uu____4933 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4933 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4946 -> FStar_Pervasives_Native.None)
    | uu____4947 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4974)::[] -> FStar_Pervasives_Native.Some a1
    | uu____4983 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5007 =
      let uu____5022 =
        let uu____5037 =
          let uu____5052 =
            let uu____5067 =
              let uu____5082 =
                let uu____5097 =
                  let uu____5112 =
                    let uu____5127 =
                      let uu____5142 =
                        let uu____5157 =
                          let uu____5172 =
                            let uu____5187 =
                              let uu____5202 =
                                let uu____5217 =
                                  let uu____5232 =
                                    let uu____5247 =
                                      let uu____5262 =
                                        let uu____5277 =
                                          let uu____5292 =
                                            let uu____5307 =
                                              let uu____5322 =
                                                let uu____5335 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____5335,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a443  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a443)
                                                     (fun a444  ->
                                                        fun a445  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a444 a445))) in
                                              let uu____5342 =
                                                let uu____5357 =
                                                  let uu____5370 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____5370,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a446  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a446)
                                                       (fun a447  ->
                                                          fun a448  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a447 a448))) in
                                                let uu____5377 =
                                                  let uu____5392 =
                                                    let uu____5407 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____5407,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____5416 =
                                                    let uu____5433 =
                                                      let uu____5448 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____5448,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    let uu____5457 =
                                                      let uu____5474 =
                                                        let uu____5493 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"] in
                                                        (uu____5493,
                                                          (Prims.parse_int
                                                             "1"), idstep) in
                                                      [uu____5474] in
                                                    uu____5433 :: uu____5457 in
                                                  uu____5392 :: uu____5416 in
                                                uu____5357 :: uu____5377 in
                                              uu____5322 :: uu____5342 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5307 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5292 in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a449  ->
                                                (Obj.magic arg_as_string)
                                                  a449)
                                             (fun a450  ->
                                                fun a451  ->
                                                  fun a452  ->
                                                    (Obj.magic
                                                       string_compare') a450
                                                      a451 a452)))
                                          :: uu____5277 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a453  ->
                                              (Obj.magic arg_as_bool) a453)
                                           (fun a454  ->
                                              fun a455  ->
                                                (Obj.magic string_of_bool1)
                                                  a454 a455)))
                                        :: uu____5262 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a456  ->
                                            (Obj.magic arg_as_int) a456)
                                         (fun a457  ->
                                            fun a458  ->
                                              (Obj.magic string_of_int1) a457
                                                a458)))
                                      :: uu____5247 in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a459  ->
                                          (Obj.magic arg_as_int) a459)
                                       (fun a460  ->
                                          (Obj.magic arg_as_char) a460)
                                       (fun a461  ->
                                          fun a462  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a461 a462)
                                       (fun a463  ->
                                          fun a464  ->
                                            fun a465  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____5710 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____5710 y)) a463
                                                a464 a465)))
                                    :: uu____5232 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5217 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5202 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5187 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5172 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5157 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5142 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a466  -> (Obj.magic arg_as_int) a466)
                         (fun a467  ->
                            fun a468  ->
                              fun a469  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____5877 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____5877)) a467 a468 a469)))
                      :: uu____5127 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a470  -> (Obj.magic arg_as_int) a470)
                       (fun a471  ->
                          fun a472  ->
                            fun a473  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____5903 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____5903)) a471 a472 a473)))
                    :: uu____5112 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a474  -> (Obj.magic arg_as_int) a474)
                     (fun a475  ->
                        fun a476  ->
                          fun a477  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____5929 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____5929)) a475 a476 a477)))
                  :: uu____5097 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a478  -> (Obj.magic arg_as_int) a478)
                   (fun a479  ->
                      fun a480  ->
                        fun a481  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____5955 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____5955)) a479 a480 a481)))
                :: uu____5082 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5067 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5052 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5037 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5022 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5007 in
  let bounded_arith_ops =
    let bounded_int_types =
      ["Int8";
      "UInt8";
      "Int16";
      "UInt16";
      "Int32";
      "UInt32";
      "Int64";
      "UInt64";
      "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6105 =
        let uu____6106 =
          let uu____6107 = FStar_Syntax_Syntax.as_arg c in [uu____6107] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6106 in
      uu____6105 FStar_Pervasives_Native.None r in
    FStar_All.pipe_right bounded_int_types
      (FStar_List.collect
         (fun m  ->
            let uu____6142 =
              let uu____6155 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
              (uu____6155, (Prims.parse_int "2"),
                (binary_op ()
                   (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                   (fun a483  ->
                      fun a484  ->
                        fun a485  ->
                          (Obj.magic
                             (fun r  ->
                                fun uu____6171  ->
                                  fun uu____6172  ->
                                    match (uu____6171, uu____6172) with
                                    | ((int_to_t1,x),(uu____6191,y)) ->
                                        let uu____6201 =
                                          FStar_BigInt.add_big_int x y in
                                        int_as_bounded r int_to_t1 uu____6201))
                            a483 a484 a485))) in
            let uu____6202 =
              let uu____6217 =
                let uu____6230 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                (uu____6230, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a486  -> (Obj.magic arg_as_bounded_int) a486)
                     (fun a487  ->
                        fun a488  ->
                          fun a489  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6246  ->
                                    fun uu____6247  ->
                                      match (uu____6246, uu____6247) with
                                      | ((int_to_t1,x),(uu____6266,y)) ->
                                          let uu____6276 =
                                            FStar_BigInt.sub_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6276)) a487 a488 a489))) in
              let uu____6277 =
                let uu____6292 =
                  let uu____6305 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                  (uu____6305, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a490  -> (Obj.magic arg_as_bounded_int) a490)
                       (fun a491  ->
                          fun a492  ->
                            fun a493  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6321  ->
                                      fun uu____6322  ->
                                        match (uu____6321, uu____6322) with
                                        | ((int_to_t1,x),(uu____6341,y)) ->
                                            let uu____6351 =
                                              FStar_BigInt.mult_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6351)) a491 a492 a493))) in
                [uu____6292] in
              uu____6217 :: uu____6277 in
            uu____6142 :: uu____6202)) in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6441)::(a1,uu____6443)::(a2,uu____6445)::[] ->
        let uu____6482 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6482 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___111_6488 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___111_6488.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___111_6488.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___112_6492 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_6492.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_6492.FStar_Syntax_Syntax.vars)
                })
         | uu____6493 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6495)::uu____6496::(a1,uu____6498)::(a2,uu____6500)::[] ->
        let uu____6549 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6549 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___111_6555 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___111_6555.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___111_6555.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___112_6559 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___112_6559.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___112_6559.FStar_Syntax_Syntax.vars)
                })
         | uu____6560 -> FStar_Pervasives_Native.None)
    | uu____6561 -> failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  [propositional_equality; hetero_propositional_equality]
let unembed_binder:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____6580 =
        let uu____6581 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6581 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6580
    with | uu____6587 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6591 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6591) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6651  ->
           fun subst1  ->
             match uu____6651 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6692,uu____6693)) ->
                      let uu____6752 = b in
                      (match uu____6752 with
                       | (bv,uu____6760) ->
                           let uu____6761 =
                             let uu____6762 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____6762 in
                           if uu____6761
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____6767 = unembed_binder term1 in
                              match uu____6767 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____6774 =
                                      let uu___115_6775 = bv in
                                      let uu____6776 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___115_6775.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___115_6775.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____6776
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____6774 in
                                  let b_for_x =
                                    let uu____6780 =
                                      let uu____6787 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____6787) in
                                    FStar_Syntax_Syntax.NT uu____6780 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___80_6796  ->
                                         match uu___80_6796 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____6797,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____6799;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____6800;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____6805 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____6806 -> subst1)) env []
let reduce_primops:
  'Auu____6823 'Auu____6824 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6824) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____6823 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____6865 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____6865
          then tm
          else
            (let uu____6867 = FStar_Syntax_Util.head_and_args tm in
             match uu____6867 with
             | (head1,args) ->
                 let uu____6904 =
                   let uu____6905 = FStar_Syntax_Util.un_uinst head1 in
                   uu____6905.FStar_Syntax_Syntax.n in
                 (match uu____6904 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____6909 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____6909 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____6926  ->
                                   let uu____6927 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____6928 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____6935 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____6927 uu____6928 uu____6935);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____6940  ->
                                   let uu____6941 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____6941);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____6944  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____6946 =
                                 prim_step.interpretation psc args in
                               match uu____6946 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____6952  ->
                                         let uu____6953 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____6953);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____6959  ->
                                         let uu____6960 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____6961 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____6960 uu____6961);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____6962 ->
                           (log_primops cfg
                              (fun uu____6966  ->
                                 let uu____6967 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____6967);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____6971  ->
                            let uu____6972 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____6972);
                       (match args with
                        | (a1,uu____6974)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____6991 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7003  ->
                            let uu____7004 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7004);
                       (match args with
                        | (t,uu____7006)::(r,uu____7008)::[] ->
                            let uu____7035 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7035 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___116_7039 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___116_7039.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___116_7039.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7042 -> tm))
                  | uu____7051 -> tm))
let reduce_equality:
  'Auu____7056 'Auu____7057 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7057) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7056 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___117_7095 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___117_7095.tcenv);
           delta_level = (uu___117_7095.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___117_7095.strong);
           memoize_lazy = (uu___117_7095.memoize_lazy)
         }) tm
let maybe_simplify_aux:
  'Auu____7102 'Auu____7103 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7103) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7102 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7145 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7145
          then tm1
          else
            (let w t =
               let uu___118_7157 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___118_7157.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___118_7157.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____7174 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7179 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7179
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7200 =
                 match uu____7200 with
                 | (t1,q) ->
                     let uu____7213 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7213 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7241 -> (t1, q)) in
               let uu____7250 = FStar_Syntax_Util.head_and_args t in
               match uu____7250 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7347;
                         FStar_Syntax_Syntax.vars = uu____7348;_},uu____7349);
                    FStar_Syntax_Syntax.pos = uu____7350;
                    FStar_Syntax_Syntax.vars = uu____7351;_},args)
                 ->
                 let uu____7377 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7377
                 then
                   let uu____7378 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7378 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7433)::
                        (uu____7434,(arg,uu____7436))::[] ->
                        maybe_auto_squash arg
                    | (uu____7501,(arg,uu____7503))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7504)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7569)::uu____7570::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7633::(FStar_Pervasives_Native.Some (false
                                   ),uu____7634)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7697 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____7713 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____7713
                    then
                      let uu____7714 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____7714 with
                      | (FStar_Pervasives_Native.Some (true ),uu____7769)::uu____7770::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____7833::(FStar_Pervasives_Native.Some (true
                                     ),uu____7834)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____7897)::
                          (uu____7898,(arg,uu____7900))::[] ->
                          maybe_auto_squash arg
                      | (uu____7965,(arg,uu____7967))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____7968)::[]
                          -> maybe_auto_squash arg
                      | uu____8033 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8049 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8049
                       then
                         let uu____8050 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8050 with
                         | uu____8105::(FStar_Pervasives_Native.Some (true
                                        ),uu____8106)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8169)::uu____8170::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8233)::
                             (uu____8234,(arg,uu____8236))::[] ->
                             maybe_auto_squash arg
                         | (uu____8301,(p,uu____8303))::(uu____8304,(q,uu____8306))::[]
                             ->
                             let uu____8371 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8371
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8373 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8389 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8389
                          then
                            let uu____8390 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8390 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8445)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8484)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8523 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8539 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8539
                             then
                               match args with
                               | (t,uu____8541)::[] ->
                                   let uu____8558 =
                                     let uu____8559 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8559.FStar_Syntax_Syntax.n in
                                   (match uu____8558 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8562::[],body,uu____8564) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8591 -> tm1)
                                    | uu____8594 -> tm1)
                               | (uu____8595,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8596))::
                                   (t,uu____8598)::[] ->
                                   let uu____8637 =
                                     let uu____8638 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8638.FStar_Syntax_Syntax.n in
                                   (match uu____8637 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8641::[],body,uu____8643) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8670 -> tm1)
                                    | uu____8673 -> tm1)
                               | uu____8674 -> tm1
                             else
                               (let uu____8684 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8684
                                then
                                  match args with
                                  | (t,uu____8686)::[] ->
                                      let uu____8703 =
                                        let uu____8704 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8704.FStar_Syntax_Syntax.n in
                                      (match uu____8703 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8707::[],body,uu____8709)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8736 -> tm1)
                                       | uu____8739 -> tm1)
                                  | (uu____8740,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____8741))::(t,uu____8743)::[] ->
                                      let uu____8782 =
                                        let uu____8783 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____8783.FStar_Syntax_Syntax.n in
                                      (match uu____8782 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____8786::[],body,uu____8788)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____8815 -> tm1)
                                       | uu____8818 -> tm1)
                                  | uu____8819 -> tm1
                                else
                                  (let uu____8829 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____8829
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8830;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8831;_},uu____8832)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____8849;
                                          FStar_Syntax_Syntax.vars =
                                            uu____8850;_},uu____8851)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____8868 -> tm1
                                   else
                                     (let uu____8878 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____8878 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____8898 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8908;
                    FStar_Syntax_Syntax.vars = uu____8909;_},args)
                 ->
                 let uu____8931 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____8931
                 then
                   let uu____8932 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____8932 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8987)::
                        (uu____8988,(arg,uu____8990))::[] ->
                        maybe_auto_squash arg
                    | (uu____9055,(arg,uu____9057))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9058)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9123)::uu____9124::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9187::(FStar_Pervasives_Native.Some (false
                                   ),uu____9188)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9251 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9267 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9267
                    then
                      let uu____9268 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9268 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9323)::uu____9324::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9387::(FStar_Pervasives_Native.Some (true
                                     ),uu____9388)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9451)::
                          (uu____9452,(arg,uu____9454))::[] ->
                          maybe_auto_squash arg
                      | (uu____9519,(arg,uu____9521))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9522)::[]
                          -> maybe_auto_squash arg
                      | uu____9587 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9603 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9603
                       then
                         let uu____9604 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9604 with
                         | uu____9659::(FStar_Pervasives_Native.Some (true
                                        ),uu____9660)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9723)::uu____9724::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9787)::
                             (uu____9788,(arg,uu____9790))::[] ->
                             maybe_auto_squash arg
                         | (uu____9855,(p,uu____9857))::(uu____9858,(q,uu____9860))::[]
                             ->
                             let uu____9925 = FStar_Syntax_Util.term_eq p q in
                             (if uu____9925
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9927 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9943 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____9943
                          then
                            let uu____9944 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____9944 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9999)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10038)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10077 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10093 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10093
                             then
                               match args with
                               | (t,uu____10095)::[] ->
                                   let uu____10112 =
                                     let uu____10113 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10113.FStar_Syntax_Syntax.n in
                                   (match uu____10112 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10116::[],body,uu____10118) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10145 -> tm1)
                                    | uu____10148 -> tm1)
                               | (uu____10149,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10150))::
                                   (t,uu____10152)::[] ->
                                   let uu____10191 =
                                     let uu____10192 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10192.FStar_Syntax_Syntax.n in
                                   (match uu____10191 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10195::[],body,uu____10197) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10224 -> tm1)
                                    | uu____10227 -> tm1)
                               | uu____10228 -> tm1
                             else
                               (let uu____10238 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10238
                                then
                                  match args with
                                  | (t,uu____10240)::[] ->
                                      let uu____10257 =
                                        let uu____10258 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10258.FStar_Syntax_Syntax.n in
                                      (match uu____10257 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10261::[],body,uu____10263)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10290 -> tm1)
                                       | uu____10293 -> tm1)
                                  | (uu____10294,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10295))::(t,uu____10297)::[] ->
                                      let uu____10336 =
                                        let uu____10337 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10337.FStar_Syntax_Syntax.n in
                                      (match uu____10336 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10340::[],body,uu____10342)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10369 -> tm1)
                                       | uu____10372 -> tm1)
                                  | uu____10373 -> tm1
                                else
                                  (let uu____10383 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10383
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10384;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10385;_},uu____10386)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10403;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10404;_},uu____10405)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10422 -> tm1
                                   else
                                     (let uu____10432 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10432 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10452 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10461 -> tm1)
let maybe_simplify:
  'Auu____10468 'Auu____10469 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10469) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10468 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10512 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10512
           then
             let uu____10513 = FStar_Syntax_Print.term_to_string tm in
             let uu____10514 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10513 uu____10514
           else ());
          tm'
let is_norm_request:
  'Auu____10520 .
    FStar_Syntax_Syntax.term -> 'Auu____10520 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10533 =
        let uu____10540 =
          let uu____10541 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10541.FStar_Syntax_Syntax.n in
        (uu____10540, args) in
      match uu____10533 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10547::uu____10548::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10552::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10557::uu____10558::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10561 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___81_10572  ->
    match uu___81_10572 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10578 =
          let uu____10581 =
            let uu____10582 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10582 in
          [uu____10581] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10578
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10597 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10597) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10635 =
          let uu____10638 =
            let uu____10643 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10643 s in
          FStar_All.pipe_right uu____10638 FStar_Util.must in
        FStar_All.pipe_right uu____10635 tr_norm_steps in
      match args with
      | uu____10668::(tm,uu____10670)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____10693)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____10708)::uu____10709::(tm,uu____10711)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____10751 =
              let uu____10754 = full_norm steps in parse_steps uu____10754 in
            Beta :: uu____10751 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____10763 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___82_10780  ->
    match uu___82_10780 with
    | (App
        (uu____10783,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10784;
                       FStar_Syntax_Syntax.vars = uu____10785;_},uu____10786,uu____10787))::uu____10788
        -> true
    | uu____10795 -> false
let firstn:
  'Auu____10801 .
    Prims.int ->
      'Auu____10801 Prims.list ->
        ('Auu____10801 Prims.list,'Auu____10801 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____10837,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10838;
                         FStar_Syntax_Syntax.vars = uu____10839;_},uu____10840,uu____10841))::uu____10842
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____10849 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            (let uu____10991 =
               FStar_TypeChecker_Env.debug cfg.tcenv
                 (FStar_Options.Other "NormDelayed") in
             if uu____10991
             then
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____10992 ->
                   let uu____11017 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11017
               | uu____11018 -> ()
             else ());
            FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11027  ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               let uu____11029 = FStar_Syntax_Print.tag_of_term t2 in
               let uu____11030 = FStar_Syntax_Print.term_to_string t2 in
               let uu____11031 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11038 =
                 let uu____11039 =
                   let uu____11042 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11042 in
                 stack_to_string uu____11039 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11029 uu____11030 uu____11031 uu____11038);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11065 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11066 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11067;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11068;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11071;
                 FStar_Syntax_Syntax.fv_delta = uu____11072;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11073;
                 FStar_Syntax_Syntax.fv_delta = uu____11074;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11075);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11083 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11083 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11089  ->
                     let uu____11090 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11091 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11090 uu____11091);
                if b
                then
                  (let uu____11092 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11092 t1 fv)
                else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (FStar_List.contains NoDeltaSteps cfg.steps)))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___119_11131 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___119_11131.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___119_11131.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11164 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11164) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___120_11172 = cfg in
                 let uu____11173 =
                   FStar_List.filter
                     (fun uu___83_11176  ->
                        match uu___83_11176 with
                        | UnfoldOnly uu____11177 -> false
                        | NoDeltaSteps  -> false
                        | uu____11180 -> true) cfg.steps in
                 {
                   steps = uu____11173;
                   tcenv = (uu___120_11172.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___120_11172.primitive_steps);
                   strong = (uu___120_11172.strong);
                   memoize_lazy = (uu___120_11172.memoize_lazy)
                 } in
               let uu____11181 = get_norm_request (norm cfg' env []) args in
               (match uu____11181 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11197 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___84_11202  ->
                                match uu___84_11202 with
                                | UnfoldUntil uu____11203 -> true
                                | UnfoldOnly uu____11204 -> true
                                | uu____11207 -> false)) in
                      if uu____11197
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___121_11212 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___121_11212.tcenv);
                        delta_level;
                        primitive_steps = (uu___121_11212.primitive_steps);
                        strong = (uu___121_11212.strong);
                        memoize_lazy = (uu___121_11212.memoize_lazy)
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11219 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11219
                      then
                        let uu____11222 =
                          let uu____11223 =
                            let uu____11228 = FStar_Util.now () in
                            (t1, uu____11228) in
                          Debug uu____11223 in
                        uu____11222 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11232 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11232
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11239 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11239
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11242 =
                      let uu____11249 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11249, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11242 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___85_11262  ->
                         match uu___85_11262 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11265 =
                   (FStar_List.mem FStar_TypeChecker_Env.UnfoldTac
                      cfg.delta_level)
                     &&
                     ((((((((((FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.and_lid)
                                ||
                                (FStar_Syntax_Syntax.fv_eq_lid f
                                   FStar_Parser_Const.or_lid))
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid f
                                  FStar_Parser_Const.imp_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.forall_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Parser_Const.squash_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid f
                               FStar_Parser_Const.exists_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid f
                              FStar_Parser_Const.eq2_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid f
                             FStar_Parser_Const.eq3_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid f
                            FStar_Parser_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Parser_Const.false_lid)) in
                 if uu____11265
                 then false
                 else
                   (let uu____11267 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___86_11274  ->
                              match uu___86_11274 with
                              | UnfoldOnly uu____11275 -> true
                              | uu____11278 -> false)) in
                    match uu____11267 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11282 -> should_delta) in
               (log cfg
                  (fun uu____11290  ->
                     let uu____11291 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11292 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11293 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11291 uu____11292 uu____11293);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11296 = lookup_bvar env x in
               (match uu____11296 with
                | Univ uu____11299 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11348 = FStar_ST.op_Bang r in
                      (match uu____11348 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11466  ->
                                 let uu____11467 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11468 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11467
                                   uu____11468);
                            (let uu____11469 =
                               let uu____11470 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11470.FStar_Syntax_Syntax.n in
                             match uu____11469 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11473 ->
                                 norm cfg env2 stack t'
                             | uu____11490 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11560)::uu____11561 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11570)::uu____11571 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11581,uu____11582))::stack_rest ->
                    (match c with
                     | Univ uu____11586 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11595 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11616  ->
                                    let uu____11617 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11617);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11657  ->
                                    let uu____11658 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11658);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____11736  ->
                          let uu____11737 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____11737);
                     norm cfg env stack1 t1)
                | (Debug uu____11738)::uu____11739 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11746 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11746
                    else
                      (let uu____11748 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11748 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11790  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11818 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11818
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11828 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11828)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_11833 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_11833.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_11833.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11834 -> lopt in
                           (log cfg
                              (fun uu____11840  ->
                                 let uu____11841 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11841);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_11850 = cfg in
                               {
                                 steps = (uu___123_11850.steps);
                                 tcenv = (uu___123_11850.tcenv);
                                 delta_level = (uu___123_11850.delta_level);
                                 primitive_steps =
                                   (uu___123_11850.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_11850.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11861)::uu____11862 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11869 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11869
                    else
                      (let uu____11871 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11871 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11913  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____11941 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____11941
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11951 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____11951)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_11956 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_11956.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_11956.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11957 -> lopt in
                           (log cfg
                              (fun uu____11963  ->
                                 let uu____11964 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11964);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_11973 = cfg in
                               {
                                 steps = (uu___123_11973.steps);
                                 tcenv = (uu___123_11973.tcenv);
                                 delta_level = (uu___123_11973.delta_level);
                                 primitive_steps =
                                   (uu___123_11973.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_11973.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11984)::uu____11985 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____11996 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____11996
                    else
                      (let uu____11998 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____11998 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12040  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12068 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12068
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12078 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12078)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12083 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12083.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12083.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12084 -> lopt in
                           (log cfg
                              (fun uu____12090  ->
                                 let uu____12091 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12091);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12100 = cfg in
                               {
                                 steps = (uu___123_12100.steps);
                                 tcenv = (uu___123_12100.tcenv);
                                 delta_level = (uu___123_12100.delta_level);
                                 primitive_steps =
                                   (uu___123_12100.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12100.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12111)::uu____12112 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12123 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12123
                    else
                      (let uu____12125 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12125 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12167  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12195 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12195
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12205 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12205)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12210 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12210.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12210.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12211 -> lopt in
                           (log cfg
                              (fun uu____12217  ->
                                 let uu____12218 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12218);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12227 = cfg in
                               {
                                 steps = (uu___123_12227.steps);
                                 tcenv = (uu___123_12227.tcenv);
                                 delta_level = (uu___123_12227.delta_level);
                                 primitive_steps =
                                   (uu___123_12227.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12227.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12238)::uu____12239 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12254 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12254
                    else
                      (let uu____12256 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12256 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12298  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12326 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12326
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12336 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12336)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12341 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12341.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12341.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12342 -> lopt in
                           (log cfg
                              (fun uu____12348  ->
                                 let uu____12349 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12349);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12358 = cfg in
                               {
                                 steps = (uu___123_12358.steps);
                                 tcenv = (uu___123_12358.tcenv);
                                 delta_level = (uu___123_12358.delta_level);
                                 primitive_steps =
                                   (uu___123_12358.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12358.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12369 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12369
                    else
                      (let uu____12371 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12371 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12413  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12441 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12441
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12451 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12451)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___122_12456 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___122_12456.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___122_12456.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12457 -> lopt in
                           (log cfg
                              (fun uu____12463  ->
                                 let uu____12464 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12464);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___123_12473 = cfg in
                               {
                                 steps = (uu___123_12473.steps);
                                 tcenv = (uu___123_12473.tcenv);
                                 delta_level = (uu___123_12473.delta_level);
                                 primitive_steps =
                                   (uu___123_12473.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___123_12473.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____12522  ->
                         fun stack1  ->
                           match uu____12522 with
                           | (a,aq) ->
                               let uu____12534 =
                                 let uu____12535 =
                                   let uu____12542 =
                                     let uu____12543 =
                                       let uu____12574 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12574, false) in
                                     Clos uu____12543 in
                                   (uu____12542, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12535 in
                               uu____12534 :: stack1) args) in
               (log cfg
                  (fun uu____12658  ->
                     let uu____12659 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12659);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains Weak cfg.steps
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___124_12695 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___124_12695.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___124_12695.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____12696 ->
                      let uu____12701 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12701)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____12704 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____12704 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____12735 =
                          let uu____12736 =
                            let uu____12743 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___125_12745 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___125_12745.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___125_12745.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12743) in
                          FStar_Syntax_Syntax.Tm_refine uu____12736 in
                        mk uu____12735 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____12764 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____12764
               else
                 (let uu____12766 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____12766 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12774 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12798  -> dummy :: env1) env) in
                        norm_comp cfg uu____12774 c1 in
                      let t2 =
                        let uu____12820 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____12820 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12879)::uu____12880 ->
                    (log cfg
                       (fun uu____12891  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12892)::uu____12893 ->
                    (log cfg
                       (fun uu____12904  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12905,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12906;
                                   FStar_Syntax_Syntax.vars = uu____12907;_},uu____12908,uu____12909))::uu____12910
                    ->
                    (log cfg
                       (fun uu____12919  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12920)::uu____12921 ->
                    (log cfg
                       (fun uu____12932  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12933 ->
                    (log cfg
                       (fun uu____12936  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____12940  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12957 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____12957
                         | FStar_Util.Inr c ->
                             let uu____12965 = norm_comp cfg env c in
                             FStar_Util.Inr uu____12965 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12978 =
                               let uu____12979 =
                                 let uu____13006 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13006, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12979 in
                             mk uu____12978 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13025 ->
                           let uu____13026 =
                             let uu____13027 =
                               let uu____13028 =
                                 let uu____13055 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13055, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13028 in
                             mk uu____13027 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13026))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (FStar_List.contains CompressUvars cfg.steps)
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____13165 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13165 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___126_13185 = cfg in
                               let uu____13186 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___126_13185.steps);
                                 tcenv = uu____13186;
                                 delta_level = (uu___126_13185.delta_level);
                                 primitive_steps =
                                   (uu___126_13185.primitive_steps);
                                 strong = (uu___126_13185.strong);
                                 memoize_lazy = (uu___126_13185.memoize_lazy)
                               } in
                             let norm1 t2 =
                               let uu____13191 =
                                 let uu____13192 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13192 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13191 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___127_13195 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___127_13195.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___127_13195.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13196 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13196
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13207,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13208;
                               FStar_Syntax_Syntax.lbunivs = uu____13209;
                               FStar_Syntax_Syntax.lbtyp = uu____13210;
                               FStar_Syntax_Syntax.lbeff = uu____13211;
                               FStar_Syntax_Syntax.lbdef = uu____13212;_}::uu____13213),uu____13214)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13250 =
                 (let uu____13253 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13253) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) ||
                       (FStar_Syntax_Util.is_ghost_effect n1))
                      &&
                      (let uu____13255 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       Prims.op_Negation uu____13255)) in
               if uu____13250
               then
                 let binder =
                   let uu____13257 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13257 in
                 let env1 =
                   let uu____13267 =
                     let uu____13274 =
                       let uu____13275 =
                         let uu____13306 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13306,
                           false) in
                       Clos uu____13275 in
                     ((FStar_Pervasives_Native.Some binder), uu____13274) in
                   uu____13267 :: env in
                 (log cfg
                    (fun uu____13399  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13401 =
                    let uu____13406 =
                      let uu____13407 =
                        let uu____13408 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13408
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13407] in
                    FStar_Syntax_Subst.open_term uu____13406 body in
                  match uu____13401 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13417  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13425 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13425 in
                          FStar_Util.Inl
                            (let uu___128_13435 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___128_13435.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___128_13435.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13438  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___129_13440 = lb in
                           let uu____13441 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___129_13440.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___129_13440.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13441
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13476  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___130_13499 = cfg in
                           {
                             steps = (uu___130_13499.steps);
                             tcenv = (uu___130_13499.tcenv);
                             delta_level = (uu___130_13499.delta_level);
                             primitive_steps =
                               (uu___130_13499.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___130_13499.memoize_lazy)
                           } in
                         log cfg1
                           (fun uu____13502  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- body\n");
                         norm cfg1 env'
                           ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____13519 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13519 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13555 =
                               let uu___131_13556 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_13556.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_13556.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13555 in
                           let uu____13557 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13557 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13583 =
                                   FStar_List.map (fun uu____13599  -> dummy)
                                     lbs1 in
                                 let uu____13600 =
                                   let uu____13609 =
                                     FStar_List.map
                                       (fun uu____13629  -> dummy) xs1 in
                                   FStar_List.append uu____13609 env in
                                 FStar_List.append uu____13583 uu____13600 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13653 =
                                       let uu___132_13654 = rc in
                                       let uu____13655 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___132_13654.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13655;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___132_13654.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13653
                                 | uu____13662 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___133_13666 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___133_13666.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___133_13666.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____13676 =
                        FStar_List.map (fun uu____13692  -> dummy) lbs2 in
                      FStar_List.append uu____13676 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____13700 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____13700 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___134_13716 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___134_13716.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___134_13716.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____13743 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____13743
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13762 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13838  ->
                        match uu____13838 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___135_13959 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___135_13959.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___135_13959.FStar_Syntax_Syntax.sort)
                              } in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____13762 with
                | (rec_env,memos,uu____14172) ->
                    let uu____14225 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____14536 =
                               let uu____14543 =
                                 let uu____14544 =
                                   let uu____14575 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14575, false) in
                                 Clos uu____14544 in
                               (FStar_Pervasives_Native.None, uu____14543) in
                             uu____14536 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____14685  ->
                     let uu____14686 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14686);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14708 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14710::uu____14711 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14716) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____14717 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14748 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____14762 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14762
                              | uu____14773 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14777 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14803 ->
               let t2 = FStar_Syntax_Subst.compress t1 in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14821 ->
                    let uu____14838 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.contains CheckNoUvars) in
                    if uu____14838
                    then
                      let uu____14839 =
                        let uu____14840 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos in
                        let uu____14841 =
                          FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14840 uu____14841 in
                      failwith uu____14839
                    else rebuild cfg env stack t2
                | uu____14843 -> norm cfg env stack t2))
and do_unfold_fv:
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun f  ->
            let r_env =
              let uu____14852 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____14852 in
            let uu____14853 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____14853 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____14866  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____14877  ->
                      let uu____14878 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____14879 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____14878
                        uu____14879);
                 (let t1 =
                    let uu____14881 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____14883 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____14883) in
                    if uu____14881
                    then t
                    else
                      FStar_Syntax_Subst.set_use_range
                        (FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                        t in
                  let n1 = FStar_List.length us in
                  if n1 > (Prims.parse_int "0")
                  then
                    match stack with
                    | (UnivArgs (us',uu____14893))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____14948 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____14951 ->
                        let uu____14954 =
                          let uu____14955 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____14955 in
                        failwith uu____14954
                  else norm cfg env stack t1))
and reduce_impure_comp:
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t in
              let stack1 = (Cfg cfg) :: stack in
              let cfg1 =
                let uu____14976 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____14976
                then
                  let uu___136_14977 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___136_14977.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___136_14977.primitive_steps);
                    strong = (uu___136_14977.strong);
                    memoize_lazy = (uu___136_14977.memoize_lazy)
                  }
                else
                  (let uu___137_14979 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___137_14979.tcenv);
                     delta_level = (uu___137_14979.delta_level);
                     primitive_steps = (uu___137_14979.primitive_steps);
                     strong = (uu___137_14979.strong);
                     memoize_lazy = (uu___137_14979.memoize_lazy)
                   }) in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
              norm cfg1 env
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1
and do_reify_monadic:
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head2 = FStar_Syntax_Util.unascribe head1 in
                log cfg
                  (fun uu____15008  ->
                     let uu____15009 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15010 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15009
                       uu____15010);
                (let uu____15011 =
                   let uu____15012 = FStar_Syntax_Subst.compress head2 in
                   uu____15012.FStar_Syntax_Syntax.n in
                 match uu____15011 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15030 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15030 with
                      | (uu____15031,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15037 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15045 =
                                   let uu____15046 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15046.FStar_Syntax_Syntax.n in
                                 match uu____15045 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15052,uu____15053))
                                     ->
                                     let uu____15062 =
                                       let uu____15063 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15063.FStar_Syntax_Syntax.n in
                                     (match uu____15062 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15069,msrc,uu____15071))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15080 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15080
                                      | uu____15081 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15082 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15083 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15083 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___138_15088 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___138_15088.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___138_15088.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___138_15088.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15089 = FStar_List.tl stack in
                                    let uu____15090 =
                                      let uu____15091 =
                                        let uu____15094 =
                                          let uu____15095 =
                                            let uu____15108 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15108) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15095 in
                                        FStar_Syntax_Syntax.mk uu____15094 in
                                      uu____15091
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15089 uu____15090
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15124 =
                                      let uu____15125 = is_return body in
                                      match uu____15125 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15129;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15130;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15135 -> false in
                                    if uu____15124
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head2.FStar_Syntax_Syntax.pos in
                                       let head3 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         } in
                                       let body2 =
                                         let uu____15158 =
                                           let uu____15161 =
                                             let uu____15162 =
                                               let uu____15179 =
                                                 let uu____15182 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15182] in
                                               (uu____15179, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15162 in
                                           FStar_Syntax_Syntax.mk uu____15161 in
                                         uu____15158
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15198 =
                                           let uu____15199 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15199.FStar_Syntax_Syntax.n in
                                         match uu____15198 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15205::uu____15206::[])
                                             ->
                                             let uu____15213 =
                                               let uu____15216 =
                                                 let uu____15217 =
                                                   let uu____15224 =
                                                     let uu____15227 =
                                                       let uu____15228 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15228 in
                                                     let uu____15229 =
                                                       let uu____15232 =
                                                         let uu____15233 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15233 in
                                                       [uu____15232] in
                                                     uu____15227 ::
                                                       uu____15229 in
                                                   (bind1, uu____15224) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15217 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15216 in
                                             uu____15213
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15241 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15247 =
                                           let uu____15250 =
                                             let uu____15251 =
                                               let uu____15266 =
                                                 let uu____15269 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15270 =
                                                   let uu____15273 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15274 =
                                                     let uu____15277 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15278 =
                                                       let uu____15281 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15282 =
                                                         let uu____15285 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15286 =
                                                           let uu____15289 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15289] in
                                                         uu____15285 ::
                                                           uu____15286 in
                                                       uu____15281 ::
                                                         uu____15282 in
                                                     uu____15277 ::
                                                       uu____15278 in
                                                   uu____15273 :: uu____15274 in
                                                 uu____15269 :: uu____15270 in
                                               (bind_inst, uu____15266) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15251 in
                                           FStar_Syntax_Syntax.mk uu____15250 in
                                         uu____15247
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15300  ->
                                            let uu____15301 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15301);
                                       (let uu____15302 = FStar_List.tl stack in
                                        norm cfg env uu____15302 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15326 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15326 with
                      | (uu____15327,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15362 =
                                  let uu____15363 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15363.FStar_Syntax_Syntax.n in
                                match uu____15362 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15369) -> t2
                                | uu____15374 -> head3 in
                              let uu____15375 =
                                let uu____15376 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15376.FStar_Syntax_Syntax.n in
                              match uu____15375 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15382 -> FStar_Pervasives_Native.None in
                            let uu____15383 = maybe_extract_fv head3 in
                            match uu____15383 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15393 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15393
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15398 = maybe_extract_fv head4 in
                                  match uu____15398 with
                                  | FStar_Pervasives_Native.Some uu____15403
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15404 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15409 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15424 =
                              match uu____15424 with
                              | (e,q) ->
                                  let uu____15431 =
                                    let uu____15432 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15432.FStar_Syntax_Syntax.n in
                                  (match uu____15431 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15447 -> false) in
                            let uu____15448 =
                              let uu____15449 =
                                let uu____15456 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15456 :: args in
                              FStar_Util.for_some is_arg_impure uu____15449 in
                            if uu____15448
                            then
                              let uu____15461 =
                                let uu____15462 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15462 in
                              failwith uu____15461
                            else ());
                           (let uu____15464 = maybe_unfold_action head_app in
                            match uu____15464 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args)) in
                                let body1 =
                                  match found_action with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Syntax_Util.mk_reify body
                                  | FStar_Pervasives_Native.Some (false ) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body in
                                let uu____15501 = FStar_List.tl stack in
                                norm cfg env uu____15501 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15503) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15527 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15527 in
                     (log cfg
                        (fun uu____15531  ->
                           let uu____15532 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15532);
                      (let uu____15533 = FStar_List.tl stack in
                       norm cfg env uu____15533 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15535) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15660  ->
                               match uu____15660 with
                               | (pat,wopt,tm) ->
                                   let uu____15708 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15708))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____15740 = FStar_List.tl stack in
                     norm cfg env uu____15740 tm
                 | uu____15741 -> fallback ())
and reify_lift:
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv in
            log cfg
              (fun uu____15755  ->
                 let uu____15756 = FStar_Ident.string_of_lid msrc in
                 let uu____15757 = FStar_Ident.string_of_lid mtgt in
                 let uu____15758 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15756
                   uu____15757 uu____15758);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____15760 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____15760 with
               | (uu____15761,return_repr) ->
                   let return_inst =
                     let uu____15770 =
                       let uu____15771 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____15771.FStar_Syntax_Syntax.n in
                     match uu____15770 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15777::[]) ->
                         let uu____15784 =
                           let uu____15787 =
                             let uu____15788 =
                               let uu____15795 =
                                 let uu____15798 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____15798] in
                               (return_tm, uu____15795) in
                             FStar_Syntax_Syntax.Tm_uinst uu____15788 in
                           FStar_Syntax_Syntax.mk uu____15787 in
                         uu____15784 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15806 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____15809 =
                     let uu____15812 =
                       let uu____15813 =
                         let uu____15828 =
                           let uu____15831 = FStar_Syntax_Syntax.as_arg t in
                           let uu____15832 =
                             let uu____15835 = FStar_Syntax_Syntax.as_arg e in
                             [uu____15835] in
                           uu____15831 :: uu____15832 in
                         (return_inst, uu____15828) in
                       FStar_Syntax_Syntax.Tm_app uu____15813 in
                     FStar_Syntax_Syntax.mk uu____15812 in
                   uu____15809 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____15844 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____15844 with
               | FStar_Pervasives_Native.None  ->
                   let uu____15847 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____15847
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15848;
                     FStar_TypeChecker_Env.mtarget = uu____15849;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15850;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____15865;
                     FStar_TypeChecker_Env.mtarget = uu____15866;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____15867;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____15891 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____15892 = FStar_Syntax_Util.mk_reify e in
                   lift uu____15891 t FStar_Syntax_Syntax.tun uu____15892)
and norm_pattern_args:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____15948  ->
                   match uu____15948 with
                   | (a,imp) ->
                       let uu____15959 = norm cfg env [] a in
                       (uu____15959, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___139_15973 = comp in
            let uu____15974 =
              let uu____15975 =
                let uu____15984 = norm cfg env [] t in
                let uu____15985 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____15984, uu____15985) in
              FStar_Syntax_Syntax.Total uu____15975 in
            {
              FStar_Syntax_Syntax.n = uu____15974;
              FStar_Syntax_Syntax.pos =
                (uu___139_15973.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___139_15973.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___140_16000 = comp in
            let uu____16001 =
              let uu____16002 =
                let uu____16011 = norm cfg env [] t in
                let uu____16012 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16011, uu____16012) in
              FStar_Syntax_Syntax.GTotal uu____16002 in
            {
              FStar_Syntax_Syntax.n = uu____16001;
              FStar_Syntax_Syntax.pos =
                (uu___140_16000.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___140_16000.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16064  ->
                      match uu____16064 with
                      | (a,i) ->
                          let uu____16075 = norm cfg env [] a in
                          (uu____16075, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___87_16086  ->
                      match uu___87_16086 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16090 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16090
                      | f -> f)) in
            let uu___141_16094 = comp in
            let uu____16095 =
              let uu____16096 =
                let uu___142_16097 = ct in
                let uu____16098 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16099 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16102 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16098;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___142_16097.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16099;
                  FStar_Syntax_Syntax.effect_args = uu____16102;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16096 in
            {
              FStar_Syntax_Syntax.n = uu____16095;
              FStar_Syntax_Syntax.pos =
                (uu___141_16094.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___141_16094.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16113  ->
        match uu____16113 with
        | (x,imp) ->
            let uu____16116 =
              let uu___143_16117 = x in
              let uu____16118 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___143_16117.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___143_16117.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16118
              } in
            (uu____16116, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16124 =
          FStar_List.fold_left
            (fun uu____16142  ->
               fun b  ->
                 match uu____16142 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16124 with | (nbs,uu____16182) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____16198 =
              let uu___144_16199 = rc in
              let uu____16200 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___144_16199.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16200;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___144_16199.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16198
        | uu____16207 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16220  ->
               let uu____16221 = FStar_Syntax_Print.tag_of_term t in
               let uu____16222 = FStar_Syntax_Print.term_to_string t in
               let uu____16223 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16230 =
                 let uu____16231 =
                   let uu____16234 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16234 in
                 stack_to_string uu____16231 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16221 uu____16222 uu____16223 uu____16230);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16263 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16263
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16265 =
                     let uu____16266 =
                       let uu____16267 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16267 in
                     FStar_Util.string_of_int uu____16266 in
                   let uu____16272 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16273 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16265 uu____16272 uu____16273
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16327  ->
                     let uu____16328 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16328);
                rebuild cfg env stack1 t)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r in
               rebuild cfg env' stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs in
               let lopt1 = norm_lcomp_opt cfg env'' lopt in
               let uu____16364 =
                 let uu___145_16365 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___145_16365.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___145_16365.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16364
           | (Arg (Univ uu____16366,uu____16367,uu____16368))::uu____16369 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16372,uu____16373))::uu____16374 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16390),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16443  ->
                     let uu____16444 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16444);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains HNF cfg.steps
                   then
                     let arg = closure_as_term cfg env_arg tm in
                     let t1 =
                       FStar_Syntax_Syntax.extend_app t (arg, aq)
                         FStar_Pervasives_Native.None r in
                     rebuild cfg env_arg stack1 t1
                   else
                     (let stack2 = (App (env, t, aq, r)) :: stack1 in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____16454 = FStar_ST.op_Bang m in
                   match uu____16454 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains HNF cfg.steps
                       then
                         let arg = closure_as_term cfg env_arg tm in
                         let t1 =
                           FStar_Syntax_Syntax.extend_app t (arg, aq)
                             FStar_Pervasives_Native.None r in
                         rebuild cfg env_arg stack1 t1
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t, aq, r))
                            :: stack1 in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____16591,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____16638 =
                 log cfg
                   (fun uu____16642  ->
                      let uu____16643 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16643);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____16647 =
                 let uu____16648 = FStar_Syntax_Subst.compress t in
                 uu____16648.FStar_Syntax_Syntax.n in
               (match uu____16647 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16675 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____16675 in
                    (log cfg
                       (fun uu____16679  ->
                          let uu____16680 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16680);
                     (let uu____16681 = FStar_List.tl stack in
                      norm cfg env1 uu____16681 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16682);
                       FStar_Syntax_Syntax.pos = uu____16683;
                       FStar_Syntax_Syntax.vars = uu____16684;_},(e,uu____16686)::[])
                    -> norm cfg env1 stack' e
                | uu____16715 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16726 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16726
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____16738  ->
                     let uu____16739 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____16739);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____16744 =
                   log cfg
                     (fun uu____16749  ->
                        let uu____16750 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____16751 =
                          let uu____16752 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____16769  ->
                                    match uu____16769 with
                                    | (p,uu____16779,uu____16780) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____16752
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____16750 uu____16751);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___88_16797  ->
                                match uu___88_16797 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____16798 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___146_16802 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___146_16802.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___146_16802.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___146_16802.memoize_lazy)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____16834 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____16855 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____16915  ->
                                    fun uu____16916  ->
                                      match (uu____16915, uu____16916) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17007 = norm_pat env3 p1 in
                                          (match uu____17007 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____16855 with
                           | (pats1,env3) ->
                               ((let uu___147_17089 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___147_17089.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___148_17108 = x in
                            let uu____17109 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17108.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17108.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17109
                            } in
                          ((let uu___149_17123 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___149_17123.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___150_17134 = x in
                            let uu____17135 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___150_17134.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___150_17134.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17135
                            } in
                          ((let uu___151_17149 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___151_17149.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___152_17165 = x in
                            let uu____17166 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___152_17165.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___152_17165.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17166
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___153_17173 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___153_17173.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17183 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17197 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17197 with
                                  | (p,wopt,e) ->
                                      let uu____17217 = norm_pat env1 p in
                                      (match uu____17217 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17242 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17242 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17248 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17248) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17258) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17263 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17264;
                         FStar_Syntax_Syntax.fv_delta = uu____17265;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17266;
                         FStar_Syntax_Syntax.fv_delta = uu____17267;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17268);_}
                       -> true
                   | uu____17275 -> false in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                   let uu____17420 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17420 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17507 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17546 ->
                                 let uu____17547 =
                                   let uu____17548 = is_cons head1 in
                                   Prims.op_Negation uu____17548 in
                                 FStar_Util.Inr uu____17547)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17573 =
                              let uu____17574 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17574.FStar_Syntax_Syntax.n in
                            (match uu____17573 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17592 ->
                                 let uu____17593 =
                                   let uu____17594 = is_cons head1 in
                                   Prims.op_Negation uu____17594 in
                                 FStar_Util.Inr uu____17593))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17663)::rest_a,(p1,uu____17666)::rest_p) ->
                       let uu____17710 = matches_pat t1 p1 in
                       (match uu____17710 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____17759 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____17865 = matches_pat scrutinee1 p1 in
                       (match uu____17865 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____17905  ->
                                  let uu____17906 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____17907 =
                                    let uu____17908 =
                                      FStar_List.map
                                        (fun uu____17918  ->
                                           match uu____17918 with
                                           | (uu____17923,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____17908
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____17906 uu____17907);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____17954  ->
                                       match uu____17954 with
                                       | (bv,t1) ->
                                           let uu____17977 =
                                             let uu____17984 =
                                               let uu____17987 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____17987 in
                                             let uu____17988 =
                                               let uu____17989 =
                                                 let uu____18020 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18020, false) in
                                               Clos uu____17989 in
                                             (uu____17984, uu____17988) in
                                           uu____17977 :: env2) env1 s in
                              let uu____18137 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18137))) in
                 let uu____18138 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18138
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___89_18159  ->
                match uu___89_18159 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18163 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18169 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true
      }
let normalize_with_primitive_steps:
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e in
          let c1 =
            let uu___154_18194 = config s e in
            {
              steps = (uu___154_18194.steps);
              tcenv = (uu___154_18194.tcenv);
              delta_level = (uu___154_18194.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___154_18194.strong);
              memoize_lazy = (uu___154_18194.memoize_lazy)
            } in
          norm c1 [] [] t
let normalize:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t
let normalize_comp:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____18219 = config s e in norm_comp uu____18219 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18232 = config [] env in norm_universe uu____18232 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env in
      let non_info t =
        let uu____18250 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18250 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18257 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___155_18276 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___155_18276.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___155_18276.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18283 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18283
          then
            let ct1 =
              match downgrade_ghost_effect_name
                      ct.FStar_Syntax_Syntax.effect_name
              with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    if
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags in
                  let uu___156_18292 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___156_18292.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___156_18292.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___156_18292.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___157_18294 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___157_18294.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___157_18294.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___157_18294.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___157_18294.FStar_Syntax_Syntax.flags)
                  } in
            let uu___158_18295 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___158_18295.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___158_18295.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18297 -> c
let ghost_to_pure_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env in
      let non_info t =
        let uu____18309 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18309 in
      let uu____18316 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18316
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18320  ->
                 let uu____18321 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18321)
        | FStar_Pervasives_Native.None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____18338 =
                let uu____18343 =
                  let uu____18344 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18344 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18343) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18338);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18355 = config [AllowUnboundUniverses] env in
          norm_comp uu____18355 [] c
        with
        | e ->
            ((let uu____18368 =
                let uu____18373 =
                  let uu____18374 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18374 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18373) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18368);
             c) in
      FStar_Syntax_Print.comp_to_string c1
let normalize_refinement:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0 in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1 in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____18411 =
                     let uu____18412 =
                       let uu____18419 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18419) in
                     FStar_Syntax_Syntax.Tm_refine uu____18412 in
                   mk uu____18411 t01.FStar_Syntax_Syntax.pos
               | uu____18424 -> t2)
          | uu____18425 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize
        [Weak; HNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta] env
        t
let reduce_or_remove_uvar_solutions:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
let reduce_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t
let remove_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t
let eta_expand_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____18465 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18465 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18494 ->
                 let uu____18501 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18501 with
                  | (actuals,uu____18511,uu____18512) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18526 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18526 with
                         | (binders,args) ->
                             let uu____18543 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18543
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____18551 ->
          let uu____18552 = FStar_Syntax_Util.head_and_args t in
          (match uu____18552 with
           | (head1,args) ->
               let uu____18589 =
                 let uu____18590 = FStar_Syntax_Subst.compress head1 in
                 uu____18590.FStar_Syntax_Syntax.n in
               (match uu____18589 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18593,thead) ->
                    let uu____18619 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18619 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18661 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___163_18669 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___163_18669.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___163_18669.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___163_18669.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___163_18669.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___163_18669.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___163_18669.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___163_18669.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___163_18669.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___163_18669.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___163_18669.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___163_18669.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___163_18669.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___163_18669.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___163_18669.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___163_18669.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___163_18669.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___163_18669.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___163_18669.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___163_18669.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___163_18669.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___163_18669.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___163_18669.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___163_18669.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___163_18669.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___163_18669.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___163_18669.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___163_18669.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___163_18669.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___163_18669.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___163_18669.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___163_18669.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___163_18669.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18661 with
                            | (uu____18670,ty,uu____18672) ->
                                eta_expand_with_type env t ty))
                | uu____18673 ->
                    let uu____18674 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___164_18682 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___164_18682.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___164_18682.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___164_18682.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___164_18682.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___164_18682.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___164_18682.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___164_18682.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___164_18682.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___164_18682.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___164_18682.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___164_18682.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___164_18682.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___164_18682.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___164_18682.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___164_18682.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___164_18682.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___164_18682.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___164_18682.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___164_18682.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___164_18682.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___164_18682.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___164_18682.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___164_18682.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___164_18682.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___164_18682.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___164_18682.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___164_18682.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___164_18682.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___164_18682.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___164_18682.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___164_18682.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___164_18682.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18674 with
                     | (uu____18683,ty,uu____18685) ->
                         eta_expand_with_type env t ty)))
let rec elim_delayed_subst_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos in
    let t1 = FStar_Syntax_Subst.compress t in
    let elim_bv x =
      let uu___165_18742 = x in
      let uu____18743 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___165_18742.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___165_18742.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____18743
      } in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____18746 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____18771 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____18772 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____18773 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____18774 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____18781 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____18782 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___166_18810 = rc in
          let uu____18811 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term in
          let uu____18818 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___166_18810.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____18811;
            FStar_Syntax_Syntax.residual_flags = uu____18818
          } in
        let uu____18821 =
          let uu____18822 =
            let uu____18839 = elim_delayed_subst_binders bs in
            let uu____18846 = elim_delayed_subst_term t2 in
            let uu____18847 = FStar_Util.map_opt rc_opt elim_rc in
            (uu____18839, uu____18846, uu____18847) in
          FStar_Syntax_Syntax.Tm_abs uu____18822 in
        mk1 uu____18821
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____18876 =
          let uu____18877 =
            let uu____18890 = elim_delayed_subst_binders bs in
            let uu____18897 = elim_delayed_subst_comp c in
            (uu____18890, uu____18897) in
          FStar_Syntax_Syntax.Tm_arrow uu____18877 in
        mk1 uu____18876
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____18910 =
          let uu____18911 =
            let uu____18918 = elim_bv bv in
            let uu____18919 = elim_delayed_subst_term phi in
            (uu____18918, uu____18919) in
          FStar_Syntax_Syntax.Tm_refine uu____18911 in
        mk1 uu____18910
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____18942 =
          let uu____18943 =
            let uu____18958 = elim_delayed_subst_term t2 in
            let uu____18959 = elim_delayed_subst_args args in
            (uu____18958, uu____18959) in
          FStar_Syntax_Syntax.Tm_app uu____18943 in
        mk1 uu____18942
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___167_19023 = p in
              let uu____19024 =
                let uu____19025 = elim_bv x in
                FStar_Syntax_Syntax.Pat_var uu____19025 in
              {
                FStar_Syntax_Syntax.v = uu____19024;
                FStar_Syntax_Syntax.p =
                  (uu___167_19023.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___168_19027 = p in
              let uu____19028 =
                let uu____19029 = elim_bv x in
                FStar_Syntax_Syntax.Pat_wild uu____19029 in
              {
                FStar_Syntax_Syntax.v = uu____19028;
                FStar_Syntax_Syntax.p =
                  (uu___168_19027.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___169_19036 = p in
              let uu____19037 =
                let uu____19038 =
                  let uu____19045 = elim_bv x in
                  let uu____19046 = elim_delayed_subst_term t0 in
                  (uu____19045, uu____19046) in
                FStar_Syntax_Syntax.Pat_dot_term uu____19038 in
              {
                FStar_Syntax_Syntax.v = uu____19037;
                FStar_Syntax_Syntax.p =
                  (uu___169_19036.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___170_19065 = p in
              let uu____19066 =
                let uu____19067 =
                  let uu____19080 =
                    FStar_List.map
                      (fun uu____19103  ->
                         match uu____19103 with
                         | (x,b) ->
                             let uu____19116 = elim_pat x in (uu____19116, b))
                      pats in
                  (fv, uu____19080) in
                FStar_Syntax_Syntax.Pat_cons uu____19067 in
              {
                FStar_Syntax_Syntax.v = uu____19066;
                FStar_Syntax_Syntax.p =
                  (uu___170_19065.FStar_Syntax_Syntax.p)
              }
          | uu____19129 -> p in
        let elim_branch uu____19151 =
          match uu____19151 with
          | (pat,wopt,t3) ->
              let uu____19177 = elim_pat pat in
              let uu____19180 =
                FStar_Util.map_opt wopt elim_delayed_subst_term in
              let uu____19183 = elim_delayed_subst_term t3 in
              (uu____19177, uu____19180, uu____19183) in
        let uu____19188 =
          let uu____19189 =
            let uu____19212 = elim_delayed_subst_term t2 in
            let uu____19213 = FStar_List.map elim_branch branches in
            (uu____19212, uu____19213) in
          FStar_Syntax_Syntax.Tm_match uu____19189 in
        mk1 uu____19188
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____19322 =
          match uu____19322 with
          | (tc,topt) ->
              let uu____19357 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____19367 = elim_delayed_subst_term t3 in
                    FStar_Util.Inl uu____19367
                | FStar_Util.Inr c ->
                    let uu____19369 = elim_delayed_subst_comp c in
                    FStar_Util.Inr uu____19369 in
              let uu____19370 =
                FStar_Util.map_opt topt elim_delayed_subst_term in
              (uu____19357, uu____19370) in
        let uu____19379 =
          let uu____19380 =
            let uu____19407 = elim_delayed_subst_term t2 in
            let uu____19408 = elim_ascription a in
            (uu____19407, uu____19408, lopt) in
          FStar_Syntax_Syntax.Tm_ascribed uu____19380 in
        mk1 uu____19379
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___171_19453 = lb in
          let uu____19454 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp in
          let uu____19457 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___171_19453.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___171_19453.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____19454;
            FStar_Syntax_Syntax.lbeff =
              (uu___171_19453.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____19457
          } in
        let uu____19460 =
          let uu____19461 =
            let uu____19474 =
              let uu____19481 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs) in
              ((FStar_Pervasives_Native.fst lbs), uu____19481) in
            let uu____19490 = elim_delayed_subst_term t2 in
            (uu____19474, uu____19490) in
          FStar_Syntax_Syntax.Tm_let uu____19461 in
        mk1 uu____19460
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____19523 =
          let uu____19524 =
            let uu____19541 = elim_delayed_subst_term t2 in (uv, uu____19541) in
          FStar_Syntax_Syntax.Tm_uvar uu____19524 in
        mk1 uu____19523
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____19558 =
          let uu____19559 =
            let uu____19566 = elim_delayed_subst_term t2 in
            let uu____19567 = elim_delayed_subst_meta md in
            (uu____19566, uu____19567) in
          FStar_Syntax_Syntax.Tm_meta uu____19559 in
        mk1 uu____19558
and elim_delayed_subst_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___90_19574  ->
         match uu___90_19574 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____19578 = elim_delayed_subst_term t in
             FStar_Syntax_Syntax.DECREASES uu____19578
         | f -> f) flags1
and elim_delayed_subst_comp:
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____19599 =
          let uu____19600 =
            let uu____19609 = elim_delayed_subst_term t in
            (uu____19609, uopt) in
          FStar_Syntax_Syntax.Total uu____19600 in
        mk1 uu____19599
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____19622 =
          let uu____19623 =
            let uu____19632 = elim_delayed_subst_term t in
            (uu____19632, uopt) in
          FStar_Syntax_Syntax.GTotal uu____19623 in
        mk1 uu____19622
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___172_19637 = ct in
          let uu____19638 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ in
          let uu____19641 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args in
          let uu____19650 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___172_19637.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___172_19637.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____19638;
            FStar_Syntax_Syntax.effect_args = uu____19641;
            FStar_Syntax_Syntax.flags = uu____19650
          } in
        mk1 (FStar_Syntax_Syntax.Comp ct1)
and elim_delayed_subst_meta:
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata =
  fun uu___91_19653  ->
    match uu___91_19653 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____19665 = FStar_List.map elim_delayed_subst_args args in
        FStar_Syntax_Syntax.Meta_pattern uu____19665
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____19698 =
          let uu____19705 = elim_delayed_subst_term t in (m, uu____19705) in
        FStar_Syntax_Syntax.Meta_monadic uu____19698
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____19713 =
          let uu____19722 = elim_delayed_subst_term t in
          (m1, m2, uu____19722) in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____19713
    | FStar_Syntax_Syntax.Meta_alien (d,s,t) ->
        let uu____19730 =
          let uu____19739 = elim_delayed_subst_term t in (d, s, uu____19739) in
        FStar_Syntax_Syntax.Meta_alien uu____19730
    | m -> m
and elim_delayed_subst_args:
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.map
      (fun uu____19762  ->
         match uu____19762 with
         | (t,q) ->
             let uu____19773 = elim_delayed_subst_term t in (uu____19773, q))
      args
and elim_delayed_subst_binders:
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    FStar_List.map
      (fun uu____19793  ->
         match uu____19793 with
         | (x,q) ->
             let uu____19804 =
               let uu___173_19805 = x in
               let uu____19806 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___173_19805.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___173_19805.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____19806
               } in
             (uu____19804, q)) bs
let elim_uvars_aux_tc:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____19882,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19888,FStar_Util.Inl t) ->
                let uu____19894 =
                  let uu____19897 =
                    let uu____19898 =
                      let uu____19911 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19911) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19898 in
                  FStar_Syntax_Syntax.mk uu____19897 in
                uu____19894 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19915 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19915 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = elim_delayed_subst_term t3 in
              let uu____19943 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____19998 ->
                    let uu____19999 =
                      let uu____20008 =
                        let uu____20009 = FStar_Syntax_Subst.compress t4 in
                        uu____20009.FStar_Syntax_Syntax.n in
                      (uu____20008, tc) in
                    (match uu____19999 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____20034) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____20071) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____20110,FStar_Util.Inl uu____20111) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____20134 -> failwith "Impossible") in
              (match uu____19943 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____20239 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____20239 with
          | (univ_names1,binders1,tc) ->
              let uu____20297 = FStar_Util.left tc in
              (univ_names1, binders1, uu____20297)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____20332 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____20332 with
          | (univ_names1,binders1,tc) ->
              let uu____20392 = FStar_Util.right tc in
              (univ_names1, binders1, uu____20392)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____20425 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____20425 with
           | (univ_names1,binders1,typ1) ->
               let uu___174_20453 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20453.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20453.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20453.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20453.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___175_20474 = s in
          let uu____20475 =
            let uu____20476 =
              let uu____20485 = FStar_List.map (elim_uvars env) sigs in
              (uu____20485, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____20476 in
          {
            FStar_Syntax_Syntax.sigel = uu____20475;
            FStar_Syntax_Syntax.sigrng =
              (uu___175_20474.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___175_20474.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___175_20474.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___175_20474.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____20502 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20502 with
           | (univ_names1,uu____20520,typ1) ->
               let uu___176_20534 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___176_20534.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___176_20534.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___176_20534.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___176_20534.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____20540 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____20540 with
           | (univ_names1,uu____20558,typ1) ->
               let uu___177_20572 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___177_20572.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___177_20572.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___177_20572.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___177_20572.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____20606 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____20606 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____20629 =
                            let uu____20630 =
                              let uu____20631 =
                                FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env uu____20631 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____20630 in
                          elim_delayed_subst_term uu____20629 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___178_20634 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___178_20634.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___178_20634.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___179_20635 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___179_20635.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___179_20635.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___179_20635.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___179_20635.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___180_20647 = s in
          let uu____20648 =
            let uu____20649 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____20649 in
          {
            FStar_Syntax_Syntax.sigel = uu____20648;
            FStar_Syntax_Syntax.sigrng =
              (uu___180_20647.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___180_20647.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___180_20647.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___180_20647.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____20653 = elim_uvars_aux_t env us [] t in
          (match uu____20653 with
           | (us1,uu____20671,t1) ->
               let uu___181_20685 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___181_20685.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___181_20685.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___181_20685.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___181_20685.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20686 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20688 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____20688 with
           | (univs1,binders,signature) ->
               let uu____20716 =
                 let uu____20725 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____20725 with
                 | (univs_opening,univs2) ->
                     let uu____20752 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____20752) in
               (match uu____20716 with
                | (univs_opening,univs_closing) ->
                    let uu____20769 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____20775 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____20776 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____20775, uu____20776) in
                    (match uu____20769 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____20798 =
                           match uu____20798 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____20816 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____20816 with
                                | (us1,t1) ->
                                    let uu____20827 =
                                      let uu____20832 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20839 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20832, uu____20839) in
                                    (match uu____20827 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20852 =
                                           let uu____20857 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20866 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20857, uu____20866) in
                                         (match uu____20852 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20882 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20882 in
                                              let uu____20883 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20883 with
                                               | (uu____20904,uu____20905,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20920 =
                                                       let uu____20921 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20921 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20920 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20926 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20926 with
                           | (uu____20939,uu____20940,t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____21000 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____21017 =
                               let uu____21018 =
                                 FStar_Syntax_Subst.compress body in
                               uu____21018.FStar_Syntax_Syntax.n in
                             match uu____21017 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____21077 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____21106 =
                               let uu____21107 =
                                 FStar_Syntax_Subst.compress t in
                               uu____21107.FStar_Syntax_Syntax.n in
                             match uu____21106 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____21128) ->
                                 let uu____21149 = destruct_action_body body in
                                 (match uu____21149 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____21194 ->
                                 let uu____21195 = destruct_action_body t in
                                 (match uu____21195 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____21244 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____21244 with
                           | (action_univs,t) ->
                               let uu____21253 = destruct_action_typ_templ t in
                               (match uu____21253 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___182_21294 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___182_21294.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___182_21294.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      } in
                                    a') in
                         let ed1 =
                           let uu___183_21296 = ed in
                           let uu____21297 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____21298 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____21299 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____21300 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____21301 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____21302 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____21303 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____21304 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____21305 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____21306 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____21307 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____21308 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____21309 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____21310 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___183_21296.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___183_21296.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____21297;
                             FStar_Syntax_Syntax.bind_wp = uu____21298;
                             FStar_Syntax_Syntax.if_then_else = uu____21299;
                             FStar_Syntax_Syntax.ite_wp = uu____21300;
                             FStar_Syntax_Syntax.stronger = uu____21301;
                             FStar_Syntax_Syntax.close_wp = uu____21302;
                             FStar_Syntax_Syntax.assert_p = uu____21303;
                             FStar_Syntax_Syntax.assume_p = uu____21304;
                             FStar_Syntax_Syntax.null_wp = uu____21305;
                             FStar_Syntax_Syntax.trivial = uu____21306;
                             FStar_Syntax_Syntax.repr = uu____21307;
                             FStar_Syntax_Syntax.return_repr = uu____21308;
                             FStar_Syntax_Syntax.bind_repr = uu____21309;
                             FStar_Syntax_Syntax.actions = uu____21310
                           } in
                         let uu___184_21313 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___184_21313.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___184_21313.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___184_21313.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___184_21313.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___92_21330 =
            match uu___92_21330 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____21357 = elim_uvars_aux_t env us [] t in
                (match uu____21357 with
                 | (us1,uu____21381,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___185_21400 = sub_eff in
            let uu____21401 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____21404 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___185_21400.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___185_21400.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____21401;
              FStar_Syntax_Syntax.lift = uu____21404
            } in
          let uu___186_21407 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___186_21407.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___186_21407.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___186_21407.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___186_21407.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____21417 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____21417 with
           | (univ_names1,binders1,comp1) ->
               let uu___187_21451 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___187_21451.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___187_21451.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___187_21451.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___187_21451.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____21462 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t