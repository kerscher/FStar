open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for () in
      match uu____7 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____12 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____12 l in
          let uu___60_13 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___60_13.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___60_13.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___60_13.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___60_13.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___60_13.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___60_13.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___60_13.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___60_13.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___60_13.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___60_13.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___60_13.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___60_13.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___60_13.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___60_13.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___60_13.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___60_13.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___60_13.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___60_13.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___60_13.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___60_13.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___60_13.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___60_13.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___60_13.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___60_13.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___60_13.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___60_13.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___60_13.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___60_13.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___60_13.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___60_13.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___60_13.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___60_13.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___60_13.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___60_13.FStar_TypeChecker_Env.dep_graph)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____22 = FStar_TypeChecker_Env.current_module env in
                let uu____23 =
                  let uu____24 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right uu____24 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____22 uu____23
            | l::uu____26 -> l in
          let uu___61_29 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___61_29.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___61_29.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___61_29.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___61_29.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___61_29.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___61_29.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___61_29.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___61_29.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___61_29.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___61_29.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___61_29.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___61_29.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___61_29.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___61_29.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___61_29.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___61_29.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___61_29.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___61_29.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___61_29.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___61_29.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.failhard =
              (uu___61_29.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___61_29.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___61_29.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___61_29.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___61_29.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___61_29.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___61_29.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (FStar_Pervasives_Native.Some (lid, (Prims.parse_int "0")));
            FStar_TypeChecker_Env.proof_ns =
              (uu___61_29.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___61_29.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___61_29.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___61_29.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___61_29.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___61_29.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___61_29.FStar_TypeChecker_Env.dep_graph)
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____38 =
         let uu____39 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____39 in
       Prims.op_Negation uu____38)
let get_tactic_fv:
  'Auu____44 .
    'Auu____44 ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tac_lid  ->
      fun h  ->
        match h.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uinst (h',uu____60) ->
            let uu____65 =
              let uu____66 = FStar_Syntax_Subst.compress h' in
              uu____66.FStar_Syntax_Syntax.n in
            (match uu____65 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.tactic_lid
                 -> FStar_Pervasives_Native.Some fv
             | uu____72 -> FStar_Pervasives_Native.None)
        | uu____73 -> FStar_Pervasives_Native.None
let is_builtin_tactic: FStar_Ident.lident -> Prims.bool =
  fun md  ->
    let path = FStar_Ident.path_of_lid md in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____80 =
        let uu____83 = FStar_List.splitAt (Prims.parse_int "2") path in
        FStar_Pervasives_Native.fst uu____83 in
      match uu____80 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____96 -> false
    else false
let user_tactics_modules: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let reified_tactic_type:
  FStar_Ident.lident -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun l  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____157 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____157 with
           | (bs1,c1) ->
               let uu____164 = FStar_Syntax_Util.is_total_comp c1 in
               if uu____164
               then
                 let c' =
                   match c1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Total (t',u) ->
                       let uu____176 =
                         let uu____177 = FStar_Syntax_Subst.compress t' in
                         uu____177.FStar_Syntax_Syntax.n in
                       (match uu____176 with
                        | FStar_Syntax_Syntax.Tm_app (h,args) ->
                            let uu____202 =
                              let uu____203 = FStar_Syntax_Subst.compress h in
                              uu____203.FStar_Syntax_Syntax.n in
                            (match uu____202 with
                             | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
                                 let h'' =
                                   let uu____213 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.u_tac_lid
                                       FStar_Syntax_Syntax.Delta_constant
                                       FStar_Pervasives_Native.None in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Syntax.fv_to_tm uu____213 in
                                 let uu____214 =
                                   let uu____215 =
                                     let uu____216 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____216
                                       args in
                                   uu____215 FStar_Pervasives_Native.None
                                     t'.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk_Total' uu____214 u
                             | uu____219 -> c1)
                        | uu____220 -> c1)
                   | uu____221 -> c1 in
                 let uu___62_222 = t1 in
                 let uu____223 =
                   let uu____224 =
                     let uu____237 = FStar_Syntax_Subst.close_comp bs1 c' in
                     (bs1, uu____237) in
                   FStar_Syntax_Syntax.Tm_arrow uu____224 in
                 {
                   FStar_Syntax_Syntax.n = uu____223;
                   FStar_Syntax_Syntax.pos =
                     (uu___62_222.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___62_222.FStar_Syntax_Syntax.vars)
                 }
               else t1)
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____261 =
            let uu____262 = FStar_Syntax_Subst.compress h in
            uu____262.FStar_Syntax_Syntax.n in
          (match uu____261 with
           | FStar_Syntax_Syntax.Tm_uinst (h',u') ->
               let h'' =
                 let uu____272 =
                   FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.u_tac_lid
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm uu____272 in
               let uu____273 =
                 let uu____274 = FStar_Syntax_Syntax.mk_Tm_uinst h'' u' in
                 FStar_Syntax_Syntax.mk_Tm_app uu____274 args in
               uu____273 FStar_Pervasives_Native.None
                 t1.FStar_Syntax_Syntax.pos
           | uu____277 -> t1)
      | uu____278 -> t1
let reified_tactic_decl:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.letbinding -> FStar_Syntax_Syntax.sigelt
  =
  fun assm_lid  ->
    fun lb  ->
      let t = reified_tactic_type assm_lid lb.FStar_Syntax_Syntax.lbtyp in
      {
        FStar_Syntax_Syntax.sigel =
          (FStar_Syntax_Syntax.Sig_declare_typ
             (assm_lid, (lb.FStar_Syntax_Syntax.lbunivs), t));
        FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid assm_lid);
        FStar_Syntax_Syntax.sigquals = [FStar_Syntax_Syntax.Assumption];
        FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
        FStar_Syntax_Syntax.sigattrs = []
      }
let reflected_tactic_decl:
  FStar_Syntax_Syntax.sigelt ->
    Prims.bool ->
      FStar_Ident.lident Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          FStar_Syntax_Syntax.binders ->
            FStar_Ident.lident ->
              FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.sigelt
  =
  fun se  ->
    fun b  ->
      fun lids  ->
        fun lb  ->
          fun bs  ->
            fun assm_lid  ->
              fun comp  ->
                let reified_tac =
                  let uu____314 =
                    FStar_Syntax_Syntax.lid_as_fv assm_lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm uu____314 in
                let tac_args =
                  FStar_List.map
                    (fun x  ->
                       let uu____331 =
                         FStar_Syntax_Syntax.bv_to_name
                           (FStar_Pervasives_Native.fst x) in
                       (uu____331, (FStar_Pervasives_Native.snd x))) bs in
                let reflect_head =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_reflect
                          FStar_Parser_Const.tac_effect_lid))
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                let refl_arg =
                  FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                let app =
                  FStar_Syntax_Syntax.mk_Tm_app reflect_head
                    [(refl_arg, FStar_Pervasives_Native.None)]
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                let unit_binder =
                  let uu____362 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      FStar_Syntax_Syntax.t_unit in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____362 in
                let body =
                  FStar_All.pipe_left
                    (FStar_Syntax_Util.abs [unit_binder] app)
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                let func =
                  FStar_All.pipe_left (FStar_Syntax_Util.abs bs body)
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_comp_of_comp comp)) in
                let uu___63_369 = se in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_let
                       ((b,
                          [(let uu___64_381 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___64_381.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___64_381.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___64_381.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___64_381.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = func
                            })]), lids));
                  FStar_Syntax_Syntax.sigrng =
                    (uu___63_369.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___63_369.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___63_369.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___63_369.FStar_Syntax_Syntax.sigattrs)
                }
let tactic_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.letbindings ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun se  ->
      fun lbs  ->
        fun lids  ->
          match FStar_Pervasives_Native.snd lbs with
          | hd1::[] ->
              let uu____413 =
                FStar_Syntax_Util.arrow_formals_comp
                  hd1.FStar_Syntax_Syntax.lbtyp in
              (match uu____413 with
               | (bs,comp) ->
                   let t = FStar_Syntax_Util.comp_result comp in
                   let uu____447 =
                     let uu____448 = FStar_Syntax_Subst.compress t in
                     uu____448.FStar_Syntax_Syntax.n in
                   (match uu____447 with
                    | FStar_Syntax_Syntax.Tm_app (h,args) ->
                        let h1 = FStar_Syntax_Subst.compress h in
                        let tac_lid =
                          let uu____481 =
                            let uu____484 =
                              FStar_Util.right hd1.FStar_Syntax_Syntax.lbname in
                            uu____484.FStar_Syntax_Syntax.fv_name in
                          uu____481.FStar_Syntax_Syntax.v in
                        let assm_lid =
                          let uu____486 =
                            FStar_All.pipe_left FStar_Ident.id_of_text
                              (Prims.strcat "__"
                                 (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                          FStar_Ident.lid_of_ns_and_id tac_lid.FStar_Ident.ns
                            uu____486 in
                        let uu____487 = get_tactic_fv env assm_lid h1 in
                        (match uu____487 with
                         | FStar_Pervasives_Native.Some fv ->
                             let uu____497 =
                               let uu____498 =
                                 let uu____499 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env tac_lid in
                                 FStar_All.pipe_left FStar_Util.is_some
                                   uu____499 in
                               Prims.op_Negation uu____498 in
                             if uu____497
                             then
                               ((let uu____529 =
                                   let uu____530 =
                                     is_builtin_tactic
                                       env.FStar_TypeChecker_Env.curmodule in
                                   Prims.op_Negation uu____530 in
                                 if uu____529
                                 then
                                   let added_modules =
                                     FStar_ST.op_Bang user_tactics_modules in
                                   let module_name =
                                     FStar_Ident.ml_path_of_lid
                                       env.FStar_TypeChecker_Env.curmodule in
                                   (if
                                      Prims.op_Negation
                                        (FStar_List.contains module_name
                                           added_modules)
                                    then
                                      FStar_ST.op_Colon_Equals
                                        user_tactics_modules
                                        (FStar_List.append added_modules
                                           [module_name])
                                    else ())
                                 else ());
                                (let uu____583 =
                                   env.FStar_TypeChecker_Env.is_native_tactic
                                     assm_lid in
                                 if uu____583
                                 then
                                   let se_assm =
                                     reified_tactic_decl assm_lid hd1 in
                                   let se_refl =
                                     reflected_tactic_decl se
                                       (FStar_Pervasives_Native.fst lbs) lids
                                       hd1 bs assm_lid comp in
                                   FStar_Pervasives_Native.Some
                                     (se_assm, se_refl)
                                 else FStar_Pervasives_Native.None))
                             else FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None)
                    | uu____612 -> FStar_Pervasives_Native.None))
          | uu____617 -> FStar_Pervasives_Native.None
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____633 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____633 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____654 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____654
         then
           let uu____655 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____655
         else ());
        (let uu____657 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____657 with
         | (t',uu____665,uu____666) ->
             ((let uu____668 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____668
               then
                 let uu____669 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____669
               else ());
              t))
let check_and_gen:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____680 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env uu____680
let check_nogen:
  'Auu____685 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____685 Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k in
        let uu____705 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta] env t1 in
        ([], uu____705)
let monad_signature:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____732 =
          let uu____733 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          FStar_Errors.raise_error uu____733 (FStar_Ident.range_of_lid m) in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a,uu____777)::(wp,uu____779)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____794 -> fail ())
        | uu____795 -> fail ()
let tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____802 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
      match uu____802 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____828 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst uu____828 t in
          let open_univs_binders n_binders bs =
            let uu____838 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs in
            FStar_Syntax_Subst.subst_binders uu____838 bs in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders in
          let uu____846 =
            let uu____853 =
              open_univs_binders (Prims.parse_int "0")
                ed.FStar_Syntax_Syntax.binders in
            let uu____854 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature in
            FStar_Syntax_Subst.open_term' uu____853 uu____854 in
          (match uu____846 with
           | (effect_params_un,signature_un,opening) ->
               let uu____864 =
                 FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
               (match uu____864 with
                | (effect_params,env,uu____873) ->
                    let uu____874 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env
                        signature_un in
                    (match uu____874 with
                     | (signature,uu____880) ->
                         let ed1 =
                           let uu___65_882 = ed in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___65_882.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___65_882.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___65_882.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___65_882.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___65_882.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.if_then_else =
                               (uu___65_882.FStar_Syntax_Syntax.if_then_else);
                             FStar_Syntax_Syntax.ite_wp =
                               (uu___65_882.FStar_Syntax_Syntax.ite_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___65_882.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.close_wp =
                               (uu___65_882.FStar_Syntax_Syntax.close_wp);
                             FStar_Syntax_Syntax.assert_p =
                               (uu___65_882.FStar_Syntax_Syntax.assert_p);
                             FStar_Syntax_Syntax.assume_p =
                               (uu___65_882.FStar_Syntax_Syntax.assume_p);
                             FStar_Syntax_Syntax.null_wp =
                               (uu___65_882.FStar_Syntax_Syntax.null_wp);
                             FStar_Syntax_Syntax.trivial =
                               (uu___65_882.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___65_882.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___65_882.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___65_882.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___65_882.FStar_Syntax_Syntax.actions)
                           } in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____898 ->
                               let op uu____920 =
                                 match uu____920 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us in
                                     let uu____940 =
                                       let uu____941 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening in
                                       let uu____950 =
                                         open_univs (n_effect_params + n_us)
                                           t in
                                       FStar_Syntax_Subst.subst uu____941
                                         uu____950 in
                                     (us, uu____940) in
                               let uu___66_963 = ed1 in
                               let uu____964 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp in
                               let uu____965 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp in
                               let uu____966 =
                                 op ed1.FStar_Syntax_Syntax.if_then_else in
                               let uu____967 =
                                 op ed1.FStar_Syntax_Syntax.ite_wp in
                               let uu____968 =
                                 op ed1.FStar_Syntax_Syntax.stronger in
                               let uu____969 =
                                 op ed1.FStar_Syntax_Syntax.close_wp in
                               let uu____970 =
                                 op ed1.FStar_Syntax_Syntax.assert_p in
                               let uu____971 =
                                 op ed1.FStar_Syntax_Syntax.assume_p in
                               let uu____972 =
                                 op ed1.FStar_Syntax_Syntax.null_wp in
                               let uu____973 =
                                 op ed1.FStar_Syntax_Syntax.trivial in
                               let uu____974 =
                                 let uu____975 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr)) in
                                 FStar_Pervasives_Native.snd uu____975 in
                               let uu____986 =
                                 op ed1.FStar_Syntax_Syntax.return_repr in
                               let uu____987 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr in
                               let uu____988 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___67_996 = a in
                                      let uu____997 =
                                        let uu____998 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_defn)) in
                                        FStar_Pervasives_Native.snd uu____998 in
                                      let uu____1009 =
                                        let uu____1010 =
                                          op
                                            ([],
                                              (a.FStar_Syntax_Syntax.action_typ)) in
                                        FStar_Pervasives_Native.snd
                                          uu____1010 in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___67_996.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___67_996.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___67_996.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___67_996.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____997;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____1009
                                      }) ed1.FStar_Syntax_Syntax.actions in
                               {
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___66_963.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___66_963.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___66_963.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___66_963.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____964;
                                 FStar_Syntax_Syntax.bind_wp = uu____965;
                                 FStar_Syntax_Syntax.if_then_else = uu____966;
                                 FStar_Syntax_Syntax.ite_wp = uu____967;
                                 FStar_Syntax_Syntax.stronger = uu____968;
                                 FStar_Syntax_Syntax.close_wp = uu____969;
                                 FStar_Syntax_Syntax.assert_p = uu____970;
                                 FStar_Syntax_Syntax.assume_p = uu____971;
                                 FStar_Syntax_Syntax.null_wp = uu____972;
                                 FStar_Syntax_Syntax.trivial = uu____973;
                                 FStar_Syntax_Syntax.repr = uu____974;
                                 FStar_Syntax_Syntax.return_repr = uu____986;
                                 FStar_Syntax_Syntax.bind_repr = uu____987;
                                 FStar_Syntax_Syntax.actions = uu____988
                               } in
                         let wp_with_fresh_result_type env1 mname signature1
                           =
                           let fail t =
                             let uu____1047 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env1 mname t in
                             FStar_Errors.raise_error uu____1047
                               (FStar_Ident.range_of_lid mname) in
                           let uu____1058 =
                             let uu____1059 =
                               FStar_Syntax_Subst.compress signature1 in
                             uu____1059.FStar_Syntax_Syntax.n in
                           match uu____1058 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs in
                               (match bs1 with
                                | (a,uu____1094)::(wp,uu____1096)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____1111 -> fail signature1)
                           | uu____1112 -> fail signature1 in
                         let uu____1113 =
                           wp_with_fresh_result_type env
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature in
                         (match uu____1113 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____1135 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____1142 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env signature_un in
                                    (match uu____1142 with
                                     | (signature1,uu____1154) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____1155 ->
                                    let uu____1158 =
                                      let uu____1163 =
                                        let uu____1164 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature in
                                        (annotated_univ_names, uu____1164) in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____1163 in
                                    (match uu____1158 with
                                     | (uu____1173,signature1) ->
                                         wp_with_fresh_result_type env
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1) in
                              let env1 =
                                let uu____1176 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature in
                                FStar_TypeChecker_Env.push_bv env uu____1176 in
                              ((let uu____1178 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED") in
                                if uu____1178
                                then
                                  let uu____1179 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname in
                                  let uu____1180 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders in
                                  let uu____1181 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature in
                                  let uu____1182 =
                                    let uu____1183 =
                                      FStar_Syntax_Syntax.bv_to_name a in
                                    FStar_Syntax_Print.term_to_string
                                      uu____1183 in
                                  let uu____1184 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____1179 uu____1180 uu____1181
                                    uu____1182 uu____1184
                                else ());
                               (let check_and_gen' env2 uu____1200 k =
                                  match uu____1200 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env2 t k
                                       | uu____1214::uu____1215 ->
                                           let uu____1218 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t) in
                                           (match uu____1218 with
                                            | (us1,t1) ->
                                                let uu____1227 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1 in
                                                (match uu____1227 with
                                                 | (us2,t2) ->
                                                     let uu____1234 =
                                                       tc_check_trivial_guard
                                                         env2 t2 k in
                                                     let uu____1235 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2 in
                                                     (us2, uu____1235)))) in
                                let return_wp =
                                  let expected_k =
                                    let uu____1240 =
                                      let uu____1247 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1248 =
                                        let uu____1251 =
                                          let uu____1252 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1252 in
                                        [uu____1251] in
                                      uu____1247 :: uu____1248 in
                                    let uu____1253 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a in
                                    FStar_Syntax_Util.arrow uu____1240
                                      uu____1253 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k in
                                let bind_wp =
                                  let uu____1257 = fresh_effect_signature () in
                                  match uu____1257 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____1273 =
                                          let uu____1280 =
                                            let uu____1281 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____1281 in
                                          [uu____1280] in
                                        let uu____1282 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____1273
                                          uu____1282 in
                                      let expected_k =
                                        let uu____1288 =
                                          let uu____1295 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____1296 =
                                            let uu____1299 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____1300 =
                                              let uu____1303 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____1304 =
                                                let uu____1307 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a in
                                                let uu____1308 =
                                                  let uu____1311 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b in
                                                  [uu____1311] in
                                                uu____1307 :: uu____1308 in
                                              uu____1303 :: uu____1304 in
                                            uu____1299 :: uu____1300 in
                                          uu____1295 :: uu____1296 in
                                        let uu____1312 =
                                          FStar_Syntax_Syntax.mk_Total wp_b in
                                        FStar_Syntax_Util.arrow uu____1288
                                          uu____1312 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k in
                                let if_then_else1 =
                                  let p =
                                    let uu____1317 =
                                      let uu____1318 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____1318
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____1317 in
                                  let expected_k =
                                    let uu____1330 =
                                      let uu____1337 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1338 =
                                        let uu____1341 =
                                          FStar_Syntax_Syntax.mk_binder p in
                                        let uu____1342 =
                                          let uu____1345 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          let uu____1346 =
                                            let uu____1349 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____1349] in
                                          uu____1345 :: uu____1346 in
                                        uu____1341 :: uu____1342 in
                                      uu____1337 :: uu____1338 in
                                    let uu____1350 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1330
                                      uu____1350 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.if_then_else
                                    expected_k in
                                let ite_wp =
                                  let expected_k =
                                    let uu____1357 =
                                      let uu____1364 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1365 =
                                        let uu____1368 =
                                          FStar_Syntax_Syntax.null_binder
                                            wp_a in
                                        [uu____1368] in
                                      uu____1364 :: uu____1365 in
                                    let uu____1369 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1357
                                      uu____1369 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.ite_wp expected_k in
                                let stronger =
                                  let uu____1373 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____1373 with
                                  | (t,uu____1379) ->
                                      let expected_k =
                                        let uu____1383 =
                                          let uu____1390 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____1391 =
                                            let uu____1394 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            let uu____1395 =
                                              let uu____1398 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a in
                                              [uu____1398] in
                                            uu____1394 :: uu____1395 in
                                          uu____1390 :: uu____1391 in
                                        let uu____1399 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Util.arrow uu____1383
                                          uu____1399 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.stronger
                                        expected_k in
                                let close_wp =
                                  let b =
                                    let uu____1404 =
                                      let uu____1405 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_right uu____1405
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Syntax.new_bv
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Ident.range_of_lid
                                            ed2.FStar_Syntax_Syntax.mname))
                                      uu____1404 in
                                  let b_wp_a =
                                    let uu____1417 =
                                      let uu____1424 =
                                        let uu____1425 =
                                          FStar_Syntax_Syntax.bv_to_name b in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____1425 in
                                      [uu____1424] in
                                    let uu____1426 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1417
                                      uu____1426 in
                                  let expected_k =
                                    let uu____1432 =
                                      let uu____1439 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1440 =
                                        let uu____1443 =
                                          FStar_Syntax_Syntax.mk_binder b in
                                        let uu____1444 =
                                          let uu____1447 =
                                            FStar_Syntax_Syntax.null_binder
                                              b_wp_a in
                                          [uu____1447] in
                                        uu____1443 :: uu____1444 in
                                      uu____1439 :: uu____1440 in
                                    let uu____1448 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1432
                                      uu____1448 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.close_wp
                                    expected_k in
                                let assert_p =
                                  let expected_k =
                                    let uu____1455 =
                                      let uu____1462 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1463 =
                                        let uu____1466 =
                                          let uu____1467 =
                                            let uu____1468 =
                                              FStar_Syntax_Util.type_u () in
                                            FStar_All.pipe_right uu____1468
                                              FStar_Pervasives_Native.fst in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1467 in
                                        let uu____1477 =
                                          let uu____1480 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____1480] in
                                        uu____1466 :: uu____1477 in
                                      uu____1462 :: uu____1463 in
                                    let uu____1481 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1455
                                      uu____1481 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assert_p
                                    expected_k in
                                let assume_p =
                                  let expected_k =
                                    let uu____1488 =
                                      let uu____1495 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____1496 =
                                        let uu____1499 =
                                          let uu____1500 =
                                            let uu____1501 =
                                              FStar_Syntax_Util.type_u () in
                                            FStar_All.pipe_right uu____1501
                                              FStar_Pervasives_Native.fst in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____1500 in
                                        let uu____1510 =
                                          let uu____1513 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_a in
                                          [uu____1513] in
                                        uu____1499 :: uu____1510 in
                                      uu____1495 :: uu____1496 in
                                    let uu____1514 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1488
                                      uu____1514 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.assume_p
                                    expected_k in
                                let null_wp =
                                  let expected_k =
                                    let uu____1521 =
                                      let uu____1528 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      [uu____1528] in
                                    let uu____1529 =
                                      FStar_Syntax_Syntax.mk_Total wp_a in
                                    FStar_Syntax_Util.arrow uu____1521
                                      uu____1529 in
                                  check_and_gen' env1
                                    ed2.FStar_Syntax_Syntax.null_wp
                                    expected_k in
                                let trivial_wp =
                                  let uu____1533 =
                                    FStar_Syntax_Util.type_u () in
                                  match uu____1533 with
                                  | (t,uu____1539) ->
                                      let expected_k =
                                        let uu____1543 =
                                          let uu____1550 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____1551 =
                                            let uu____1554 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a in
                                            [uu____1554] in
                                          uu____1550 :: uu____1551 in
                                        let uu____1555 =
                                          FStar_Syntax_Syntax.mk_GTotal t in
                                        FStar_Syntax_Util.arrow uu____1543
                                          uu____1555 in
                                      check_and_gen' env1
                                        ed2.FStar_Syntax_Syntax.trivial
                                        expected_k in
                                let uu____1558 =
                                  let uu____1569 =
                                    let uu____1570 =
                                      FStar_Syntax_Subst.compress
                                        ed2.FStar_Syntax_Syntax.repr in
                                    uu____1570.FStar_Syntax_Syntax.n in
                                  match uu____1569 with
                                  | FStar_Syntax_Syntax.Tm_unknown  ->
                                      ((ed2.FStar_Syntax_Syntax.repr),
                                        (ed2.FStar_Syntax_Syntax.bind_repr),
                                        (ed2.FStar_Syntax_Syntax.return_repr),
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____1585 ->
                                      let repr =
                                        let uu____1587 =
                                          FStar_Syntax_Util.type_u () in
                                        match uu____1587 with
                                        | (t,uu____1593) ->
                                            let expected_k =
                                              let uu____1597 =
                                                let uu____1604 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1605 =
                                                  let uu____1608 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a in
                                                  [uu____1608] in
                                                uu____1604 :: uu____1605 in
                                              let uu____1609 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t in
                                              FStar_Syntax_Util.arrow
                                                uu____1597 uu____1609 in
                                            tc_check_trivial_guard env1
                                              ed2.FStar_Syntax_Syntax.repr
                                              expected_k in
                                      let mk_repr' t wp =
                                        let repr1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.EraseUniverses;
                                            FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                            env1 repr in
                                        let uu____1622 =
                                          let uu____1625 =
                                            let uu____1626 =
                                              let uu____1641 =
                                                let uu____1644 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t in
                                                let uu____1645 =
                                                  let uu____1648 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      wp in
                                                  [uu____1648] in
                                                uu____1644 :: uu____1645 in
                                              (repr1, uu____1641) in
                                            FStar_Syntax_Syntax.Tm_app
                                              uu____1626 in
                                          FStar_Syntax_Syntax.mk uu____1625 in
                                        uu____1622
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange in
                                      let mk_repr a1 wp =
                                        let uu____1663 =
                                          FStar_Syntax_Syntax.bv_to_name a1 in
                                        mk_repr' uu____1663 wp in
                                      let destruct_repr t =
                                        let uu____1676 =
                                          let uu____1677 =
                                            FStar_Syntax_Subst.compress t in
                                          uu____1677.FStar_Syntax_Syntax.n in
                                        match uu____1676 with
                                        | FStar_Syntax_Syntax.Tm_app
                                            (uu____1688,(t1,uu____1690)::
                                             (wp,uu____1692)::[])
                                            -> (t1, wp)
                                        | uu____1735 ->
                                            failwith "Unexpected repr type" in
                                      let bind_repr =
                                        let r =
                                          let uu____1746 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.Delta_constant
                                              FStar_Pervasives_Native.None in
                                          FStar_All.pipe_right uu____1746
                                            FStar_Syntax_Syntax.fv_to_tm in
                                        let uu____1747 =
                                          fresh_effect_signature () in
                                        match uu____1747 with
                                        | (b,wp_b) ->
                                            let a_wp_b =
                                              let uu____1763 =
                                                let uu____1770 =
                                                  let uu____1771 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1771 in
                                                [uu____1770] in
                                              let uu____1772 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_b in
                                              FStar_Syntax_Util.arrow
                                                uu____1763 uu____1772 in
                                            let wp_f =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_f"
                                                FStar_Pervasives_Native.None
                                                wp_a in
                                            let wp_g =
                                              FStar_Syntax_Syntax.gen_bv
                                                "wp_g"
                                                FStar_Pervasives_Native.None
                                                a_wp_b in
                                            let x_a =
                                              let uu____1778 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____1778 in
                                            let wp_g_x =
                                              let uu____1782 =
                                                let uu____1783 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    wp_g in
                                                let uu____1784 =
                                                  let uu____1785 =
                                                    let uu____1786 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1786 in
                                                  [uu____1785] in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____1783 uu____1784 in
                                              uu____1782
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange in
                                            let res =
                                              let wp =
                                                let uu____1795 =
                                                  let uu____1796 =
                                                    let uu____1797 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        bind_wp in
                                                    FStar_All.pipe_right
                                                      uu____1797
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____1806 =
                                                    let uu____1807 =
                                                      let uu____1810 =
                                                        let uu____1813 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        let uu____1814 =
                                                          let uu____1817 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              b in
                                                          let uu____1818 =
                                                            let uu____1821 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f in
                                                            let uu____1822 =
                                                              let uu____1825
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_g in
                                                              [uu____1825] in
                                                            uu____1821 ::
                                                              uu____1822 in
                                                          uu____1817 ::
                                                            uu____1818 in
                                                        uu____1813 ::
                                                          uu____1814 in
                                                      r :: uu____1810 in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____1807 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____1796 uu____1806 in
                                                uu____1795
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange in
                                              mk_repr b wp in
                                            let expected_k =
                                              let uu____1831 =
                                                let uu____1838 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a in
                                                let uu____1839 =
                                                  let uu____1842 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b in
                                                  let uu____1843 =
                                                    let uu____1846 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp_f in
                                                    let uu____1847 =
                                                      let uu____1850 =
                                                        let uu____1851 =
                                                          let uu____1852 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp_f in
                                                          mk_repr a
                                                            uu____1852 in
                                                        FStar_Syntax_Syntax.null_binder
                                                          uu____1851 in
                                                      let uu____1853 =
                                                        let uu____1856 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_g in
                                                        let uu____1857 =
                                                          let uu____1860 =
                                                            let uu____1861 =
                                                              let uu____1862
                                                                =
                                                                let uu____1869
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                [uu____1869] in
                                                              let uu____1870
                                                                =
                                                                let uu____1873
                                                                  =
                                                                  mk_repr b
                                                                    wp_g_x in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                  uu____1873 in
                                                              FStar_Syntax_Util.arrow
                                                                uu____1862
                                                                uu____1870 in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____1861 in
                                                          [uu____1860] in
                                                        uu____1856 ::
                                                          uu____1857 in
                                                      uu____1850 ::
                                                        uu____1853 in
                                                    uu____1846 :: uu____1847 in
                                                  uu____1842 :: uu____1843 in
                                                uu____1838 :: uu____1839 in
                                              let uu____1874 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res in
                                              FStar_Syntax_Util.arrow
                                                uu____1831 uu____1874 in
                                            let uu____1877 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env1 expected_k in
                                            (match uu____1877 with
                                             | (expected_k1,uu____1885,uu____1886)
                                                 ->
                                                 let env2 =
                                                   FStar_TypeChecker_Env.set_range
                                                     env1
                                                     (FStar_Pervasives_Native.snd
                                                        ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                                 let env3 =
                                                   let uu___68_1891 = env2 in
                                                   {
                                                     FStar_TypeChecker_Env.solver
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.solver);
                                                     FStar_TypeChecker_Env.range
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.range);
                                                     FStar_TypeChecker_Env.curmodule
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.curmodule);
                                                     FStar_TypeChecker_Env.gamma
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.gamma);
                                                     FStar_TypeChecker_Env.gamma_cache
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.gamma_cache);
                                                     FStar_TypeChecker_Env.modules
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.modules);
                                                     FStar_TypeChecker_Env.expected_typ
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.expected_typ);
                                                     FStar_TypeChecker_Env.sigtab
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.sigtab);
                                                     FStar_TypeChecker_Env.is_pattern
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.is_pattern);
                                                     FStar_TypeChecker_Env.instantiate_imp
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.instantiate_imp);
                                                     FStar_TypeChecker_Env.effects
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.effects);
                                                     FStar_TypeChecker_Env.generalize
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.generalize);
                                                     FStar_TypeChecker_Env.letrecs
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.letrecs);
                                                     FStar_TypeChecker_Env.top_level
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.top_level);
                                                     FStar_TypeChecker_Env.check_uvars
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.check_uvars);
                                                     FStar_TypeChecker_Env.use_eq
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.use_eq);
                                                     FStar_TypeChecker_Env.is_iface
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.is_iface);
                                                     FStar_TypeChecker_Env.admit
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.admit);
                                                     FStar_TypeChecker_Env.lax
                                                       = true;
                                                     FStar_TypeChecker_Env.lax_universes
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.lax_universes);
                                                     FStar_TypeChecker_Env.failhard
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.failhard);
                                                     FStar_TypeChecker_Env.nosynth
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.nosynth);
                                                     FStar_TypeChecker_Env.tc_term
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.tc_term);
                                                     FStar_TypeChecker_Env.type_of
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.type_of);
                                                     FStar_TypeChecker_Env.universe_of
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.universe_of);
                                                     FStar_TypeChecker_Env.check_type_of
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.check_type_of);
                                                     FStar_TypeChecker_Env.use_bv_sorts
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.use_bv_sorts);
                                                     FStar_TypeChecker_Env.qname_and_index
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.qname_and_index);
                                                     FStar_TypeChecker_Env.proof_ns
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.proof_ns);
                                                     FStar_TypeChecker_Env.synth
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.synth);
                                                     FStar_TypeChecker_Env.is_native_tactic
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.is_native_tactic);
                                                     FStar_TypeChecker_Env.identifier_info
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.identifier_info);
                                                     FStar_TypeChecker_Env.tc_hooks
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.tc_hooks);
                                                     FStar_TypeChecker_Env.dsenv
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.dsenv);
                                                     FStar_TypeChecker_Env.dep_graph
                                                       =
                                                       (uu___68_1891.FStar_TypeChecker_Env.dep_graph)
                                                   } in
                                                 let br =
                                                   check_and_gen' env3
                                                     ed2.FStar_Syntax_Syntax.bind_repr
                                                     expected_k1 in
                                                 br) in
                                      let return_repr =
                                        let x_a =
                                          let uu____1901 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.gen_bv "x_a"
                                            FStar_Pervasives_Native.None
                                            uu____1901 in
                                        let res =
                                          let wp =
                                            let uu____1908 =
                                              let uu____1909 =
                                                let uu____1910 =
                                                  FStar_TypeChecker_Env.inst_tscheme
                                                    return_wp in
                                                FStar_All.pipe_right
                                                  uu____1910
                                                  FStar_Pervasives_Native.snd in
                                              let uu____1919 =
                                                let uu____1920 =
                                                  let uu____1923 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  let uu____1924 =
                                                    let uu____1927 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        x_a in
                                                    [uu____1927] in
                                                  uu____1923 :: uu____1924 in
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____1920 in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                uu____1909 uu____1919 in
                                            uu____1908
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange in
                                          mk_repr a wp in
                                        let expected_k =
                                          let uu____1933 =
                                            let uu____1940 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____1941 =
                                              let uu____1944 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  x_a in
                                              [uu____1944] in
                                            uu____1940 :: uu____1941 in
                                          let uu____1945 =
                                            FStar_Syntax_Syntax.mk_Total res in
                                          FStar_Syntax_Util.arrow uu____1933
                                            uu____1945 in
                                        let uu____1948 =
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            env1 expected_k in
                                        match uu____1948 with
                                        | (expected_k1,uu____1962,uu____1963)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (FStar_Pervasives_Native.snd
                                                   ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                            let uu____1967 =
                                              check_and_gen' env2
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                expected_k1 in
                                            (match uu____1967 with
                                             | (univs1,repr1) ->
                                                 (match univs1 with
                                                  | [] -> ([], repr1)
                                                  | uu____1988 ->
                                                      FStar_Errors.raise_error
                                                        (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                          "Unexpected universe-polymorphic return for effect")
                                                        repr1.FStar_Syntax_Syntax.pos)) in
                                      let actions =
                                        let check_action act =
                                          let uu____2013 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env1
                                              act.FStar_Syntax_Syntax.action_typ in
                                          match uu____2013 with
                                          | (act_typ,uu____2021,g_t) ->
                                              let env' =
                                                let uu___69_2024 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 act_typ in
                                                {
                                                  FStar_TypeChecker_Env.solver
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.solver);
                                                  FStar_TypeChecker_Env.range
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.range);
                                                  FStar_TypeChecker_Env.curmodule
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.curmodule);
                                                  FStar_TypeChecker_Env.gamma
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.gamma);
                                                  FStar_TypeChecker_Env.gamma_cache
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.gamma_cache);
                                                  FStar_TypeChecker_Env.modules
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.modules);
                                                  FStar_TypeChecker_Env.expected_typ
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.expected_typ);
                                                  FStar_TypeChecker_Env.sigtab
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.sigtab);
                                                  FStar_TypeChecker_Env.is_pattern
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.is_pattern);
                                                  FStar_TypeChecker_Env.instantiate_imp
                                                    = false;
                                                  FStar_TypeChecker_Env.effects
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.effects);
                                                  FStar_TypeChecker_Env.generalize
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.generalize);
                                                  FStar_TypeChecker_Env.letrecs
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.letrecs);
                                                  FStar_TypeChecker_Env.top_level
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.top_level);
                                                  FStar_TypeChecker_Env.check_uvars
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.check_uvars);
                                                  FStar_TypeChecker_Env.use_eq
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.use_eq);
                                                  FStar_TypeChecker_Env.is_iface
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.is_iface);
                                                  FStar_TypeChecker_Env.admit
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.admit);
                                                  FStar_TypeChecker_Env.lax =
                                                    (uu___69_2024.FStar_TypeChecker_Env.lax);
                                                  FStar_TypeChecker_Env.lax_universes
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.lax_universes);
                                                  FStar_TypeChecker_Env.failhard
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.failhard);
                                                  FStar_TypeChecker_Env.nosynth
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.nosynth);
                                                  FStar_TypeChecker_Env.tc_term
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.tc_term);
                                                  FStar_TypeChecker_Env.type_of
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.type_of);
                                                  FStar_TypeChecker_Env.universe_of
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.universe_of);
                                                  FStar_TypeChecker_Env.check_type_of
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.check_type_of);
                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.use_bv_sorts);
                                                  FStar_TypeChecker_Env.qname_and_index
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.qname_and_index);
                                                  FStar_TypeChecker_Env.proof_ns
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.proof_ns);
                                                  FStar_TypeChecker_Env.synth
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.synth);
                                                  FStar_TypeChecker_Env.is_native_tactic
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.is_native_tactic);
                                                  FStar_TypeChecker_Env.identifier_info
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.identifier_info);
                                                  FStar_TypeChecker_Env.tc_hooks
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.tc_hooks);
                                                  FStar_TypeChecker_Env.dsenv
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.dsenv);
                                                  FStar_TypeChecker_Env.dep_graph
                                                    =
                                                    (uu___69_2024.FStar_TypeChecker_Env.dep_graph)
                                                } in
                                              ((let uu____2026 =
                                                  FStar_TypeChecker_Env.debug
                                                    env1
                                                    (FStar_Options.Other "ED") in
                                                if uu____2026
                                                then
                                                  let uu____2027 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act.FStar_Syntax_Syntax.action_defn in
                                                  let uu____2028 =
                                                    FStar_Syntax_Print.term_to_string
                                                      act_typ in
                                                  FStar_Util.print3
                                                    "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                    (FStar_Ident.text_of_lid
                                                       act.FStar_Syntax_Syntax.action_name)
                                                    uu____2027 uu____2028
                                                else ());
                                               (let uu____2030 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env'
                                                    act.FStar_Syntax_Syntax.action_defn in
                                                match uu____2030 with
                                                | (act_defn,uu____2038,g_a)
                                                    ->
                                                    let act_defn1 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant]
                                                        env1 act_defn in
                                                    let act_typ1 =
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.UnfoldUntil
                                                           FStar_Syntax_Syntax.Delta_constant;
                                                        FStar_TypeChecker_Normalize.Eager_unfolding;
                                                        FStar_TypeChecker_Normalize.Beta]
                                                        env1 act_typ in
                                                    let uu____2042 =
                                                      let act_typ2 =
                                                        FStar_Syntax_Subst.compress
                                                          act_typ1 in
                                                      match act_typ2.FStar_Syntax_Syntax.n
                                                      with
                                                      | FStar_Syntax_Syntax.Tm_arrow
                                                          (bs,c) ->
                                                          let uu____2070 =
                                                            FStar_Syntax_Subst.open_comp
                                                              bs c in
                                                          (match uu____2070
                                                           with
                                                           | (bs1,uu____2080)
                                                               ->
                                                               let res =
                                                                 mk_repr'
                                                                   FStar_Syntax_Syntax.tun
                                                                   FStar_Syntax_Syntax.tun in
                                                               let k =
                                                                 let uu____2087
                                                                   =
                                                                   FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                 FStar_Syntax_Util.arrow
                                                                   bs1
                                                                   uu____2087 in
                                                               let uu____2090
                                                                 =
                                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                   env1 k in
                                                               (match uu____2090
                                                                with
                                                                | (k1,uu____2102,g)
                                                                    ->
                                                                    (k1, g)))
                                                      | uu____2104 ->
                                                          let uu____2105 =
                                                            let uu____2110 =
                                                              let uu____2111
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ2 in
                                                              let uu____2112
                                                                =
                                                                FStar_Syntax_Print.tag_of_term
                                                                  act_typ2 in
                                                              FStar_Util.format2
                                                                "Actions must have function types (not: %s, a.k.a. %s)"
                                                                uu____2111
                                                                uu____2112 in
                                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                              uu____2110) in
                                                          FStar_Errors.raise_error
                                                            uu____2105
                                                            act_defn1.FStar_Syntax_Syntax.pos in
                                                    (match uu____2042 with
                                                     | (expected_k,g_k) ->
                                                         let g =
                                                           FStar_TypeChecker_Rel.teq
                                                             env1 act_typ1
                                                             expected_k in
                                                         ((let uu____2121 =
                                                             let uu____2122 =
                                                               let uu____2123
                                                                 =
                                                                 FStar_TypeChecker_Rel.conj_guard
                                                                   g_t g in
                                                               FStar_TypeChecker_Rel.conj_guard
                                                                 g_k
                                                                 uu____2123 in
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               g_a uu____2122 in
                                                           FStar_TypeChecker_Rel.force_trivial_guard
                                                             env1 uu____2121);
                                                          (let act_typ2 =
                                                             let uu____2127 =
                                                               let uu____2128
                                                                 =
                                                                 FStar_Syntax_Subst.compress
                                                                   expected_k in
                                                               uu____2128.FStar_Syntax_Syntax.n in
                                                             match uu____2127
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____2151
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c in
                                                                 (match uu____2151
                                                                  with
                                                                  | (bs1,c1)
                                                                    ->
                                                                    let uu____2160
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____2160
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____2182
                                                                    =
                                                                    let uu____2183
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1 in
                                                                    [uu____2183] in
                                                                    let uu____2184
                                                                    =
                                                                    let uu____2193
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____2193] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2182;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2184;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____2194
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____2194))
                                                             | uu____2197 ->
                                                                 failwith
                                                                   "Impossible (expected_k is an arrow)" in
                                                           let uu____2200 =
                                                             FStar_TypeChecker_Util.generalize_universes
                                                               env1 act_defn1 in
                                                           match uu____2200
                                                           with
                                                           | (univs1,act_defn2)
                                                               ->
                                                               let act_typ3 =
                                                                 FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Normalize.Beta]
                                                                   env1
                                                                   act_typ2 in
                                                               let act_typ4 =
                                                                 FStar_Syntax_Subst.close_univ_vars
                                                                   univs1
                                                                   act_typ3 in
                                                               let uu___70_2209
                                                                 = act in
                                                               {
                                                                 FStar_Syntax_Syntax.action_name
                                                                   =
                                                                   (uu___70_2209.FStar_Syntax_Syntax.action_name);
                                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                                   =
                                                                   (uu___70_2209.FStar_Syntax_Syntax.action_unqualified_name);
                                                                 FStar_Syntax_Syntax.action_univs
                                                                   = univs1;
                                                                 FStar_Syntax_Syntax.action_params
                                                                   =
                                                                   (uu___70_2209.FStar_Syntax_Syntax.action_params);
                                                                 FStar_Syntax_Syntax.action_defn
                                                                   =
                                                                   act_defn2;
                                                                 FStar_Syntax_Syntax.action_typ
                                                                   = act_typ4
                                                               }))))) in
                                        FStar_All.pipe_right
                                          ed2.FStar_Syntax_Syntax.actions
                                          (FStar_List.map check_action) in
                                      (repr, bind_repr, return_repr, actions) in
                                match uu____1558 with
                                | (repr,bind_repr,return_repr,actions) ->
                                    let t0 =
                                      let uu____2233 =
                                        FStar_Syntax_Syntax.mk_Total
                                          ed2.FStar_Syntax_Syntax.signature in
                                      FStar_Syntax_Util.arrow
                                        ed2.FStar_Syntax_Syntax.binders
                                        uu____2233 in
                                    let uu____2236 =
                                      let uu____2243 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env0 t0 in
                                      match uu____2243 with
                                      | (gen_univs,t) ->
                                          (match annotated_univ_names with
                                           | [] -> (gen_univs, t)
                                           | uu____2264 ->
                                               let uu____2267 =
                                                 ((FStar_List.length
                                                     gen_univs)
                                                    =
                                                    (FStar_List.length
                                                       annotated_univ_names))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           (FStar_Syntax_Syntax.order_univ_name
                                                              u1 u2)
                                                             =
                                                             (Prims.parse_int
                                                                "0"))
                                                      gen_univs
                                                      annotated_univ_names) in
                                               if uu____2267
                                               then (gen_univs, t)
                                               else
                                                 (let uu____2281 =
                                                    let uu____2286 =
                                                      let uu____2287 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             annotated_univ_names) in
                                                      let uu____2288 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             gen_univs) in
                                                      FStar_Util.format2
                                                        "Expected an effect definition with %s universes; but found %s"
                                                        uu____2287 uu____2288 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____2286) in
                                                  FStar_Errors.raise_error
                                                    uu____2281
                                                    (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos)) in
                                    (match uu____2236 with
                                     | (univs1,t) ->
                                         let signature1 =
                                           let uu____2302 =
                                             let uu____2307 =
                                               let uu____2308 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____2308.FStar_Syntax_Syntax.n in
                                             (effect_params, uu____2307) in
                                           match uu____2302 with
                                           | ([],uu____2311) -> t
                                           | (uu____2322,FStar_Syntax_Syntax.Tm_arrow
                                              (uu____2323,c)) ->
                                               FStar_Syntax_Util.comp_result
                                                 c
                                           | uu____2341 ->
                                               failwith
                                                 "Impossible : t is an arrow" in
                                         let close1 n1 ts =
                                           let ts1 =
                                             let uu____2354 =
                                               FStar_Syntax_Subst.close_tscheme
                                                 effect_params ts in
                                             FStar_Syntax_Subst.close_univ_vars_tscheme
                                               univs1 uu____2354 in
                                           let m =
                                             FStar_List.length
                                               (FStar_Pervasives_Native.fst
                                                  ts1) in
                                           (let uu____2359 =
                                              ((n1 >= (Prims.parse_int "0"))
                                                 &&
                                                 (let uu____2361 =
                                                    FStar_Syntax_Util.is_unknown
                                                      (FStar_Pervasives_Native.snd
                                                         ts1) in
                                                  Prims.op_Negation
                                                    uu____2361))
                                                && (m <> n1) in
                                            if uu____2359
                                            then
                                              let error =
                                                if m < n1
                                                then
                                                  "not universe-polymorphic enough"
                                                else
                                                  "too universe-polymorphic" in
                                              let err_msg =
                                                let uu____2377 =
                                                  FStar_Util.string_of_int m in
                                                let uu____2384 =
                                                  FStar_Util.string_of_int n1 in
                                                let uu____2385 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    ts1 in
                                                FStar_Util.format4
                                                  "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                  error uu____2377 uu____2384
                                                  uu____2385 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                  err_msg)
                                                (FStar_Pervasives_Native.snd
                                                   ts1).FStar_Syntax_Syntax.pos
                                            else ());
                                           ts1 in
                                         let close_action act =
                                           let uu____2393 =
                                             close1 (- (Prims.parse_int "1"))
                                               ((act.FStar_Syntax_Syntax.action_univs),
                                                 (act.FStar_Syntax_Syntax.action_defn)) in
                                           match uu____2393 with
                                           | (univs2,defn) ->
                                               let uu____2400 =
                                                 close1
                                                   (- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_typ)) in
                                               (match uu____2400 with
                                                | (univs',typ) ->
                                                    let uu___71_2410 = act in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___71_2410.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___71_2410.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = univs2;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___71_2410.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = defn;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = typ
                                                    }) in
                                         let ed3 =
                                           let uu___72_2415 = ed2 in
                                           let uu____2416 =
                                             close1 (Prims.parse_int "0")
                                               return_wp in
                                           let uu____2417 =
                                             close1 (Prims.parse_int "1")
                                               bind_wp in
                                           let uu____2418 =
                                             close1 (Prims.parse_int "0")
                                               if_then_else1 in
                                           let uu____2419 =
                                             close1 (Prims.parse_int "0")
                                               ite_wp in
                                           let uu____2420 =
                                             close1 (Prims.parse_int "0")
                                               stronger in
                                           let uu____2421 =
                                             close1 (Prims.parse_int "1")
                                               close_wp in
                                           let uu____2422 =
                                             close1 (Prims.parse_int "0")
                                               assert_p in
                                           let uu____2423 =
                                             close1 (Prims.parse_int "0")
                                               assume_p in
                                           let uu____2424 =
                                             close1 (Prims.parse_int "0")
                                               null_wp in
                                           let uu____2425 =
                                             close1 (Prims.parse_int "0")
                                               trivial_wp in
                                           let uu____2426 =
                                             let uu____2427 =
                                               close1 (Prims.parse_int "0")
                                                 ([], repr) in
                                             FStar_Pervasives_Native.snd
                                               uu____2427 in
                                           let uu____2438 =
                                             close1 (Prims.parse_int "0")
                                               return_repr in
                                           let uu____2439 =
                                             close1 (Prims.parse_int "1")
                                               bind_repr in
                                           let uu____2440 =
                                             FStar_List.map close_action
                                               actions in
                                           {
                                             FStar_Syntax_Syntax.cattributes
                                               =
                                               (uu___72_2415.FStar_Syntax_Syntax.cattributes);
                                             FStar_Syntax_Syntax.mname =
                                               (uu___72_2415.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.univs =
                                               univs1;
                                             FStar_Syntax_Syntax.binders =
                                               effect_params;
                                             FStar_Syntax_Syntax.signature =
                                               signature1;
                                             FStar_Syntax_Syntax.ret_wp =
                                               uu____2416;
                                             FStar_Syntax_Syntax.bind_wp =
                                               uu____2417;
                                             FStar_Syntax_Syntax.if_then_else
                                               = uu____2418;
                                             FStar_Syntax_Syntax.ite_wp =
                                               uu____2419;
                                             FStar_Syntax_Syntax.stronger =
                                               uu____2420;
                                             FStar_Syntax_Syntax.close_wp =
                                               uu____2421;
                                             FStar_Syntax_Syntax.assert_p =
                                               uu____2422;
                                             FStar_Syntax_Syntax.assume_p =
                                               uu____2423;
                                             FStar_Syntax_Syntax.null_wp =
                                               uu____2424;
                                             FStar_Syntax_Syntax.trivial =
                                               uu____2425;
                                             FStar_Syntax_Syntax.repr =
                                               uu____2426;
                                             FStar_Syntax_Syntax.return_repr
                                               = uu____2438;
                                             FStar_Syntax_Syntax.bind_repr =
                                               uu____2439;
                                             FStar_Syntax_Syntax.actions =
                                               uu____2440
                                           } in
                                         ((let uu____2444 =
                                             (FStar_TypeChecker_Env.debug
                                                env1 FStar_Options.Low)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "ED")) in
                                           if uu____2444
                                           then
                                             let uu____2445 =
                                               FStar_Syntax_Print.eff_decl_to_string
                                                 false ed3 in
                                             FStar_Util.print_string
                                               uu____2445
                                           else ());
                                          ed3))))))))
let cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ed  ->
      let uu____2463 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____2463 with
      | (effect_binders_un,signature_un) ->
          let uu____2480 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____2480 with
           | (effect_binders,env1,uu____2499) ->
               let uu____2500 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un in
               (match uu____2500 with
                | (signature,uu____2516) ->
                    let raise_error1 a uu____2527 =
                      match uu____2527 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____2553  ->
                           match uu____2553 with
                           | (bv,qual) ->
                               let uu____2564 =
                                 let uu___73_2565 = bv in
                                 let uu____2566 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___73_2565.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___73_2565.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____2566
                                 } in
                               (uu____2564, qual)) effect_binders in
                    let uu____2569 =
                      let uu____2576 =
                        let uu____2577 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____2577.FStar_Syntax_Syntax.n in
                      Obj.magic
                        (match uu____2576 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____2587)::[],effect_marker) ->
                             Obj.repr (a, effect_marker)
                         | uu____2609 ->
                             Obj.repr
                               (raise_error1 ()
                                  (FStar_Errors.Fatal_BadSignatureShape,
                                    "bad shape for effect-for-free signature"))) in
                    (match uu____2569 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____2627 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____2627
                           then
                             let uu____2628 =
                               let uu____2631 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____2631 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____2628
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst1 t in
                           let uu____2665 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1 in
                           match uu____2665 with
                           | (t2,comp,uu____2678) -> (t2, comp) in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____2685 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr in
                         (match uu____2685 with
                          | (repr,_comp) ->
                              ((let uu____2707 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED") in
                                if uu____2707
                                then
                                  let uu____2708 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____2708
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let wp_type1 = recheck_debug "*" env1 wp_type in
                                let wp_a =
                                  let uu____2714 =
                                    let uu____2715 =
                                      let uu____2716 =
                                        let uu____2731 =
                                          let uu____2738 =
                                            let uu____2743 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____2744 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____2743, uu____2744) in
                                          [uu____2738] in
                                        (wp_type1, uu____2731) in
                                      FStar_Syntax_Syntax.Tm_app uu____2716 in
                                    mk1 uu____2715 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____2714 in
                                let effect_signature =
                                  let binders =
                                    let uu____2769 =
                                      let uu____2774 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____2774) in
                                    let uu____2775 =
                                      let uu____2782 =
                                        let uu____2783 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____2783
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____2782] in
                                    uu____2769 :: uu____2775 in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker)) in
                                let effect_signature1 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature in
                                let sigelts = FStar_Util.mk_ref [] in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env2 =
                                    FStar_TypeChecker_DMFF.get_env dmff_env1 in
                                  let uu____2846 = item in
                                  match uu____2846 with
                                  | (u_item,item1) ->
                                      let uu____2867 =
                                        open_and_check env2 other_binders
                                          item1 in
                                      (match uu____2867 with
                                       | (item2,item_comp) ->
                                           ((let uu____2883 =
                                               let uu____2884 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____2884 in
                                             if uu____2883
                                             then
                                               let uu____2885 =
                                                 let uu____2890 =
                                                   let uu____2891 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____2892 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____2891 uu____2892 in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____2890) in
                                               FStar_Errors.raise_err
                                                 uu____2885
                                             else ());
                                            (let uu____2894 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2 in
                                             match uu____2894 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp1 =
                                                   recheck_debug "*" env2
                                                     item_wp in
                                                 let item_elab1 =
                                                   recheck_debug "_" env2
                                                     item_elab in
                                                 (dmff_env1, item_t,
                                                   item_wp1, item_elab1)))) in
                                let uu____2914 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____2914 with
                                | (dmff_env1,uu____2938,bind_wp,bind_elab) ->
                                    let uu____2941 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____2941 with
                                     | (dmff_env2,uu____2965,return_wp,return_elab)
                                         ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           } in
                                         let lift_from_pure_wp =
                                           let uu____2972 =
                                             let uu____2973 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____2973.FStar_Syntax_Syntax.n in
                                           Obj.magic
                                             (match uu____2972 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____3017 =
                                                       let uu____3032 =
                                                         let uu____3037 =
                                                           FStar_Syntax_Util.abs
                                                             bs body
                                                             FStar_Pervasives_Native.None in
                                                         FStar_Syntax_Subst.open_term
                                                           [b1; b2]
                                                           uu____3037 in
                                                       match uu____3032 with
                                                       | (b11::b21::[],body1)
                                                           ->
                                                           (b11, b21, body1)
                                                       | uu____3101 ->
                                                           failwith
                                                             "Impossible : open_term not preserving binders arity" in
                                                     match uu____3017 with
                                                     | (b11,b21,body1) ->
                                                         let env0 =
                                                           let uu____3140 =
                                                             FStar_TypeChecker_DMFF.get_env
                                                               dmff_env2 in
                                                           FStar_TypeChecker_Env.push_binders
                                                             uu____3140
                                                             [b11; b21] in
                                                         let wp_b1 =
                                                           let raw_wp_b1 =
                                                             let uu____3157 =
                                                               let uu____3158
                                                                 =
                                                                 let uu____3173
                                                                   =
                                                                   let uu____3180
                                                                    =
                                                                    let uu____3185
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                    let uu____3186
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                    (uu____3185,
                                                                    uu____3186) in
                                                                   [uu____3180] in
                                                                 (wp_type1,
                                                                   uu____3173) in
                                                               FStar_Syntax_Syntax.Tm_app
                                                                 uu____3158 in
                                                             mk1 uu____3157 in
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Normalize.Beta]
                                                             env0 raw_wp_b1 in
                                                         let uu____3201 =
                                                           let uu____3210 =
                                                             let uu____3211 =
                                                               FStar_Syntax_Util.unascribe
                                                                 wp_b1 in
                                                             FStar_TypeChecker_Normalize.eta_expand_with_type
                                                               env0 body1
                                                               uu____3211 in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Util.abs_formals
                                                             uu____3210 in
                                                         (match uu____3201
                                                          with
                                                          | (bs1,body2,what')
                                                              ->
                                                              let fail a412 =
                                                                (Obj.magic
                                                                   (fun
                                                                    uu____3230
                                                                     ->
                                                                    let error_msg
                                                                    =
                                                                    let uu____3232
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    body2 in
                                                                    FStar_Util.format2
                                                                    "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                    uu____3232
                                                                    (match what'
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect) in
                                                                    raise_error1
                                                                    ()
                                                                    (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                                    error_msg)))
                                                                  a412 in
                                                              ((match what'
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ()
                                                                | FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    (
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect)
                                                                    then
                                                                    fail ()
                                                                    else ();
                                                                    (
                                                                    let uu____3238
                                                                    =
                                                                    FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt 
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0 in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ()) in
                                                                    FStar_All.pipe_right
                                                                    uu____3238
                                                                    FStar_Pervasives.ignore)));
                                                               (let wp =
                                                                  let t2 =
                                                                    (FStar_Pervasives_Native.fst
                                                                    b21).FStar_Syntax_Syntax.sort in
                                                                  let pure_wp_type
                                                                    =
                                                                    FStar_TypeChecker_DMFF.double_star
                                                                    t2 in
                                                                  FStar_Syntax_Syntax.gen_bv
                                                                    "wp"
                                                                    FStar_Pervasives_Native.None
                                                                    pure_wp_type in
                                                                let body3 =
                                                                  let uu____3265
                                                                    =
                                                                    let uu____3266
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp in
                                                                    let uu____3267
                                                                    =
                                                                    let uu____3268
                                                                    =
                                                                    let uu____3275
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                    (uu____3275,
                                                                    FStar_Pervasives_Native.None) in
                                                                    [uu____3268] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____3266
                                                                    uu____3267 in
                                                                  uu____3265
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange in
                                                                let uu____3300
                                                                  =
                                                                  let uu____3301
                                                                    =
                                                                    let uu____3308
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp in
                                                                    [uu____3308] in
                                                                  b11 ::
                                                                    uu____3301 in
                                                                let uu____3313
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    bs1 body3
                                                                    what in
                                                                FStar_Syntax_Util.abs
                                                                  uu____3300
                                                                  uu____3313
                                                                  (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                              | uu____3314 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return"))) in
                                         let return_wp1 =
                                           let uu____3316 =
                                             let uu____3317 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____3317.FStar_Syntax_Syntax.n in
                                           Obj.magic
                                             (match uu____3316 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (b1::b2::bs,body,what) ->
                                                  Obj.repr
                                                    (let uu____3361 =
                                                       FStar_Syntax_Util.abs
                                                         bs body what in
                                                     FStar_Syntax_Util.abs
                                                       [b1; b2] uu____3361
                                                       (FStar_Pervasives_Native.Some
                                                          rc_gtot))
                                              | uu____3374 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                         "unexpected shape for return"))) in
                                         let bind_wp1 =
                                           let uu____3376 =
                                             let uu____3377 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____3377.FStar_Syntax_Syntax.n in
                                           Obj.magic
                                             (match uu____3376 with
                                              | FStar_Syntax_Syntax.Tm_abs
                                                  (binders,body,what) ->
                                                  Obj.repr
                                                    (let r =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         FStar_Parser_Const.range_lid
                                                         (FStar_Syntax_Syntax.Delta_defined_at_level
                                                            (Prims.parse_int
                                                               "1"))
                                                         FStar_Pervasives_Native.None in
                                                     let uu____3404 =
                                                       let uu____3405 =
                                                         let uu____3408 =
                                                           let uu____3409 =
                                                             mk1
                                                               (FStar_Syntax_Syntax.Tm_fvar
                                                                  r) in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____3409 in
                                                         [uu____3408] in
                                                       FStar_List.append
                                                         uu____3405 binders in
                                                     FStar_Syntax_Util.abs
                                                       uu____3404 body what)
                                              | uu____3410 ->
                                                  Obj.repr
                                                    (raise_error1 ()
                                                       (FStar_Errors.Fatal_UnexpectedBindShape,
                                                         "unexpected shape for bind"))) in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____3428 =
                                                let uu____3429 =
                                                  let uu____3430 =
                                                    let uu____3445 =
                                                      let uu____3446 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____3446 in
                                                    (t, uu____3445) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____3430 in
                                                mk1 uu____3429 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____3428) in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____3476 = f a2 in
                                               [uu____3476]
                                           | x::xs ->
                                               let uu____3481 =
                                                 apply_last1 f xs in
                                               x :: uu____3481 in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.strcat "__"
                                                    (Prims.strcat s
                                                       (Prims.strcat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange in
                                           let uu____3501 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l' in
                                           match uu____3501 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____3531 =
                                                   FStar_Options.debug_any () in
                                                 if uu____3531
                                                 then
                                                   let uu____3532 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____3532
                                                 else ());
                                                (let uu____3534 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.Delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____3534))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____3543 =
                                                 let uu____3548 = mk_lid name in
                                                 let uu____3549 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____3548 uu____3549 in
                                               (match uu____3543 with
                                                | (sigelt,fv) ->
                                                    ((let uu____3553 =
                                                        let uu____3556 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt :: uu____3556 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____3553);
                                                     fv)) in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp2 =
                                           register "return_wp" return_wp1 in
                                         (FStar_Options.push ();
                                          (let uu____3653 =
                                             let uu____3656 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries true")) in
                                             let uu____3657 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____3656 :: uu____3657 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____3653);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab in
                                           FStar_Options.pop ();
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1 in
                                            FStar_Options.push ();
                                            (let uu____3755 =
                                               let uu____3758 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.SetOptions
                                                         "--admit_smt_queries true")) in
                                               let uu____3759 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____3758 :: uu____3759 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____3755);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab in
                                             FStar_Options.pop ();
                                             (let uu____3854 =
                                                FStar_List.fold_left
                                                  (fun uu____3894  ->
                                                     fun action  ->
                                                       match uu____3894 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____3915 =
                                                             let uu____3922 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____3922
                                                               params_un in
                                                           (match uu____3915
                                                            with
                                                            | (action_params,env',uu____3931)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____3951
                                                                     ->
                                                                    match uu____3951
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____3962
                                                                    =
                                                                    let uu___74_3963
                                                                    = bv in
                                                                    let uu____3964
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Normalize.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___74_3963.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___74_3963.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____3964
                                                                    } in
                                                                    (uu____3962,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____3968
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____3968
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1 in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    FStar_Pervasives_Native.None in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____3998
                                                                    ->
                                                                    let uu____3999
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____3999 in
                                                                    ((
                                                                    let uu____4003
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____4003
                                                                    then
                                                                    let uu____4004
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____4005
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____4006
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____4007
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____4004
                                                                    uu____4005
                                                                    uu____4006
                                                                    uu____4007
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
                                                                    let uu____4011
                                                                    =
                                                                    let uu____4014
                                                                    =
                                                                    let uu___75_4015
                                                                    = action in
                                                                    let uu____4016
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____4017
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___75_4015.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___75_4015.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___75_4015.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____4016;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____4017
                                                                    } in
                                                                    uu____4014
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____4011))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____3854 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a in
                                                    let binders =
                                                      let uu____4050 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____4051 =
                                                        let uu____4054 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____4054] in
                                                      uu____4050 ::
                                                        uu____4051 in
                                                    let uu____4055 =
                                                      let uu____4056 =
                                                        let uu____4057 =
                                                          let uu____4058 =
                                                            let uu____4073 =
                                                              let uu____4080
                                                                =
                                                                let uu____4085
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____4086
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____4085,
                                                                  uu____4086) in
                                                              [uu____4080] in
                                                            (repr,
                                                              uu____4073) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____4058 in
                                                        mk1 uu____4057 in
                                                      let uu____4101 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____4056
                                                        uu____4101 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____4055
                                                      FStar_Pervasives_Native.None in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1 in
                                                  let repr3 =
                                                    register "repr" repr2 in
                                                  let uu____4104 =
                                                    let uu____4111 =
                                                      let uu____4112 =
                                                        let uu____4115 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1 in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____4115 in
                                                      uu____4112.FStar_Syntax_Syntax.n in
                                                    Obj.magic
                                                      (match uu____4111 with
                                                       | FStar_Syntax_Syntax.Tm_abs
                                                           (type_param::effect_param,arrow1,uu____4125)
                                                           ->
                                                           Obj.repr
                                                             (let uu____4154
                                                                =
                                                                let uu____4171
                                                                  =
                                                                  FStar_Syntax_Subst.open_term
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    arrow1 in
                                                                match uu____4171
                                                                with
                                                                | (b::bs,body)
                                                                    ->
                                                                    (b, bs,
                                                                    body)
                                                                | uu____4229
                                                                    ->
                                                                    failwith
                                                                    "Impossible : open_term nt preserving binders arity" in
                                                              match uu____4154
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____4279
                                                                    =
                                                                    let uu____4280
                                                                    =
                                                                    let uu____4283
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2 in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____4283 in
                                                                    uu____4280.FStar_Syntax_Syntax.n in
                                                                  Obj.magic
                                                                    (
                                                                    match uu____4279
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4308
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                    match uu____4308
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____4321
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____4346
                                                                     ->
                                                                    match uu____4346
                                                                    with
                                                                    | 
                                                                    (bv,uu____4352)
                                                                    ->
                                                                    let uu____4353
                                                                    =
                                                                    let uu____4354
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____4354
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____4353
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____4321
                                                                    with
                                                                    | 
                                                                    (pre_args,post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post::[]
                                                                    -> post
                                                                    | 
                                                                    [] ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4418
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____4418 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____4423
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____4431
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____4431 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg) in
                                                                    let uu____4436
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____4439
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____4436,
                                                                    uu____4439)))
                                                                    | 
                                                                    uu____4446
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu____4447
                                                                    =
                                                                    let uu____4452
                                                                    =
                                                                    let uu____4453
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____4453 in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____4452) in
                                                                    raise_error1
                                                                    ()
                                                                    uu____4447)))
                                                       | uu____4454 ->
                                                           Obj.repr
                                                             (let uu____4455
                                                                =
                                                                let uu____4460
                                                                  =
                                                                  let uu____4461
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    wp_type1 in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post abs %s"
                                                                    uu____4461 in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                  uu____4460) in
                                                              raise_error1 ()
                                                                uu____4455)) in
                                                  (match uu____4104 with
                                                   | (pre,post) ->
                                                       ((let uu____4479 =
                                                           register "pre" pre in
                                                         ());
                                                        (let uu____4481 =
                                                           register "post"
                                                             post in
                                                         ());
                                                        (let uu____4483 =
                                                           register "wp"
                                                             wp_type1 in
                                                         ());
                                                        (let ed1 =
                                                           let uu___76_4485 =
                                                             ed in
                                                           let uu____4486 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____4487 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1 in
                                                           let uu____4488 =
                                                             let uu____4489 =
                                                               apply_close
                                                                 return_wp2 in
                                                             ([], uu____4489) in
                                                           let uu____4496 =
                                                             let uu____4497 =
                                                               apply_close
                                                                 bind_wp2 in
                                                             ([], uu____4497) in
                                                           let uu____4504 =
                                                             apply_close
                                                               repr3 in
                                                           let uu____4505 =
                                                             let uu____4506 =
                                                               apply_close
                                                                 return_elab1 in
                                                             ([], uu____4506) in
                                                           let uu____4513 =
                                                             let uu____4514 =
                                                               apply_close
                                                                 bind_elab1 in
                                                             ([], uu____4514) in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____4486;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____4487;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____4488;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____4496;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___76_4485.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____4504;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____4505;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____4513;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           } in
                                                         let uu____4521 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____4521
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____4539
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____4539
                                                               then
                                                                 let uu____4540
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____4540
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int
                                                                    "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____4552
                                                                    =
                                                                    let uu____4555
                                                                    =
                                                                    let uu____4564
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____4564) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4555 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____4552;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____4579
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____4579
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____4581
                                                                 =
                                                                 let uu____4584
                                                                   =
                                                                   let uu____4587
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____4587 in
                                                                 FStar_List.append
                                                                   uu____4584
                                                                   sigelts' in
                                                               (uu____4581,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
let tc_lex_t:
  'Auu____4644 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____4644 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____4677 = FStar_List.hd ses in
            uu____4677.FStar_Syntax_Syntax.sigrng in
          (match lids with
           | lex_t1::lex_top1::lex_cons::[] when
               ((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
                  &&
                  (FStar_Ident.lid_equals lex_top1
                     FStar_Parser_Const.lextop_lid))
                 &&
                 (FStar_Ident.lid_equals lex_cons
                    FStar_Parser_Const.lexcons_lid)
               -> ()
           | uu____4682 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,[],[],t,uu____4687,uu____4688);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____4690;
               FStar_Syntax_Syntax.sigattrs = uu____4691;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,[],_t_top,_lex_t_top,_0_40,uu____4695);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____4697;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____4698;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,[],_t_cons,_lex_t_cons,_0_41,uu____4702);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____4704;
                 FStar_Syntax_Syntax.sigattrs = uu____4705;_}::[]
               when
               ((_0_40 = (Prims.parse_int "0")) &&
                  (_0_41 = (Prims.parse_int "0")))
                 &&
                 (((FStar_Ident.lid_equals lex_t1
                      FStar_Parser_Const.lex_t_lid)
                     &&
                     (FStar_Ident.lid_equals lex_top1
                        FStar_Parser_Const.lextop_lid))
                    &&
                    (FStar_Ident.lid_equals lex_cons
                       FStar_Parser_Const.lexcons_lid))
               ->
               let u =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r) in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_type
                      (FStar_Syntax_Syntax.U_name u))
                   FStar_Pervasives_Native.None r in
               let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1 in
               let tc =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_inductive_typ
                        (lex_t1, [u], [], t2, [],
                          [FStar_Parser_Const.lextop_lid;
                          FStar_Parser_Const.lexcons_lid]));
                   FStar_Syntax_Syntax.sigrng = r;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1) in
               let lex_top_t =
                 let uu____4770 =
                   let uu____4773 =
                     let uu____4774 =
                       let uu____4781 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Parser_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____4781, [FStar_Syntax_Syntax.U_name utop]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____4774 in
                   FStar_Syntax_Syntax.mk uu____4773 in
                 uu____4770 FStar_Pervasives_Native.None r1 in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r1;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let ucons1 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let ucons2 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let lex_cons_t =
                 let a =
                   let uu____4799 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4799 in
                 let hd1 =
                   let uu____4801 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4801 in
                 let tl1 =
                   let uu____4803 =
                     let uu____4804 =
                       let uu____4807 =
                         let uu____4808 =
                           let uu____4815 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Parser_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           (uu____4815, [FStar_Syntax_Syntax.U_name ucons2]) in
                         FStar_Syntax_Syntax.Tm_uinst uu____4808 in
                       FStar_Syntax_Syntax.mk uu____4807 in
                     uu____4804 FStar_Pervasives_Native.None r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____4803 in
                 let res =
                   let uu____4824 =
                     let uu____4827 =
                       let uu____4828 =
                         let uu____4835 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Parser_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4835,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____4828 in
                     FStar_Syntax_Syntax.mk uu____4827 in
                   uu____4824 FStar_Pervasives_Native.None r2 in
                 let uu____4841 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____4841 in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t in
               let dc_lexcons =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_cons, [ucons1; ucons2], lex_cons_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let uu____4880 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____4880;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____4885 ->
               let err_msg =
                 let uu____4889 =
                   let uu____4890 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____4890 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____4889 in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
let tc_assume:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.formula ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Range.range -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun lid  ->
      fun phi  ->
        fun quals  ->
          fun r  ->
            let env1 = FStar_TypeChecker_Env.set_range env r in
            let uu____4915 = FStar_Syntax_Util.type_u () in
            match uu____4915 with
            | (k,uu____4921) ->
                let phi1 =
                  let uu____4923 = tc_check_trivial_guard env1 phi k in
                  FStar_All.pipe_right uu____4923
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env1) in
                (FStar_TypeChecker_Util.check_uvars r phi1;
                 (let uu____4925 =
                    FStar_TypeChecker_Util.generalize_universes env1 phi1 in
                  match uu____4925 with
                  | (us,phi2) ->
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_assume (lid, us, phi2));
                        FStar_Syntax_Syntax.sigrng = r;
                        FStar_Syntax_Syntax.sigquals = quals;
                        FStar_Syntax_Syntax.sigmeta =
                          FStar_Syntax_Syntax.default_sigmeta;
                        FStar_Syntax_Syntax.sigattrs = []
                      }))
let tc_inductive:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
          let uu____4967 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1
              ses quals lids in
          match uu____4967 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____5000 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs)
                    datas in
                FStar_All.pipe_right uu____5000 FStar_List.flatten in
              ((let uu____5014 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____5014
                then ()
                else
                  (let env2 =
                     FStar_TypeChecker_Env.push_sigelt env1 sig_bndle in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env2 in
                        if Prims.op_Negation b
                        then
                          let uu____5025 =
                            match ty.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____5035,uu____5036,uu____5037,uu____5038,uu____5039)
                                -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                            | uu____5048 -> failwith "Impossible!" in
                          match uu____5025 with
                          | (lid,r) ->
                              FStar_Errors.log_issue r
                                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                  (Prims.strcat "Inductive type "
                                     (Prims.strcat lid.FStar_Ident.str
                                        " does not satisfy the positivity condition")))
                        else ()) tcs));
               (let skip_prims_type uu____5059 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____5063,uu____5064,uu____5065,uu____5066,uu____5067)
                        -> lid
                    | uu____5076 -> failwith "Impossible" in
                  let types_to_skip =
                    ["c_False";
                    "c_True";
                    "equals";
                    "h_equals";
                    "c_and";
                    "c_or"] in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    types_to_skip in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals in
                let res =
                  let uu____5094 =
                    (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                       ((FStar_Ident.lid_equals
                           env1.FStar_TypeChecker_Env.curmodule
                           FStar_Parser_Const.prims_lid)
                          && (skip_prims_type ())))
                      || is_noeq in
                  if uu____5094
                  then ([sig_bndle], data_ops_ses)
                  else
                    (let is_unopteq =
                       FStar_List.existsb
                         (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals in
                     let ses1 =
                       if is_unopteq
                       then
                         FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume
                       else
                         FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                           sig_bndle tcs datas env1 tc_assume in
                     let uu____5117 =
                       let uu____5120 =
                         let uu____5121 =
                           FStar_TypeChecker_Env.get_range env1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_bundle
                                ((FStar_List.append tcs datas), lids));
                           FStar_Syntax_Syntax.sigrng = uu____5121;
                           FStar_Syntax_Syntax.sigquals = quals;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = []
                         } in
                       uu____5120 :: ses1 in
                     (uu____5117, data_ops_ses)) in
                (let uu____5131 =
                   FStar_TypeChecker_Env.pop env1 "tc_inductive" in
                 ());
                res))
let tc_decl:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env1 se;
      (let r = se.FStar_Syntax_Syntax.sigrng in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5165 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____5190 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let se1 = tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5242 =
             tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids in
           (match uu____5242 with
            | (ses1,projectors_ses) -> (ses1, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           let set_options1 t s =
             let uu____5281 = FStar_Options.set_options t s in
             match uu____5281 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_FailToProcessPragma,
                     "Failed to process pragma: use 'fstar --help' to see which options are available")
                   r
             | FStar_Getopt.Error s1 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_FailToProcessPragma,
                     (Prims.strcat "Failed to process pragma: " s1)) r in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options1 FStar_Options.Set o; ([se], []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let uu____5307 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____5307 FStar_Pervasives.ignore);
                 (match sopt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some s ->
                      set_options1 FStar_Options.Reset s);
                 ([se], [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____5315 = cps_and_elaborate env1 ne in
           (match uu____5315 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___77_5352 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___77_5352.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___77_5352.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___77_5352.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___77_5352.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___78_5354 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___78_5354.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___78_5354.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___78_5354.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___78_5354.FStar_Syntax_Syntax.sigattrs)
                        })] in
                ([], (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let ne1 = tc_eff_decl env1 ne in
           let se1 =
             let uu___79_5362 = se in
             {
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
               FStar_Syntax_Syntax.sigrng =
                 (uu___79_5362.FStar_Syntax_Syntax.sigrng);
               FStar_Syntax_Syntax.sigquals =
                 (uu___79_5362.FStar_Syntax_Syntax.sigquals);
               FStar_Syntax_Syntax.sigmeta =
                 (uu___79_5362.FStar_Syntax_Syntax.sigmeta);
               FStar_Syntax_Syntax.sigattrs =
                 (uu___79_5362.FStar_Syntax_Syntax.sigattrs)
             } in
           ([se1], [])
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env1
               sub1.FStar_Syntax_Syntax.target in
           let uu____5370 =
             let uu____5377 =
               FStar_TypeChecker_Env.lookup_effect_lid env1
                 sub1.FStar_Syntax_Syntax.source in
             monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____5377 in
           (match uu____5370 with
            | (a,wp_a_src) ->
                let uu____5392 =
                  let uu____5399 =
                    FStar_TypeChecker_Env.lookup_effect_lid env1
                      sub1.FStar_Syntax_Syntax.target in
                  monad_signature env1 sub1.FStar_Syntax_Syntax.target
                    uu____5399 in
                (match uu____5392 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____5415 =
                         let uu____5418 =
                           let uu____5419 =
                             let uu____5426 =
                               FStar_Syntax_Syntax.bv_to_name a in
                             (b, uu____5426) in
                           FStar_Syntax_Syntax.NT uu____5419 in
                         [uu____5418] in
                       FStar_Syntax_Subst.subst uu____5415 wp_b_tgt in
                     let expected_k =
                       let uu____5430 =
                         let uu____5437 = FStar_Syntax_Syntax.mk_binder a in
                         let uu____5438 =
                           let uu____5441 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [uu____5441] in
                         uu____5437 :: uu____5438 in
                       let uu____5442 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow uu____5430 uu____5442 in
                     let repr_type eff_name a1 wp =
                       let no_reify l =
                         let uu____5463 =
                           let uu____5468 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               l.FStar_Ident.str in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____5468) in
                         let uu____5469 =
                           FStar_TypeChecker_Env.get_range env1 in
                         FStar_Errors.raise_error uu____5463 uu____5469 in
                       let uu____5472 =
                         FStar_TypeChecker_Env.effect_decl_opt env1 eff_name in
                       match uu____5472 with
                       | FStar_Pervasives_Native.None  -> no_reify eff_name
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env1 ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____5504 =
                             let uu____5505 =
                               FStar_All.pipe_right qualifiers
                                 (FStar_List.contains
                                    FStar_Syntax_Syntax.Reifiable) in
                             Prims.op_Negation uu____5505 in
                           if uu____5504
                           then no_reify eff_name
                           else
                             (let uu____5511 =
                                FStar_TypeChecker_Env.get_range env1 in
                              let uu____5512 =
                                let uu____5515 =
                                  let uu____5516 =
                                    let uu____5531 =
                                      let uu____5534 =
                                        FStar_Syntax_Syntax.as_arg a1 in
                                      let uu____5535 =
                                        let uu____5538 =
                                          FStar_Syntax_Syntax.as_arg wp in
                                        [uu____5538] in
                                      uu____5534 :: uu____5535 in
                                    (repr, uu____5531) in
                                  FStar_Syntax_Syntax.Tm_app uu____5516 in
                                FStar_Syntax_Syntax.mk uu____5515 in
                              uu____5512 FStar_Pervasives_Native.None
                                uu____5511) in
                     let uu____5544 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some
                          (uu____5572,lift_wp)) ->
                           let uu____5596 =
                             check_and_gen env1 lift_wp expected_k in
                           (lift, uu____5596)
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           ((let uu____5622 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "ED") in
                             if uu____5622
                             then
                               let uu____5623 =
                                 FStar_Syntax_Print.term_to_string lift in
                               FStar_Util.print1 "Lift for free : %s\n"
                                 uu____5623
                             else ());
                            (let dmff_env =
                               FStar_TypeChecker_DMFF.empty env1
                                 (FStar_TypeChecker_TcTerm.tc_constant env1
                                    FStar_Range.dummyRange) in
                             let uu____5626 =
                               FStar_TypeChecker_TcTerm.tc_term env1 lift in
                             match uu____5626 with
                             | (lift1,comp,uu____5641) ->
                                 let uu____5642 =
                                   FStar_TypeChecker_DMFF.star_expr dmff_env
                                     lift1 in
                                 (match uu____5642 with
                                  | (uu____5655,lift_wp,lift_elab) ->
                                      let uu____5658 =
                                        recheck_debug "lift-wp" env1 lift_wp in
                                      let uu____5659 =
                                        recheck_debug "lift-elab" env1
                                          lift_elab in
                                      ((FStar_Pervasives_Native.Some
                                          ([], lift_elab)), ([], lift_wp))))) in
                     (match uu____5544 with
                      | (lift,lift_wp) ->
                          let lax1 = env1.FStar_TypeChecker_Env.lax in
                          let env2 =
                            let uu___80_5700 = env1 in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___80_5700.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___80_5700.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___80_5700.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___80_5700.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___80_5700.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___80_5700.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___80_5700.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___80_5700.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___80_5700.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___80_5700.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___80_5700.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___80_5700.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___80_5700.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___80_5700.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___80_5700.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___80_5700.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___80_5700.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___80_5700.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___80_5700.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___80_5700.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___80_5700.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___80_5700.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___80_5700.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___80_5700.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___80_5700.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___80_5700.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___80_5700.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___80_5700.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___80_5700.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___80_5700.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___80_5700.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___80_5700.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___80_5700.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___80_5700.FStar_TypeChecker_Env.dep_graph)
                            } in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uu____5706,lift1)
                                ->
                                let uu____5718 =
                                  let uu____5725 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env2 sub1.FStar_Syntax_Syntax.source in
                                  monad_signature env2
                                    sub1.FStar_Syntax_Syntax.source
                                    uu____5725 in
                                (match uu____5718 with
                                 | (a1,wp_a_src1) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv
                                         FStar_Pervasives_Native.None
                                         wp_a_src1 in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a1 in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a in
                                     let repr_f =
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.source
                                         a_typ wp_a_typ in
                                     let repr_result =
                                       let lift_wp1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env2
                                           (FStar_Pervasives_Native.snd
                                              lift_wp) in
                                       let lift_wp_a =
                                         let uu____5749 =
                                           FStar_TypeChecker_Env.get_range
                                             env2 in
                                         let uu____5750 =
                                           let uu____5753 =
                                             let uu____5754 =
                                               let uu____5769 =
                                                 let uu____5772 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     a_typ in
                                                 let uu____5773 =
                                                   let uu____5776 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp_a_typ in
                                                   [uu____5776] in
                                                 uu____5772 :: uu____5773 in
                                               (lift_wp1, uu____5769) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5754 in
                                           FStar_Syntax_Syntax.mk uu____5753 in
                                         uu____5750
                                           FStar_Pervasives_Native.None
                                           uu____5749 in
                                       repr_type
                                         sub1.FStar_Syntax_Syntax.target
                                         a_typ lift_wp_a in
                                     let expected_k1 =
                                       let uu____5785 =
                                         let uu____5792 =
                                           FStar_Syntax_Syntax.mk_binder a1 in
                                         let uu____5793 =
                                           let uu____5796 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let uu____5797 =
                                             let uu____5800 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [uu____5800] in
                                           uu____5796 :: uu____5797 in
                                         uu____5792 :: uu____5793 in
                                       let uu____5801 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow uu____5785
                                         uu____5801 in
                                     let uu____5804 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env2 expected_k1 in
                                     (match uu____5804 with
                                      | (expected_k2,uu____5814,uu____5815)
                                          ->
                                          let lift2 =
                                            check_and_gen env2 lift1
                                              expected_k2 in
                                          FStar_Pervasives_Native.Some lift2)) in
                          let sub2 =
                            let uu___81_5818 = sub1 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___81_5818.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___81_5818.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp =
                                (FStar_Pervasives_Native.Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift1
                            } in
                          let se1 =
                            let uu___82_5820 = se in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___82_5820.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___82_5820.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___82_5820.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___82_5820.FStar_Syntax_Syntax.sigattrs)
                            } in
                          ([se1], []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let env0 = env1 in
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let uu____5839 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____5839 with
            | (tps1,c1) ->
                let uu____5854 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1 in
                (match uu____5854 with
                 | (tps2,env3,us) ->
                     let uu____5872 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1 in
                     (match uu____5872 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2 in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2 in
                            let uu____5893 =
                              let uu____5894 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  FStar_Pervasives_Native.None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____5894 in
                            match uu____5893 with
                            | (uvs1,t) ->
                                let uu____5909 =
                                  let uu____5922 =
                                    let uu____5927 =
                                      let uu____5928 =
                                        FStar_Syntax_Subst.compress t in
                                      uu____5928.FStar_Syntax_Syntax.n in
                                    (tps3, uu____5927) in
                                  match uu____5922 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____5943,c4)) -> ([], c4)
                                  | (uu____5983,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____6010 ->
                                      failwith "Impossible (t is an arrow)" in
                                (match uu____5909 with
                                 | (tps4,c4) ->
                                     (if
                                        (FStar_List.length uvs1) <>
                                          (Prims.parse_int "1")
                                      then
                                        (let uu____6054 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t in
                                         match uu____6054 with
                                         | (uu____6059,t1) ->
                                             let uu____6061 =
                                               let uu____6066 =
                                                 let uu____6067 =
                                                   FStar_Syntax_Print.lid_to_string
                                                     lid in
                                                 let uu____6068 =
                                                   FStar_All.pipe_right
                                                     (FStar_List.length uvs1)
                                                     FStar_Util.string_of_int in
                                                 let uu____6069 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1 in
                                                 FStar_Util.format3
                                                   "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                   uu____6067 uu____6068
                                                   uu____6069 in
                                               (FStar_Errors.Fatal_TooManyUniverse,
                                                 uu____6066) in
                                             FStar_Errors.raise_error
                                               uu____6061 r)
                                      else ();
                                      (let se1 =
                                         let uu___83_6072 = se in
                                         {
                                           FStar_Syntax_Syntax.sigel =
                                             (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                (lid, uvs1, tps4, c4, flags1));
                                           FStar_Syntax_Syntax.sigrng =
                                             (uu___83_6072.FStar_Syntax_Syntax.sigrng);
                                           FStar_Syntax_Syntax.sigquals =
                                             (uu___83_6072.FStar_Syntax_Syntax.sigquals);
                                           FStar_Syntax_Syntax.sigmeta =
                                             (uu___83_6072.FStar_Syntax_Syntax.sigmeta);
                                           FStar_Syntax_Syntax.sigattrs =
                                             (uu___83_6072.FStar_Syntax_Syntax.sigattrs)
                                         } in
                                       ([se1], [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____6089,uu____6090,uu____6091) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___55_6095  ->
                   match uu___55_6095 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____6096 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_let (uu____6101,uu____6102) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___55_6110  ->
                   match uu___55_6110 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____6111 -> false))
           -> ([], [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           ((let uu____6121 = FStar_TypeChecker_Env.lid_exists env2 lid in
             if uu____6121
             then
               let uu____6122 =
                 let uu____6127 =
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     (FStar_Ident.text_of_lid lid) in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____6127) in
               FStar_Errors.raise_error uu____6122 r
             else ());
            (let uu____6129 =
               if uvs = []
               then
                 let uu____6130 =
                   let uu____6131 = FStar_Syntax_Util.type_u () in
                   FStar_Pervasives_Native.fst uu____6131 in
                 check_and_gen env2 t uu____6130
               else
                 (let uu____6137 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____6137 with
                  | (uvs1,t1) ->
                      let t2 =
                        let uu____6145 =
                          let uu____6146 = FStar_Syntax_Util.type_u () in
                          FStar_Pervasives_Native.fst uu____6146 in
                        tc_check_trivial_guard env2 t1 uu____6145 in
                      let t3 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.NoFullNorm;
                          FStar_TypeChecker_Normalize.Beta] env2 t2 in
                      let uu____6152 =
                        FStar_Syntax_Subst.close_univ_vars uvs1 t3 in
                      (uvs1, uu____6152)) in
             match uu____6129 with
             | (uvs1,t1) ->
                 let se1 =
                   let uu___84_6168 = se in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs1, t1));
                     FStar_Syntax_Syntax.sigrng =
                       (uu___84_6168.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___84_6168.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___84_6168.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs =
                       (uu___84_6168.FStar_Syntax_Syntax.sigattrs)
                   } in
                 ([se1], [])))
       | FStar_Syntax_Syntax.Sig_assume (lid,us,phi) ->
           let uu____6178 = FStar_Syntax_Subst.open_univ_vars us phi in
           (match uu____6178 with
            | (uu____6191,phi1) ->
                let se1 =
                  tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r in
                ([se1], []))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let env3 =
             FStar_TypeChecker_Env.set_expected_typ env2
               FStar_Syntax_Syntax.t_unit in
           let uu____6201 = FStar_TypeChecker_TcTerm.tc_term env3 e in
           (match uu____6201 with
            | (e1,c,g1) ->
                let uu____6219 =
                  let uu____6226 =
                    let uu____6229 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r in
                    FStar_Pervasives_Native.Some uu____6229 in
                  let uu____6230 =
                    let uu____6235 = FStar_Syntax_Syntax.lcomp_comp c in
                    (e1, uu____6235) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____6226 uu____6230 in
                (match uu____6219 with
                 | (e2,uu____6245,g) ->
                     ((let uu____6248 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____6248);
                      (let se1 =
                         let uu___85_6250 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___85_6250.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___85_6250.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___85_6250.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___85_6250.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ([se1], [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r in
           let check_quals_eq l qopt q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some q
             | FStar_Pervasives_Native.Some q' ->
                 let uu____6301 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____6301
                 then FStar_Pervasives_Native.Some q
                 else
                   (let uu____6309 =
                      let uu____6314 =
                        let uu____6315 = FStar_Syntax_Print.lid_to_string l in
                        let uu____6316 = FStar_Syntax_Print.quals_to_string q in
                        let uu____6317 =
                          FStar_Syntax_Print.quals_to_string q' in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____6315 uu____6316 uu____6317 in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____6314) in
                    FStar_Errors.raise_error uu____6309 r) in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ in
               let def_bs =
                 let uu____6343 =
                   let uu____6344 = FStar_Syntax_Subst.compress def in
                   uu____6344.FStar_Syntax_Syntax.n in
                 match uu____6343 with
                 | FStar_Syntax_Syntax.Tm_abs (binders,uu____6354,uu____6355)
                     -> binders
                 | uu____6376 -> [] in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____6386;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____6464) -> val_bs1
                     | (uu____6487,[]) -> val_bs1
                     | ((body_bv,uu____6511)::bt,(val_bv,aqual)::vt) ->
                         let uu____6548 = rename_binders1 bt vt in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____6564) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___86_6566 = val_bv in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___87_6569 =
                                        val_bv.FStar_Syntax_Syntax.ppname in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___87_6569.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___86_6566.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___86_6566.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____6548 in
                   let uu____6570 =
                     let uu____6573 =
                       let uu____6574 =
                         let uu____6587 = rename_binders1 def_bs val_bs in
                         (uu____6587, c) in
                       FStar_Syntax_Syntax.Tm_arrow uu____6574 in
                     FStar_Syntax_Syntax.mk uu____6573 in
                   uu____6570 FStar_Pervasives_Native.None r1
               | uu____6605 -> typ1 in
             let uu___88_6606 = lb in
             let uu____6607 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___88_6606.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___88_6606.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____6607;
               FStar_Syntax_Syntax.lbeff =
                 (uu___88_6606.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___88_6606.FStar_Syntax_Syntax.lbdef)
             } in
           let uu____6610 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____6661  ->
                     fun lb  ->
                       match uu____6661 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____6703 =
                             let uu____6714 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____6714 with
                             | FStar_Pervasives_Native.None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | FStar_Pervasives_Native.Some
                                 ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
                                 let def =
                                   match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  ->
                                       lb.FStar_Syntax_Syntax.lbdef
                                   | uu____6799 ->
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_ascribed
                                            ((lb.FStar_Syntax_Syntax.lbdef),
                                              ((FStar_Util.Inl
                                                  (lb.FStar_Syntax_Syntax.lbtyp)),
                                                FStar_Pervasives_Native.None),
                                              FStar_Pervasives_Native.None))
                                         FStar_Pervasives_Native.None
                                         (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos in
                                 (if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                        "Inline universes are incoherent with annotation from val declaration")
                                      r
                                  else ();
                                  (let uu____6842 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def) in
                                   (false, uu____6842, quals_opt1))) in
                           (match uu____6703 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals)))) in
           (match uu____6610 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____6936 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___56_6940  ->
                                match uu___56_6940 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____6941 -> false)) in
                      if uu____6936
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs'1 = FStar_List.rev lbs' in
                let e =
                  let uu____6951 =
                    let uu____6954 =
                      let uu____6955 =
                        let uu____6968 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____6968) in
                      FStar_Syntax_Syntax.Tm_let uu____6955 in
                    FStar_Syntax_Syntax.mk uu____6954 in
                  uu____6951 FStar_Pervasives_Native.None r in
                let uu____6986 =
                  let uu____6997 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___89_7006 = env2 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___89_7006.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___89_7006.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___89_7006.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___89_7006.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___89_7006.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___89_7006.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___89_7006.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___89_7006.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___89_7006.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___89_7006.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___89_7006.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___89_7006.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___89_7006.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___89_7006.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___89_7006.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___89_7006.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___89_7006.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___89_7006.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___89_7006.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___89_7006.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___89_7006.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___89_7006.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___89_7006.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___89_7006.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___89_7006.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___89_7006.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___89_7006.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___89_7006.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___89_7006.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___89_7006.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___89_7006.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___89_7006.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___89_7006.FStar_TypeChecker_Env.dep_graph)
                       }) e in
                  match uu____6997 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.pos = uu____7019;
                       FStar_Syntax_Syntax.vars = uu____7020;_},uu____7021,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let lbs2 =
                        let uu____7050 =
                          FStar_All.pipe_right
                            (FStar_Pervasives_Native.snd lbs1)
                            (FStar_List.map rename_parameters) in
                        ((FStar_Pervasives_Native.fst lbs1), uu____7050) in
                      let quals1 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____7068,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____7073 -> quals in
                      ((let uu___90_7081 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_let (lbs2, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___90_7081.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals = quals1;
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___90_7081.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___90_7081.FStar_Syntax_Syntax.sigattrs)
                        }), lbs2)
                  | uu____7090 ->
                      failwith
                        "impossible (typechecking should preserve Tm_let)" in
                (match uu____6986 with
                 | (se1,lbs1) ->
                     (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
                        (FStar_List.iter
                           (fun lb  ->
                              let fv =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              FStar_TypeChecker_Env.insert_fv_info env2 fv
                                lb.FStar_Syntax_Syntax.lbtyp));
                      (let uu____7139 = log env2 in
                       if uu____7139
                       then
                         let uu____7140 =
                           let uu____7141 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____7156 =
                                         let uu____7165 =
                                           let uu____7166 =
                                             let uu____7169 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             uu____7169.FStar_Syntax_Syntax.fv_name in
                                           uu____7166.FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____7165 in
                                       match uu____7156 with
                                       | FStar_Pervasives_Native.None  ->
                                           true
                                       | uu____7176 -> false in
                                     if should_log
                                     then
                                       let uu____7185 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let uu____7186 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____7185 uu____7186
                                     else "")) in
                           FStar_All.pipe_right uu____7141
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" uu____7140
                       else ());
                      (let uu____7191 = tactic_decls env2 se1 lbs1 lids in
                       match uu____7191 with
                       | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                           ((let uu____7213 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "NativeTactics") in
                             if uu____7213
                             then
                               let uu____7214 =
                                 FStar_Syntax_Print.sigelt_to_string se_assm in
                               let uu____7215 =
                                 FStar_Syntax_Print.sigelt_to_string se_refl in
                               FStar_Util.print2
                                 "Native tactic declarations: \n%s\n%s\n"
                                 uu____7214 uu____7215
                             else ());
                            ([se_assm; se_refl], []))
                       | FStar_Pervasives_Native.None  -> ([se1], []))))))
let for_export:
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___57_7266  ->
                match uu___57_7266 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____7267 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,uu____7273) ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____7279 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma uu____7288 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7293 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_datacon uu____7318 ->
          failwith "Impossible (Already handled)"
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7342) ->
          let uu____7351 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7351
          then
            let for_export_bundle se1 uu____7382 =
              match uu____7382 with
              | (out,hidden1) ->
                  (match se1.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____7421,uu____7422) ->
                       let dec =
                         let uu___91_7432 = se1 in
                         let uu____7433 =
                           let uu____7434 =
                             let uu____7441 =
                               let uu____7444 =
                                 FStar_Syntax_Syntax.mk_Total t in
                               FStar_Syntax_Util.arrow bs uu____7444 in
                             (l, us, uu____7441) in
                           FStar_Syntax_Syntax.Sig_declare_typ uu____7434 in
                         {
                           FStar_Syntax_Syntax.sigel = uu____7433;
                           FStar_Syntax_Syntax.sigrng =
                             (uu___91_7432.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New ::
                             (se1.FStar_Syntax_Syntax.sigquals));
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___91_7432.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___91_7432.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____7456,uu____7457,uu____7458) ->
                       let dec =
                         let uu___92_7464 = se1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___92_7464.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             [FStar_Syntax_Syntax.Assumption];
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___92_7464.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___92_7464.FStar_Syntax_Syntax.sigattrs)
                         } in
                       ((dec :: out), (l :: hidden1))
                   | uu____7469 -> (out, hidden1)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume (uu____7491,uu____7492,uu____7493) ->
          let uu____7494 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7494 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
          let uu____7515 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____7515
          then
            ([(let uu___93_7531 = se in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___93_7531.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___93_7531.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___93_7531.FStar_Syntax_Syntax.sigattrs)
               })], (l :: hidden))
          else
            (let uu____7533 =
               FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___58_7537  ->
                       match uu___58_7537 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | FStar_Syntax_Syntax.Projector uu____7538 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____7543 -> true
                       | uu____7544 -> false)) in
             if uu____7533 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____7562 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect uu____7567 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7572 ->
          ([se], hidden)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____7577 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____7582 -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____7600) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____7617 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____7617
          then ([], hidden)
          else
            (let dec =
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                        (lb.FStar_Syntax_Syntax.lbunivs),
                        (lb.FStar_Syntax_Syntax.lbtyp)));
                 FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid lid);
                 FStar_Syntax_Syntax.sigquals =
                   [FStar_Syntax_Syntax.Assumption];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               } in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____7648 = is_abstract se.FStar_Syntax_Syntax.sigquals in
          if uu____7648
          then
            let uu____7657 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___94_7670 = se in
                      let uu____7671 =
                        let uu____7672 =
                          let uu____7679 =
                            let uu____7680 =
                              let uu____7683 =
                                FStar_Util.right
                                  lb.FStar_Syntax_Syntax.lbname in
                              uu____7683.FStar_Syntax_Syntax.fv_name in
                            uu____7680.FStar_Syntax_Syntax.v in
                          (uu____7679, (lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)) in
                        FStar_Syntax_Syntax.Sig_declare_typ uu____7672 in
                      {
                        FStar_Syntax_Syntax.sigel = uu____7671;
                        FStar_Syntax_Syntax.sigrng =
                          (uu___94_7670.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (FStar_Syntax_Syntax.Assumption ::
                          (se.FStar_Syntax_Syntax.sigquals));
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___94_7670.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___94_7670.FStar_Syntax_Syntax.sigattrs)
                      })) in
            (uu____7657, hidden)
          else ([se], hidden)
let add_sigelt_to_env:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____7703 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_datacon uu____7720 ->
          failwith "add_sigelt_to_env: Impossible, bare data constructor"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          uu____7735) ->
          let env1 =
            let uu____7739 = FStar_Options.using_facts_from () in
            FStar_TypeChecker_Env.set_proof_ns uu____7739 env in
          ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           env1)
      | FStar_Syntax_Syntax.Sig_pragma uu____7741 -> env
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____7742 -> env
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let env1 = FStar_TypeChecker_Env.push_sigelt env se in
          FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
            (FStar_List.fold_left
               (fun env2  ->
                  fun a  ->
                    let uu____7752 =
                      FStar_Syntax_Util.action_as_lb
                        ne.FStar_Syntax_Syntax.mname a in
                    FStar_TypeChecker_Env.push_sigelt env2 uu____7752) env1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          (uu____7753,uu____7754,uu____7755) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___59_7759  ->
                  match uu___59_7759 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7760 -> false))
          -> env
      | FStar_Syntax_Syntax.Sig_let (uu____7761,uu____7762) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___59_7770  ->
                  match uu___59_7770 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____7771 -> false))
          -> env
      | uu____7772 -> FStar_TypeChecker_Env.push_sigelt env se
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                               Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____7832 se =
        match uu____7832 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____7885 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
              if uu____7885
              then
                let uu____7886 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7886
              else ());
             (let uu____7888 = tc_decl env1 se in
              match uu____7888 with
              | (ses',ses_elaborated) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____7938 =
                               FStar_TypeChecker_Env.debug env1
                                 (FStar_Options.Other "UF") in
                             if uu____7938
                             then
                               let uu____7939 =
                                 FStar_Syntax_Print.sigelt_to_string se1 in
                               FStar_Util.print1 "About to elim vars from %s"
                                 uu____7939
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            FStar_TypeChecker_Normalize.elim_uvars env1 se1)) in
                  (FStar_TypeChecker_Env.promote_id_info env1
                     (fun t  ->
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                          FStar_TypeChecker_Normalize.CheckNoUvars;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.NoDeltaSteps;
                          FStar_TypeChecker_Normalize.CompressUvars;
                          FStar_TypeChecker_Normalize.Exclude
                            FStar_TypeChecker_Normalize.Zeta;
                          FStar_TypeChecker_Normalize.Exclude
                            FStar_TypeChecker_Normalize.Iota;
                          FStar_TypeChecker_Normalize.NoFullNorm] env1 t);
                   (let env2 =
                      FStar_All.pipe_right ses'1
                        (FStar_List.fold_left
                           (fun env2  ->
                              fun se1  -> add_sigelt_to_env env2 se1) env1) in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____7962 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env2)
                            (FStar_Options.Other "LogTypes")) in
                     if uu____7962
                     then
                       let uu____7963 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____7969 =
                                  let uu____7970 =
                                    FStar_Syntax_Print.sigelt_to_string se1 in
                                  Prims.strcat uu____7970 "\n" in
                                Prims.strcat s uu____7969) "" ses'1 in
                       FStar_Util.print1 "Checked: %s\n" uu____7963
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env2 se1) ses'1;
                    (let uu____7975 =
                       let accum_exports_hidden uu____8005 se1 =
                         match uu____8005 with
                         | (exports1,hidden1) ->
                             let uu____8033 = for_export hidden1 se1 in
                             (match uu____8033 with
                              | (se_exported,hidden2) ->
                                  ((FStar_List.rev_append se_exported
                                      exports1), hidden2)) in
                       FStar_List.fold_left accum_exports_hidden
                         (exports, hidden) ses'1 in
                     match uu____7975 with
                     | (exports1,hidden1) ->
                         let ses'2 =
                           FStar_List.map
                             (fun s  ->
                                let uu___95_8112 = s in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___95_8112.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___95_8112.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___95_8112.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___95_8112.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (se.FStar_Syntax_Syntax.sigattrs)
                                }) ses'1 in
                         (((FStar_List.rev_append ses'2 ses1), exports1,
                            env2, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____8190 = acc in
        match uu____8190 with
        | (uu____8225,uu____8226,env1,uu____8228) ->
            let uu____8241 =
              FStar_Util.record_time
                (fun uu____8287  -> process_one_decl acc se) in
            (match uu____8241 with
             | (r,ms_elapsed) ->
                 ((let uu____8351 =
                     FStar_TypeChecker_Env.debug env1
                       (FStar_Options.Other "TCDeclTime") in
                   if uu____8351
                   then
                     let uu____8352 =
                       FStar_Syntax_Print.sigelt_to_string_short se in
                     let uu____8353 = FStar_Util.string_of_int ms_elapsed in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____8352 uu____8353
                   else ());
                  r)) in
      let uu____8355 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses in
      match uu____8355 with
      | (ses1,exports,env1,uu____8403) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let tc_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun modul  ->
      fun push_before_typechecking  ->
        let verify =
          FStar_Options.should_verify
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
        let action = if verify then "Verifying" else "Lax-checking" in
        let label1 =
          if modul.FStar_Syntax_Syntax.is_interface
          then "interface"
          else "implementation" in
        (let uu____8443 = FStar_Options.debug_any () in
         if uu____8443
         then
           FStar_Util.print3 "%s %s of %s\n" action label1
             (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         else ());
        (let name =
           FStar_Util.format2 "%s %s"
             (if modul.FStar_Syntax_Syntax.is_interface
              then "interface"
              else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
         let msg = Prims.strcat "Internals for " name in
         let env1 =
           let uu___96_8449 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___96_8449.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___96_8449.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___96_8449.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___96_8449.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___96_8449.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___96_8449.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___96_8449.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___96_8449.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___96_8449.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___96_8449.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___96_8449.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___96_8449.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___96_8449.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___96_8449.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___96_8449.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___96_8449.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (modul.FStar_Syntax_Syntax.is_interface);
             FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
             FStar_TypeChecker_Env.lax =
               (uu___96_8449.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___96_8449.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___96_8449.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___96_8449.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___96_8449.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___96_8449.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___96_8449.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___96_8449.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___96_8449.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___96_8449.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___96_8449.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___96_8449.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___96_8449.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___96_8449.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___96_8449.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___96_8449.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.dep_graph =
               (uu___96_8449.FStar_TypeChecker_Env.dep_graph)
           } in
         if push_before_typechecking
         then
           (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg
         else ();
         (let env2 =
            FStar_TypeChecker_Env.set_current_module env1
              modul.FStar_Syntax_Syntax.name in
          let uu____8453 =
            tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
          match uu____8453 with
          | (ses,exports,env3) ->
              ((let uu___97_8486 = modul in
                {
                  FStar_Syntax_Syntax.name =
                    (uu___97_8486.FStar_Syntax_Syntax.name);
                  FStar_Syntax_Syntax.declarations = ses;
                  FStar_Syntax_Syntax.exports =
                    (uu___97_8486.FStar_Syntax_Syntax.exports);
                  FStar_Syntax_Syntax.is_interface =
                    (uu___97_8486.FStar_Syntax_Syntax.is_interface)
                }), exports, env3)))
let tc_more_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.sigelt Prims.list,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____8508 = tc_decls env decls in
        match uu____8508 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___98_8539 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___98_8539.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___98_8539.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___98_8539.FStar_Syntax_Syntax.is_interface)
              } in
            (modul1, exports, env1)
let check_exports:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___99_8556 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___99_8556.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___99_8556.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___99_8556.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___99_8556.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___99_8556.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___99_8556.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___99_8556.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___99_8556.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___99_8556.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___99_8556.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___99_8556.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___99_8556.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___99_8556.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___99_8556.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___99_8556.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___99_8556.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___99_8556.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.failhard =
              (uu___99_8556.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___99_8556.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.tc_term =
              (uu___99_8556.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___99_8556.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___99_8556.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___99_8556.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___99_8556.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___99_8556.FStar_TypeChecker_Env.qname_and_index);
            FStar_TypeChecker_Env.proof_ns =
              (uu___99_8556.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth =
              (uu___99_8556.FStar_TypeChecker_Env.synth);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___99_8556.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___99_8556.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___99_8556.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___99_8556.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.dep_graph =
              (uu___99_8556.FStar_TypeChecker_Env.dep_graph)
          } in
        let check_term1 lid univs1 t =
          let uu____8567 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          match uu____8567 with
          | (univs2,t1) ->
              ((let uu____8575 =
                  let uu____8576 =
                    let uu____8579 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____8579 in
                  FStar_All.pipe_left uu____8576
                    (FStar_Options.Other "Exports") in
                if uu____8575
                then
                  let uu____8580 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____8581 =
                    let uu____8582 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____8582
                      (FStar_String.concat ", ") in
                  let uu____8591 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____8580 uu____8581 uu____8591
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2 in
                let uu____8594 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____8594 FStar_Pervasives.ignore)) in
        let check_term2 lid univs1 t =
          (let uu____8618 =
             let uu____8619 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let uu____8620 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____8619 uu____8620 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8618);
          check_term1 lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8627) ->
              let uu____8636 =
                let uu____8637 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8637 in
              if uu____8636
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____8647,uu____8648) ->
              let t =
                let uu____8660 =
                  let uu____8663 =
                    let uu____8664 =
                      let uu____8677 = FStar_Syntax_Syntax.mk_Total typ in
                      (binders, uu____8677) in
                    FStar_Syntax_Syntax.Tm_arrow uu____8664 in
                  FStar_Syntax_Syntax.mk uu____8663 in
                uu____8660 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng in
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____8684,uu____8685,uu____8686) ->
              check_term2 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____8694 =
                let uu____8695 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8695 in
              if uu____8694 then check_term2 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____8699,lbs),uu____8701) ->
              let uu____8716 =
                let uu____8717 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8717 in
              if uu____8716
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term2
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags1) ->
              let uu____8736 =
                let uu____8737 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____8737 in
              if uu____8736
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng in
                check_term2 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____8744 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____8745 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____8752 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____8753 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____8754 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____8755 -> () in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
let finish_partial_modul:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.modul ->
        FStar_Syntax_Syntax.sigelts ->
          (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple2
  =
  fun must_check_exports  ->
    fun env  ->
      fun modul  ->
        fun exports  ->
          let modul1 =
            let uu___100_8774 = modul in
            {
              FStar_Syntax_Syntax.name =
                (uu___100_8774.FStar_Syntax_Syntax.name);
              FStar_Syntax_Syntax.declarations =
                (uu___100_8774.FStar_Syntax_Syntax.declarations);
              FStar_Syntax_Syntax.exports = exports;
              FStar_Syntax_Syntax.is_interface =
                (modul.FStar_Syntax_Syntax.is_interface)
            } in
          let env1 = FStar_TypeChecker_Env.finish_module env modul1 in
          (let uu____8777 =
             (let uu____8780 = FStar_Options.lax () in
              Prims.op_Negation uu____8780) && must_check_exports in
           if uu____8777 then check_exports env1 modul1 exports else ());
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
            (Prims.strcat "Ending modul "
               (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
            env1 modul1;
          (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
            ();
          (let uu____8786 =
             let uu____8787 = FStar_Options.interactive () in
             Prims.op_Negation uu____8787 in
           if uu____8786
           then
             let uu____8788 = FStar_Options.restore_cmd_line_options true in
             FStar_All.pipe_right uu____8788 FStar_Pervasives.ignore
           else ());
          (modul1, env1)
let push_sigelt_or_native_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let se' =
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
            let uu____8807 = tactic_decls env se lbs lids in
            (match uu____8807 with
             | FStar_Pervasives_Native.Some (se_assm,se_refl) ->
                 ((let uu____8823 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "NativeTactics") in
                   if uu____8823
                   then
                     let uu____8824 =
                       FStar_Syntax_Print.sigelt_to_string se_assm in
                     let uu____8825 =
                       FStar_Syntax_Print.sigelt_to_string se_refl in
                     FStar_Util.print2
                       "Native tactic declarations from checked module: \n%s\n%s\n"
                       uu____8824 uu____8825
                   else ());
                  [se_assm; se_refl])
             | FStar_Pervasives_Native.None  -> [se])
        | uu____8831 -> [se] in
      FStar_List.fold_left
        (fun env1  -> fun se1  -> FStar_TypeChecker_Env.push_sigelt env1 se1)
        env se'
let load_checked_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun modul  ->
      (let uu____8843 = FStar_Options.debug_any () in
       if uu____8843
       then
         let uu____8844 =
           FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Loading checked %s: %s\n"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "i'face"
            else "module") uu____8844
       else ());
      (let env1 =
         FStar_TypeChecker_Env.set_current_module env
           modul.FStar_Syntax_Syntax.name in
       (let uu____8849 =
          let uu____8850 =
            FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
          Prims.strcat "Internals for " uu____8850 in
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
          uu____8849);
       (let uu____8852 =
          FStar_TypeChecker_Env.debug env1
            (FStar_Options.Other "NativeTactics") in
        if uu____8852
        then
          (FStar_Util.print "Environment before loading checked module:\n" [];
           FStar_TypeChecker_Env.print_gamma env1)
        else ());
       (let env2 =
          FStar_List.fold_left
            (fun env2  ->
               fun se  ->
                 let env3 = push_sigelt_or_native_tactic env2 se in
                 let lids = FStar_Syntax_Util.lids_of_sigelt se in
                 FStar_All.pipe_right lids
                   (FStar_List.iter
                      (fun lid  ->
                         let uu____8873 =
                           FStar_TypeChecker_Env.try_lookup_lid env3 lid in
                         ()));
                 env3) env1 modul.FStar_Syntax_Syntax.declarations in
        (let uu____8895 =
           FStar_TypeChecker_Env.debug env2
             (FStar_Options.Other "NativeTactics") in
         if uu____8895
         then
           (FStar_Util.print "Environment after loading checked module:\n" [];
            FStar_TypeChecker_Env.print_gamma env2)
         else ());
        (let uu____8898 =
           finish_partial_modul false env2 modul
             modul.FStar_Syntax_Syntax.exports in
         FStar_Pervasives_Native.snd uu____8898)))
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun modul  ->
      let uu____8913 = tc_partial_modul env modul true in
      match uu____8913 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul true env1 modul1 non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      (let uu____8944 = FStar_Options.debug_any () in
       if uu____8944
       then
         let uu____8945 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____8945
       else ());
      (let env1 =
         let uu___101_8949 = env in
         let uu____8950 =
           let uu____8951 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
           Prims.op_Negation uu____8951 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___101_8949.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___101_8949.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___101_8949.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___101_8949.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___101_8949.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___101_8949.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___101_8949.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___101_8949.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___101_8949.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___101_8949.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___101_8949.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___101_8949.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___101_8949.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___101_8949.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___101_8949.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___101_8949.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___101_8949.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___101_8949.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____8950;
           FStar_TypeChecker_Env.lax_universes =
             (uu___101_8949.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___101_8949.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___101_8949.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___101_8949.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___101_8949.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___101_8949.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___101_8949.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___101_8949.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___101_8949.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___101_8949.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___101_8949.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___101_8949.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___101_8949.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___101_8949.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___101_8949.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___101_8949.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____8952 = tc_modul env1 m in
       match uu____8952 with
       | (m1,env2) ->
           ((let uu____8964 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____8964
             then
               let uu____8965 = FStar_Syntax_Print.modul_to_string m1 in
               FStar_Util.print1 "%s\n" uu____8965
             else ());
            (let uu____8968 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____8968
             then
               let normalize_toplevel_lets se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),ids) ->
                     let n1 =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.Eager_unfolding;
                         FStar_TypeChecker_Normalize.Reify;
                         FStar_TypeChecker_Normalize.Inlining;
                         FStar_TypeChecker_Normalize.Primops;
                         FStar_TypeChecker_Normalize.UnfoldUntil
                           FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
                     let update lb =
                       let uu____8999 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____8999 with
                       | (univnames1,e) ->
                           let uu___102_9006 = lb in
                           let uu____9007 =
                             let uu____9010 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1 in
                             n1 uu____9010 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___102_9006.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___102_9006.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___102_9006.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___102_9006.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____9007
                           } in
                     let uu___103_9011 = se in
                     let uu____9012 =
                       let uu____9013 =
                         let uu____9020 =
                           let uu____9027 = FStar_List.map update lbs in
                           (b, uu____9027) in
                         (uu____9020, ids) in
                       FStar_Syntax_Syntax.Sig_let uu____9013 in
                     {
                       FStar_Syntax_Syntax.sigel = uu____9012;
                       FStar_Syntax_Syntax.sigrng =
                         (uu___103_9011.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___103_9011.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___103_9011.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs =
                         (uu___103_9011.FStar_Syntax_Syntax.sigattrs)
                     }
                 | uu____9040 -> se in
               let normalized_module =
                 let uu___104_9042 = m1 in
                 let uu____9043 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___104_9042.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____9043;
                   FStar_Syntax_Syntax.exports =
                     (uu___104_9042.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___104_9042.FStar_Syntax_Syntax.is_interface)
                 } in
               let uu____9044 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" uu____9044
             else ());
            (m1, env2)))