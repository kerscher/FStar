open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mk_tactic_interpretation_0 :
  'r .
    Prims.bool ->
      'r FStar_Tactics_Basic.tac ->
        'r FStar_Syntax_Embeddings.embedder ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun embed_r  ->
        fun t_r  ->
          fun nm  ->
            fun psc  ->
              fun args  ->
                match args with
                | (embedded_state,uu____68)::[] ->
                    let uu____85 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state
                       in
                    FStar_Util.bind_opt uu____85
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps  in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____98  ->
                              let uu____99 = FStar_Ident.string_of_lid nm  in
                              let uu____100 =
                                FStar_Syntax_Print.args_to_string args  in
                              FStar_Util.print2 "Reached %s, args are: %s\n"
                                uu____99 uu____100);
                         (let res =
                            let uu____102 =
                              FStar_TypeChecker_Normalize.psc_range psc  in
                            let uu____103 = FStar_Tactics_Basic.run t ps1  in
                            let uu____106 =
                              FStar_Tactics_Embedding.embed_result embed_r
                                t_r
                               in
                            uu____106 uu____102 uu____103  in
                          FStar_Pervasives_Native.Some res))
                | uu____120 ->
                    failwith "Unexpected application of tactic primitive"
  
let mk_tactic_interpretation_1 :
  'a 'r .
    Prims.bool ->
      ('a -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'r FStar_Syntax_Embeddings.embedder ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun psc  ->
                fun args  ->
                  match args with
                  | (a,uu____197)::(embedded_state,uu____199)::[] ->
                      let uu____226 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____226
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____239  ->
                                let uu____240 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____241 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____240
                                  uu____241);
                           (let uu____242 = unembed_a a  in
                            FStar_Util.bind_opt uu____242
                              (fun a1  ->
                                 let res =
                                   let uu____254 = t a1  in
                                   FStar_Tactics_Basic.run uu____254 ps1  in
                                 let uu____257 =
                                   let uu____258 =
                                     FStar_TypeChecker_Normalize.psc_range
                                       psc
                                      in
                                   let uu____259 =
                                     FStar_Tactics_Embedding.embed_result
                                       embed_r t_r
                                      in
                                   uu____259 uu____258 res  in
                                 FStar_Pervasives_Native.Some uu____257)))
                  | uu____273 ->
                      let uu____274 =
                        let uu____275 = FStar_Ident.string_of_lid nm  in
                        let uu____276 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____275 uu____276
                         in
                      failwith uu____274
  
let mk_tactic_interpretation_1_env :
  'a 'r .
    Prims.bool ->
      (FStar_TypeChecker_Normalize.psc -> 'a -> 'r FStar_Tactics_Basic.tac)
        ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'r FStar_Syntax_Embeddings.embedder ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun psc  ->
                fun args  ->
                  match args with
                  | (a,uu____358)::(embedded_state,uu____360)::[] ->
                      let uu____387 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state
                         in
                      FStar_Util.bind_opt uu____387
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                              in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____400  ->
                                let uu____401 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____402 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state
                                   in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____401
                                  uu____402);
                           (let uu____403 = unembed_a a  in
                            FStar_Util.bind_opt uu____403
                              (fun a1  ->
                                 let res =
                                   let uu____415 = t psc a1  in
                                   FStar_Tactics_Basic.run uu____415 ps1  in
                                 let uu____418 =
                                   let uu____419 =
                                     FStar_TypeChecker_Normalize.psc_range
                                       psc
                                      in
                                   let uu____420 =
                                     FStar_Tactics_Embedding.embed_result
                                       embed_r t_r
                                      in
                                   uu____420 uu____419 res  in
                                 FStar_Pervasives_Native.Some uu____418)))
                  | uu____434 ->
                      let uu____435 =
                        let uu____436 = FStar_Ident.string_of_lid nm  in
                        let uu____437 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____436 uu____437
                         in
                      failwith uu____435
  
let mk_tactic_interpretation_2 :
  'a 'b 'r .
    Prims.bool ->
      ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'r FStar_Syntax_Embeddings.embedder ->
              FStar_Syntax_Syntax.typ ->
                FStar_Ident.lid ->
                  FStar_TypeChecker_Normalize.psc ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun embed_r  ->
            fun t_r  ->
              fun nm  ->
                fun psc  ->
                  fun args  ->
                    match args with
                    | (a,uu____534)::(b,uu____536)::(embedded_state,uu____538)::[]
                        ->
                        let uu____575 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state
                           in
                        FStar_Util.bind_opt uu____575
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps
                                in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____588  ->
                                  let uu____589 =
                                    FStar_Ident.string_of_lid nm  in
                                  let uu____590 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state
                                     in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____589
                                    uu____590);
                             (let uu____591 = unembed_a a  in
                              FStar_Util.bind_opt uu____591
                                (fun a1  ->
                                   let uu____599 = unembed_b b  in
                                   FStar_Util.bind_opt uu____599
                                     (fun b1  ->
                                        let res =
                                          let uu____611 = t a1 b1  in
                                          FStar_Tactics_Basic.run uu____611
                                            ps1
                                           in
                                        let uu____614 =
                                          let uu____615 =
                                            FStar_TypeChecker_Normalize.psc_range
                                              psc
                                             in
                                          let uu____616 =
                                            FStar_Tactics_Embedding.embed_result
                                              embed_r t_r
                                             in
                                          uu____616 uu____615 res  in
                                        FStar_Pervasives_Native.Some
                                          uu____614))))
                    | uu____630 ->
                        let uu____631 =
                          let uu____632 = FStar_Ident.string_of_lid nm  in
                          let uu____633 =
                            FStar_Syntax_Print.args_to_string args  in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____632 uu____633
                           in
                        failwith uu____631
  
let mk_tactic_interpretation_3 :
  'a 'b 'c 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'c FStar_Syntax_Embeddings.unembedder ->
              'r FStar_Syntax_Embeddings.embedder ->
                FStar_Syntax_Syntax.typ ->
                  FStar_Ident.lid ->
                    FStar_TypeChecker_Normalize.psc ->
                      FStar_Syntax_Syntax.args ->
                        FStar_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun unembed_c  ->
            fun embed_r  ->
              fun t_r  ->
                fun nm  ->
                  fun psc  ->
                    fun args  ->
                      match args with
                      | (a,uu____750)::(b,uu____752)::(c,uu____754)::
                          (embedded_state,uu____756)::[] ->
                          let uu____803 =
                            FStar_Tactics_Embedding.unembed_proofstate
                              embedded_state
                             in
                          FStar_Util.bind_opt uu____803
                            (fun ps  ->
                               let ps1 =
                                 FStar_Tactics_Types.set_ps_psc psc ps  in
                               FStar_Tactics_Basic.log ps1
                                 (fun uu____816  ->
                                    let uu____817 =
                                      FStar_Ident.string_of_lid nm  in
                                    let uu____818 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state
                                       in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n" uu____817
                                      uu____818);
                               (let uu____819 = unembed_a a  in
                                FStar_Util.bind_opt uu____819
                                  (fun a1  ->
                                     let uu____827 = unembed_b b  in
                                     FStar_Util.bind_opt uu____827
                                       (fun b1  ->
                                          let uu____835 = unembed_c c  in
                                          FStar_Util.bind_opt uu____835
                                            (fun c1  ->
                                               let res =
                                                 let uu____847 = t a1 b1 c1
                                                    in
                                                 FStar_Tactics_Basic.run
                                                   uu____847 ps1
                                                  in
                                               let uu____850 =
                                                 let uu____851 =
                                                   FStar_TypeChecker_Normalize.psc_range
                                                     psc
                                                    in
                                                 let uu____852 =
                                                   FStar_Tactics_Embedding.embed_result
                                                     embed_r t_r
                                                    in
                                                 uu____852 uu____851 res  in
                                               FStar_Pervasives_Native.Some
                                                 uu____850)))))
                      | uu____866 ->
                          let uu____867 =
                            let uu____868 = FStar_Ident.string_of_lid nm  in
                            let uu____869 =
                              FStar_Syntax_Print.args_to_string args  in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____868 uu____869
                             in
                          failwith uu____867
  
let mk_tactic_interpretation_5 :
  'a 'b 'c 'd 'e 'r .
    Prims.bool ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
        'a FStar_Syntax_Embeddings.unembedder ->
          'b FStar_Syntax_Embeddings.unembedder ->
            'c FStar_Syntax_Embeddings.unembedder ->
              'd FStar_Syntax_Embeddings.unembedder ->
                'e FStar_Syntax_Embeddings.unembedder ->
                  'r FStar_Syntax_Embeddings.embedder ->
                    FStar_Syntax_Syntax.typ ->
                      FStar_Ident.lid ->
                        FStar_TypeChecker_Normalize.psc ->
                          FStar_Syntax_Syntax.args ->
                            FStar_Syntax_Syntax.term
                              FStar_Pervasives_Native.option
  =
  fun reflect  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun unembed_c  ->
            fun unembed_d  ->
              fun unembed_e  ->
                fun embed_r  ->
                  fun t_r  ->
                    fun nm  ->
                      fun psc  ->
                        fun args  ->
                          match args with
                          | (a,uu____1026)::(b,uu____1028)::(c,uu____1030)::
                              (d,uu____1032)::(e,uu____1034)::(embedded_state,uu____1036)::[]
                              ->
                              let uu____1103 =
                                FStar_Tactics_Embedding.unembed_proofstate
                                  embedded_state
                                 in
                              FStar_Util.bind_opt uu____1103
                                (fun ps  ->
                                   let ps1 =
                                     FStar_Tactics_Types.set_ps_psc psc ps
                                      in
                                   FStar_Tactics_Basic.log ps1
                                     (fun uu____1116  ->
                                        let uu____1117 =
                                          FStar_Ident.string_of_lid nm  in
                                        let uu____1118 =
                                          FStar_Syntax_Print.term_to_string
                                            embedded_state
                                           in
                                        FStar_Util.print2
                                          "Reached %s, goals are: %s\n"
                                          uu____1117 uu____1118);
                                   (let uu____1119 = unembed_a a  in
                                    FStar_Util.bind_opt uu____1119
                                      (fun a1  ->
                                         let uu____1127 = unembed_b b  in
                                         FStar_Util.bind_opt uu____1127
                                           (fun b1  ->
                                              let uu____1135 = unembed_c c
                                                 in
                                              FStar_Util.bind_opt uu____1135
                                                (fun c1  ->
                                                   let uu____1143 =
                                                     unembed_d d  in
                                                   FStar_Util.bind_opt
                                                     uu____1143
                                                     (fun d1  ->
                                                        let uu____1151 =
                                                          unembed_e e  in
                                                        FStar_Util.bind_opt
                                                          uu____1151
                                                          (fun e1  ->
                                                             let res =
                                                               let uu____1163
                                                                 =
                                                                 t a1 b1 c1
                                                                   d1 e1
                                                                  in
                                                               FStar_Tactics_Basic.run
                                                                 uu____1163
                                                                 ps1
                                                                in
                                                             let uu____1166 =
                                                               let uu____1167
                                                                 =
                                                                 FStar_TypeChecker_Normalize.psc_range
                                                                   psc
                                                                  in
                                                               let uu____1168
                                                                 =
                                                                 FStar_Tactics_Embedding.embed_result
                                                                   embed_r
                                                                   t_r
                                                                  in
                                                               uu____1168
                                                                 uu____1167
                                                                 res
                                                                in
                                                             FStar_Pervasives_Native.Some
                                                               uu____1166)))))))
                          | uu____1182 ->
                              let uu____1183 =
                                let uu____1184 = FStar_Ident.string_of_lid nm
                                   in
                                let uu____1185 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format2
                                  "Unexpected application of tactic primitive %s %s"
                                  uu____1184 uu____1185
                                 in
                              failwith uu____1183
  
let (step_from_native_step :
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Normalize.primitive_step)
  =
  fun s  ->
    {
      FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
      FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
      FStar_TypeChecker_Normalize.auto_reflect =
        (FStar_Pervasives_Native.Some
           (s.FStar_Tactics_Native.arity - (Prims.parse_int "1")));
      FStar_TypeChecker_Normalize.strong_reduction_ok =
        (s.FStar_Tactics_Native.strong_reduction_ok);
      FStar_TypeChecker_Normalize.requires_binder_substitution = false;
      FStar_TypeChecker_Normalize.interpretation =
        (fun psc  -> fun args  -> s.FStar_Tactics_Native.tactic psc args)
    }
  
let rec (primitive_steps :
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
  fun uu____1271  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]
         in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation =
          (fun psc  -> fun args  -> interpretation nm1 psc args)
      }  in
    let native_tactics = FStar_Tactics_Native.list_all ()  in
    let native_tactics_steps =
      FStar_List.map step_from_native_step native_tactics  in
    let mktac0 r name f e_r tr =
      mk1 name (Prims.parse_int "1")
        (mk_tactic_interpretation_0 false f e_r tr)
       in
    let mktac1 a r name f u_a e_r tr =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 false f u_a e_r tr)
       in
    let mktac2 a b r name f u_a u_b e_r tr =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 false f u_a u_b e_r tr)
       in
    let mktac3 a b c r name f u_a u_b u_c e_r tr =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 false f u_a u_b u_c e_r tr)
       in
    let mktac5 a b c d e r name f u_a u_b u_c u_d u_e e_r tr =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 false f u_a u_b u_c u_d u_e e_r tr)
       in
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____1759)::[] ->
          let uu____1776 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1776
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1784 =
                 let uu____1785 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1786 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1785
                   uu____1786
                  in
               FStar_Pervasives_Native.Some uu____1784)
      | uu____1787 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____1791 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1791;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1804)::[] ->
          let uu____1821 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1821
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____1829 =
                 let uu____1830 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____1831 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Tactics_Embedding.embed_proofstate uu____1830
                   uu____1831
                  in
               FStar_Pervasives_Native.Some uu____1829)
      | uu____1832 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____1836 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"  in
      {
        FStar_TypeChecker_Normalize.name = uu____1836;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1853)::[] ->
          let uu____1870 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1870
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1883 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____1900)::(r,uu____1902)::[] ->
          let uu____1929 = FStar_Tactics_Embedding.unembed_proofstate ps  in
          FStar_Util.bind_opt uu____1929
            (fun ps1  ->
               let uu____1935 = FStar_Syntax_Embeddings.unembed_range r  in
               FStar_Util.bind_opt uu____1935
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____1943 =
                      let uu____1944 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Tactics_Embedding.embed_proofstate uu____1944 ps'
                       in
                    FStar_Pervasives_Native.Some uu____1943))
      | uu____1945 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____1960)::(b,uu____1962)::[] ->
          let uu____1989 = FStar_Reflection_Embeddings.unembed_env env_t  in
          FStar_Util.bind_opt uu____1989
            (fun env  ->
               let uu____1995 = FStar_Reflection_Embeddings.unembed_binder b
                  in
               FStar_Util.bind_opt uu____1995
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____2003 =
                      FStar_Reflection_Embeddings.embed_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____2003))
      | uu____2004 -> failwith "Unexpected application of push_binder"  in
    let set_proofstate_range_step =
      let nm =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation =
          set_proofstate_range_interp
      }  in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      }  in
    let push_binder_step =
      let nm =
        FStar_Tactics_Embedding.fstar_tactics_lid'
          ["Builtins"; "push_binder"]
         in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = push_binder_interp
      }  in
    let put1 rng t =
      let uu___58_2020 = t  in
      {
        FStar_Syntax_Syntax.n = (uu___58_2020.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___58_2020.FStar_Syntax_Syntax.vars)
      }  in
    let get1 t = FStar_Pervasives_Native.Some t  in
    let uu____2027 =
      let uu____2030 =
        mktac2 () () () "__fail"
          (fun a438  ->
             fun a439  ->
               (Obj.magic (fun uu____2032  -> FStar_Tactics_Basic.fail)) a438
                 a439) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit
         in
      let uu____2033 =
        let uu____2036 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit
           in
        let uu____2037 =
          let uu____2040 =
            let uu____2041 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit
               in
            mktac2 () () () "__trytac"
              (fun a440  ->
                 fun a441  ->
                   (Obj.magic (fun uu____2047  -> FStar_Tactics_Basic.trytac))
                     a440 a441) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____2041)
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2054 =
            let uu____2057 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Embeddings.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder
               in
            let uu____2058 =
              let uu____2061 =
                let uu____2062 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Embeddings.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                let uu____2069 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder
                   in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____2062) uu____2069
                 in
              let uu____2076 =
                let uu____2079 =
                  let uu____2080 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step
                     in
                  mktac1 () () "__norm"
                    (fun a442  -> (Obj.magic FStar_Tactics_Basic.norm) a442)
                    (Obj.magic uu____2080)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit
                   in
                let uu____2089 =
                  let uu____2092 =
                    let uu____2093 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step
                       in
                    mktac3 () () () () "__norm_term_env"
                      (fun a443  ->
                         fun a444  ->
                           fun a445  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a443 a444 a445)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_env)
                      (Obj.magic uu____2093)
                      (Obj.magic FStar_Reflection_Embeddings.unembed_term)
                      (Obj.magic FStar_Reflection_Embeddings.embed_term)
                      FStar_Syntax_Syntax.t_term
                     in
                  let uu____2102 =
                    let uu____2105 =
                      let uu____2106 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step
                         in
                      mktac2 () () () "__norm_binder_type"
                        (fun a446  ->
                           fun a447  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a446 a447) (Obj.magic uu____2106)
                        (Obj.magic FStar_Reflection_Embeddings.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit
                       in
                    let uu____2115 =
                      let uu____2118 =
                        mktac2 () () () "__rename_to"
                          (fun a448  ->
                             fun a449  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a448
                                 a449)
                          (Obj.magic
                             FStar_Reflection_Embeddings.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit
                         in
                      let uu____2119 =
                        let uu____2122 =
                          mktac1 () () "__binder_retype"
                            (fun a450  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a450)
                            (Obj.magic
                               FStar_Reflection_Embeddings.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit
                           in
                        let uu____2123 =
                          let uu____2126 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit
                             in
                          let uu____2127 =
                            let uu____2130 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit
                               in
                            let uu____2131 =
                              let uu____2134 =
                                mktac1 () () "__clear"
                                  (fun a451  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a451)
                                  (Obj.magic
                                     FStar_Reflection_Embeddings.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit
                                 in
                              let uu____2135 =
                                let uu____2138 =
                                  mktac1 () () "__rewrite"
                                    (fun a452  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a452)
                                    (Obj.magic
                                       FStar_Reflection_Embeddings.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                let uu____2139 =
                                  let uu____2142 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit
                                     in
                                  let uu____2143 =
                                    let uu____2146 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit
                                       in
                                    let uu____2147 =
                                      let uu____2150 =
                                        mktac2 () () () "__t_exact"
                                          (fun a453  ->
                                             fun a454  ->
                                               (Obj.magic
                                                  FStar_Tactics_Basic.t_exact)
                                                 a453 a454)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Embeddings.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit
                                         in
                                      let uu____2151 =
                                        let uu____2154 =
                                          mktac1 () () "__apply"
                                            (fun a455  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a455)
                                            (Obj.magic
                                               FStar_Reflection_Embeddings.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit
                                           in
                                        let uu____2155 =
                                          let uu____2158 =
                                            mktac1 () () "__apply_raw"
                                              (fun a456  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a456)
                                              (Obj.magic
                                                 FStar_Reflection_Embeddings.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit
                                             in
                                          let uu____2159 =
                                            let uu____2162 =
                                              mktac1 () () "__apply_lemma"
                                                (fun a457  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a457)
                                                (Obj.magic
                                                   FStar_Reflection_Embeddings.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit
                                               in
                                            let uu____2163 =
                                              let uu____2166 =
                                                let uu____2167 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a458  ->
                                                     fun a459  ->
                                                       fun a460  ->
                                                         fun a461  ->
                                                           fun a462  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2176
                                                                    ->
                                                                   fun
                                                                    uu____2177
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a458 a459 a460
                                                               a461 a462)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____2167)
                                                  FStar_Syntax_Syntax.t_unit
                                                 in
                                              let uu____2184 =
                                                let uu____2187 =
                                                  mktac1 () ()
                                                    "__set_options"
                                                    (fun a463  ->
                                                       (Obj.magic
                                                          FStar_Tactics_Basic.set_options)
                                                         a463)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.unembed_string)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.embed_unit)
                                                    FStar_Syntax_Syntax.t_unit
                                                   in
                                                let uu____2188 =
                                                  let uu____2191 =
                                                    mktac2 () () () "__seq"
                                                      (fun a464  ->
                                                         fun a465  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.seq)
                                                             a464 a465)
                                                      (Obj.magic
                                                         (unembed_tactic_0'
                                                            FStar_Syntax_Embeddings.unembed_unit))
                                                      (Obj.magic
                                                         (unembed_tactic_0'
                                                            FStar_Syntax_Embeddings.unembed_unit))
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.embed_unit)
                                                      FStar_Syntax_Syntax.t_unit
                                                     in
                                                  let uu____2192 =
                                                    let uu____2195 =
                                                      mktac1 () () "__tc"
                                                        (fun a466  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a466)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Embeddings.embed_term)
                                                        FStar_Syntax_Syntax.t_term
                                                       in
                                                    let uu____2196 =
                                                      let uu____2199 =
                                                        mktac1 () ()
                                                          "__unshelve"
                                                          (fun a467  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a467)
                                                          (Obj.magic
                                                             FStar_Reflection_Embeddings.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit
                                                         in
                                                      let uu____2200 =
                                                        let uu____2203 =
                                                          mktac2 () () ()
                                                            "__unquote"
                                                            (fun a468  ->
                                                               fun a469  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a468 a469)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Embeddings.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit
                                                           in
                                                        let uu____2204 =
                                                          let uu____2207 =
                                                            mktac1 () ()
                                                              "__prune"
                                                              (fun a470  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a470)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit
                                                             in
                                                          let uu____2208 =
                                                            let uu____2211 =
                                                              mktac1 () ()
                                                                "__addns"
                                                                (fun a471  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a471)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit
                                                               in
                                                            let uu____2212 =
                                                              let uu____2215
                                                                =
                                                                mktac1 () ()
                                                                  "__print"
                                                                  (fun a472 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun x 
                                                                    ->
                                                                    FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                    FStar_Tactics_Basic.ret
                                                                    ())) a472)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit
                                                                 in
                                                              let uu____2220
                                                                =
                                                                let uu____2223
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "__dump"
                                                                    (
                                                                    fun a473 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a473)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                   in
                                                                let uu____2224
                                                                  =
                                                                  let uu____2227
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__dump1"
                                                                    (fun a474
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a474)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                  let uu____2228
                                                                    =
                                                                    let uu____2231
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a475
                                                                     ->
                                                                    fun a476 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a475 a476)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2232
                                                                    =
                                                                    let uu____2235
                                                                    =
                                                                    let uu____2236
                                                                    =
                                                                    let uu____2247
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_pair
                                                                    FStar_Syntax_Embeddings.unembed_bool
                                                                    FStar_Syntax_Embeddings.unembed_int
                                                                     in
                                                                    unembed_tactic_1
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    uu____2247
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__topdown_rewrite"
                                                                    (fun a477
                                                                     ->
                                                                    fun a478 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.topdown_rewrite)
                                                                    a477 a478)
                                                                    (Obj.magic
                                                                    uu____2236)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2266
                                                                    =
                                                                    let uu____2269
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2270
                                                                    =
                                                                    let uu____2273
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2274
                                                                    =
                                                                    let uu____2277
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2278
                                                                    =
                                                                    let uu____2281
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2282
                                                                    =
                                                                    let uu____2285
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2286
                                                                    =
                                                                    let uu____2289
                                                                    =
                                                                    mktac0 ()
                                                                    "__dismiss"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dismiss)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2290
                                                                    =
                                                                    let uu____2293
                                                                    =
                                                                    mktac0 ()
                                                                    "__tadmit"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.tadmit)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2294
                                                                    =
                                                                    let uu____2297
                                                                    =
                                                                    let uu____2298
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Embeddings.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2305
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    mktac1 ()
                                                                    ()
                                                                    "__cases"
                                                                    (fun a479
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a479)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2298)
                                                                    uu____2305
                                                                     in
                                                                    let uu____2312
                                                                    =
                                                                    let uu____2315
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2316
                                                                    =
                                                                    let uu____2319
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env
                                                                     in
                                                                    let uu____2320
                                                                    =
                                                                    let uu____2323
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2324
                                                                    =
                                                                    let uu____2327
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2328
                                                                    =
                                                                    let uu____2331
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__inspect"
                                                                    (fun a480
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.inspect)
                                                                    a480)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term_view)
                                                                    FStar_Reflection_Data.fstar_refl_term_view
                                                                     in
                                                                    let uu____2332
                                                                    =
                                                                    let uu____2335
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__pack"
                                                                    (fun a481
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pack)
                                                                    a481)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term_view)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2336
                                                                    =
                                                                    let uu____2339
                                                                    =
                                                                    mktac0 ()
                                                                    "__ngoals"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2340
                                                                    =
                                                                    let uu____2343
                                                                    =
                                                                    mktac0 ()
                                                                    "__ngoals_smt"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.ngoals_smt)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_int)
                                                                    FStar_Syntax_Syntax.t_int
                                                                     in
                                                                    let uu____2344
                                                                    =
                                                                    let uu____2347
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2348
                                                                    =
                                                                    let uu____2351
                                                                    =
                                                                    let uu____2352
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Embeddings.unembed_term
                                                                     in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__uvar_env"
                                                                    (fun a482
                                                                     ->
                                                                    fun a483 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a482 a483)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2352)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_term)
                                                                    FStar_Syntax_Syntax.t_term
                                                                     in
                                                                    let uu____2361
                                                                    =
                                                                    let uu____2364
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__unify"
                                                                    (fun a484
                                                                     ->
                                                                    fun a485 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a484 a485)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool
                                                                     in
                                                                    let uu____2365
                                                                    =
                                                                    let uu____2368
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "__launch_process"
                                                                    (fun a486
                                                                     ->
                                                                    fun a487 
                                                                    ->
                                                                    fun a488 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a486 a487
                                                                    a488)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_string)
                                                                    FStar_Syntax_Syntax.t_string
                                                                     in
                                                                    let uu____2369
                                                                    =
                                                                    let uu____2372
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__fresh_bv_named"
                                                                    (fun a489
                                                                     ->
                                                                    fun a490 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.fresh_bv_named)
                                                                    a489 a490)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.embed_bv)
                                                                    FStar_Syntax_Syntax.t_bv
                                                                     in
                                                                    let uu____2373
                                                                    =
                                                                    let uu____2376
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__change"
                                                                    (fun a491
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.change)
                                                                    a491)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Embeddings.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    let uu____2377
                                                                    =
                                                                    let uu____2380
                                                                    =
                                                                    mktac0 ()
                                                                    "__get_guard_policy"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.get_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.embed_guard_policy)
                                                                    FStar_Tactics_Embedding.t_guard_policy
                                                                     in
                                                                    let uu____2381
                                                                    =
                                                                    let uu____2384
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__set_guard_policy"
                                                                    (fun a492
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.set_guard_policy)
                                                                    a492)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_guard_policy)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit
                                                                     in
                                                                    [uu____2384;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____2380
                                                                    ::
                                                                    uu____2381
                                                                     in
                                                                    uu____2376
                                                                    ::
                                                                    uu____2377
                                                                     in
                                                                    uu____2372
                                                                    ::
                                                                    uu____2373
                                                                     in
                                                                    uu____2368
                                                                    ::
                                                                    uu____2369
                                                                     in
                                                                    uu____2364
                                                                    ::
                                                                    uu____2365
                                                                     in
                                                                    uu____2351
                                                                    ::
                                                                    uu____2361
                                                                     in
                                                                    uu____2347
                                                                    ::
                                                                    uu____2348
                                                                     in
                                                                    uu____2343
                                                                    ::
                                                                    uu____2344
                                                                     in
                                                                    uu____2339
                                                                    ::
                                                                    uu____2340
                                                                     in
                                                                    uu____2335
                                                                    ::
                                                                    uu____2336
                                                                     in
                                                                    uu____2331
                                                                    ::
                                                                    uu____2332
                                                                     in
                                                                    uu____2327
                                                                    ::
                                                                    uu____2328
                                                                     in
                                                                    uu____2323
                                                                    ::
                                                                    uu____2324
                                                                     in
                                                                    uu____2319
                                                                    ::
                                                                    uu____2320
                                                                     in
                                                                    uu____2315
                                                                    ::
                                                                    uu____2316
                                                                     in
                                                                    uu____2297
                                                                    ::
                                                                    uu____2312
                                                                     in
                                                                    uu____2293
                                                                    ::
                                                                    uu____2294
                                                                     in
                                                                    uu____2289
                                                                    ::
                                                                    uu____2290
                                                                     in
                                                                    uu____2285
                                                                    ::
                                                                    uu____2286
                                                                     in
                                                                    uu____2281
                                                                    ::
                                                                    uu____2282
                                                                     in
                                                                    uu____2277
                                                                    ::
                                                                    uu____2278
                                                                     in
                                                                    uu____2273
                                                                    ::
                                                                    uu____2274
                                                                     in
                                                                    uu____2269
                                                                    ::
                                                                    uu____2270
                                                                     in
                                                                    uu____2235
                                                                    ::
                                                                    uu____2266
                                                                     in
                                                                    uu____2231
                                                                    ::
                                                                    uu____2232
                                                                     in
                                                                  uu____2227
                                                                    ::
                                                                    uu____2228
                                                                   in
                                                                uu____2223 ::
                                                                  uu____2224
                                                                 in
                                                              uu____2215 ::
                                                                uu____2220
                                                               in
                                                            uu____2211 ::
                                                              uu____2212
                                                             in
                                                          uu____2207 ::
                                                            uu____2208
                                                           in
                                                        uu____2203 ::
                                                          uu____2204
                                                         in
                                                      uu____2199 ::
                                                        uu____2200
                                                       in
                                                    uu____2195 :: uu____2196
                                                     in
                                                  uu____2191 :: uu____2192
                                                   in
                                                uu____2187 :: uu____2188  in
                                              uu____2166 :: uu____2184  in
                                            uu____2162 :: uu____2163  in
                                          uu____2158 :: uu____2159  in
                                        uu____2154 :: uu____2155  in
                                      uu____2150 :: uu____2151  in
                                    uu____2146 :: uu____2147  in
                                  uu____2142 :: uu____2143  in
                                uu____2138 :: uu____2139  in
                              uu____2134 :: uu____2135  in
                            uu____2130 :: uu____2131  in
                          uu____2126 :: uu____2127  in
                        uu____2122 :: uu____2123  in
                      uu____2118 :: uu____2119  in
                    uu____2105 :: uu____2115  in
                  uu____2092 :: uu____2102  in
                uu____2079 :: uu____2089  in
              uu____2061 :: uu____2076  in
            uu____2057 :: uu____2058  in
          uu____2040 :: uu____2054  in
        uu____2036 :: uu____2037  in
      uu____2030 :: uu____2033  in
    FStar_List.append uu____2027
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)

and unembed_tactic_1 :
  'Aa 'Ab .
    'Aa FStar_Syntax_Embeddings.embedder ->
      'Ab FStar_Syntax_Embeddings.unembedder ->
        FStar_Syntax_Syntax.term ->
          ('Aa -> 'Ab FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option
  =
  fun arg  ->
    fun res  ->
      fun f  ->
        FStar_Pervasives_Native.Some
          (fun x  ->
             let rng = FStar_Range.dummyRange  in
             let x_tm = arg rng x  in
             let app =
               let uu____2414 =
                 let uu____2415 =
                   let uu____2416 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____2416]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____2415  in
               uu____2414 FStar_Pervasives_Native.None rng  in
             unembed_tactic_0 res app)

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term -> 'Ab FStar_Tactics_Basic.tac
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state  ->
           let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
           let tm =
             let uu____2445 =
               let uu____2446 =
                 let uu____2447 =
                   let uu____2448 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____2448  in
                 [uu____2447]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2446  in
             uu____2445 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           (let uu____2455 =
              FStar_TypeChecker_Env.debug
                proof_state.FStar_Tactics_Types.main_context
                (FStar_Options.Other "TacVerbose")
               in
            if uu____2455
            then
              let uu____2456 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2456
            else ());
           (let result =
              let uu____2459 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2459 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            (let uu____2463 =
               FStar_TypeChecker_Env.debug
                 proof_state.FStar_Tactics_Types.main_context
                 (FStar_Options.Other "TacVerbose")
                in
             if uu____2463
             then
               let uu____2464 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2464
             else ());
            (let res =
               FStar_Tactics_Embedding.unembed_result result unembed_b  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2509 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2509
                   (fun uu____2513  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2536 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____2536
                   (fun uu____2540  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2553 =
                   let uu____2558 =
                     let uu____2559 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2559
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2558)  in
                 FStar_Errors.raise_error uu____2553
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2568 = unembed_tactic_0 unembed_b embedded_tac_b  in
      FStar_All.pipe_left (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
        uu____2568

let (report_implicits :
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit)
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2624  ->
             match uu____2624 with
             | (r,uu____2644,uv,uu____2646,ty,rng) ->
                 let uu____2649 =
                   let uu____2650 = FStar_Syntax_Print.uvar_to_string uv  in
                   let uu____2651 = FStar_Syntax_Print.term_to_string ty  in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2650 uu____2651 r
                    in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2649, rng)) is
         in
      match errs with
      | [] -> ()
      | (e,msg,r)::tl1 ->
          (FStar_Tactics_Basic.dump_proofstate ps
             "failing due to uninstantiated implicits";
           FStar_Errors.add_errors tl1;
           FStar_Errors.raise_error (e, msg) r)
  
let (run_tactic_on_typ :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Tactics_Basic.goal Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun tactic  ->
    fun env  ->
      fun typ  ->
        (let uu____2700 = FStar_ST.op_Bang tacdbg  in
         if uu____2700
         then
           let uu____2720 = FStar_Syntax_Print.term_to_string tactic  in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2720
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic  in
         (let uu____2724 = FStar_ST.op_Bang tacdbg  in
          if uu____2724
          then
            let uu____2744 = FStar_Syntax_Print.term_to_string tactic1  in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2744
          else ());
         (let uu____2746 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1  in
          match uu____2746 with
          | (uu____2759,uu____2760,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic1
                   in
                let uu____2767 = FStar_TypeChecker_Env.clear_expected_typ env
                   in
                match uu____2767 with
                | (env1,uu____2781) ->
                    let env2 =
                      let uu___59_2787 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___59_2787.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___59_2787.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___59_2787.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___59_2787.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___59_2787.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___59_2787.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___59_2787.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___59_2787.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___59_2787.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___59_2787.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___59_2787.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___59_2787.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___59_2787.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___59_2787.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___59_2787.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___59_2787.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___59_2787.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___59_2787.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___59_2787.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___59_2787.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___59_2787.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___59_2787.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___59_2787.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___59_2787.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___59_2787.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___59_2787.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___59_2787.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___59_2787.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___59_2787.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.splice =
                          (uu___59_2787.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___59_2787.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___59_2787.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___59_2787.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___59_2787.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___59_2787.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let env3 =
                      let uu___60_2789 = env2  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___60_2789.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___60_2789.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___60_2789.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___60_2789.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___60_2789.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___60_2789.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___60_2789.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___60_2789.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___60_2789.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___60_2789.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___60_2789.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___60_2789.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___60_2789.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___60_2789.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___60_2789.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___60_2789.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___60_2789.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___60_2789.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___60_2789.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes = true;
                        FStar_TypeChecker_Env.failhard =
                          (uu___60_2789.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___60_2789.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___60_2789.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___60_2789.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___60_2789.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___60_2789.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___60_2789.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___60_2789.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___60_2789.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___60_2789.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.splice =
                          (uu___60_2789.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___60_2789.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___60_2789.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___60_2789.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___60_2789.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___60_2789.FStar_TypeChecker_Env.dep_graph)
                      }  in
                    let uu____2790 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env3 typ  in
                    (match uu____2790 with
                     | (ps,w) ->
                         ((let uu____2804 = FStar_ST.op_Bang tacdbg  in
                           if uu____2804
                           then
                             let uu____2824 =
                               FStar_Syntax_Print.term_to_string typ  in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____2824
                           else ());
                          (let uu____2826 =
                             FStar_Util.record_time
                               (fun uu____2836  ->
                                  FStar_Tactics_Basic.run tau ps)
                              in
                           match uu____2826 with
                           | (res,ms) ->
                               ((let uu____2850 = FStar_ST.op_Bang tacdbg  in
                                 if uu____2850
                                 then
                                   let uu____2870 =
                                     FStar_Syntax_Print.term_to_string
                                       tactic1
                                      in
                                   let uu____2871 =
                                     FStar_Util.string_of_int ms  in
                                   let uu____2872 =
                                     FStar_Syntax_Print.lid_to_string
                                       env3.FStar_TypeChecker_Env.curmodule
                                      in
                                   FStar_Util.print3
                                     "Tactic %s ran in %s ms (%s)\n"
                                     uu____2870 uu____2871 uu____2872
                                 else ());
                                (match res with
                                 | FStar_Tactics_Result.Success
                                     (uu____2880,ps1) ->
                                     ((let uu____2883 =
                                         FStar_ST.op_Bang tacdbg  in
                                       if uu____2883
                                       then
                                         let uu____2903 =
                                           FStar_Syntax_Print.term_to_string
                                             w
                                            in
                                         FStar_Util.print1
                                           "Tactic generated proofterm %s\n"
                                           uu____2903
                                       else ());
                                      FStar_List.iter
                                        (fun g1  ->
                                           let uu____2910 =
                                             FStar_Tactics_Basic.is_irrelevant
                                               g1
                                              in
                                           if uu____2910
                                           then
                                             let uu____2911 =
                                               FStar_TypeChecker_Rel.teq_nosmt
                                                 g1.FStar_Tactics_Types.context
                                                 g1.FStar_Tactics_Types.witness
                                                 FStar_Syntax_Util.exp_unit
                                                in
                                             (if uu____2911
                                              then ()
                                              else
                                                (let uu____2913 =
                                                   let uu____2914 =
                                                     FStar_Syntax_Print.term_to_string
                                                       g1.FStar_Tactics_Types.witness
                                                      in
                                                   FStar_Util.format1
                                                     "Irrelevant tactic witness does not unify with (): %s"
                                                     uu____2914
                                                    in
                                                 failwith uu____2913))
                                           else ())
                                        (FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals);
                                      (let g1 =
                                         let uu___61_2917 =
                                           FStar_TypeChecker_Rel.trivial_guard
                                            in
                                         {
                                           FStar_TypeChecker_Env.guard_f =
                                             (uu___61_2917.FStar_TypeChecker_Env.guard_f);
                                           FStar_TypeChecker_Env.deferred =
                                             (uu___61_2917.FStar_TypeChecker_Env.deferred);
                                           FStar_TypeChecker_Env.univ_ineqs =
                                             (uu___61_2917.FStar_TypeChecker_Env.univ_ineqs);
                                           FStar_TypeChecker_Env.implicits =
                                             (ps1.FStar_Tactics_Types.all_implicits)
                                         }  in
                                       let g2 =
                                         let uu____2919 =
                                           FStar_TypeChecker_Rel.solve_deferred_constraints
                                             env3 g1
                                            in
                                         FStar_All.pipe_right uu____2919
                                           FStar_TypeChecker_Rel.resolve_implicits_tac
                                          in
                                       report_implicits ps1
                                         g2.FStar_TypeChecker_Env.implicits;
                                       ((FStar_List.append
                                           ps1.FStar_Tactics_Types.goals
                                           ps1.FStar_Tactics_Types.smt_goals),
                                         w)))
                                 | FStar_Tactics_Result.Failed (s,ps1) ->
                                     ((let uu____2926 =
                                         let uu____2927 =
                                           FStar_TypeChecker_Normalize.psc_subst
                                             ps1.FStar_Tactics_Types.psc
                                            in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____2927 ps1
                                          in
                                       FStar_Tactics_Basic.dump_proofstate
                                         uu____2926 "at the time of failure");
                                      (let uu____2928 =
                                         let uu____2933 =
                                           FStar_Util.format1
                                             "user tactic failed: %s" s
                                            in
                                         (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                           uu____2933)
                                          in
                                       FStar_Errors.raise_error uu____2928
                                         typ.FStar_Syntax_Syntax.pos)))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both [@@deriving show]
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2943 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2947 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2951 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____3000 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____3036 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____3086 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure : 'Auu____3124 . 'Auu____3124 -> 'Auu____3124 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3143 = FStar_Syntax_Util.head_and_args t  in
        match uu____3143 with
        | (hd1,args) ->
            let uu____3180 =
              let uu____3193 =
                let uu____3194 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3194.FStar_Syntax_Syntax.n  in
              (uu____3193, args)  in
            (match uu____3180 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3207))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3270 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3270 with
                       | (gs,uu____3278) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3285 = run_tactic_on_typ tactic e assertion
                         in
                      (match uu____3285 with
                       | (gs,uu____3293) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3344 =
                        let uu____3351 =
                          let uu____3354 =
                            let uu____3355 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3355
                             in
                          [uu____3354]  in
                        (FStar_Syntax_Util.t_true, uu____3351)  in
                      Simplified uu____3344
                  | Both  ->
                      let uu____3366 =
                        let uu____3379 =
                          let uu____3382 =
                            let uu____3383 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3383
                             in
                          [uu____3382]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3379)  in
                      Dual uu____3366
                  | Neg  -> Simplified (assertion, []))
             | uu____3404 -> Unchanged t)
  
let explode :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___57_3484  ->
      match uu___57_3484 with
      | Unchanged t -> let uu____3490 = f t  in Unchanged uu____3490
      | Simplified (t,gs) ->
          let uu____3497 = let uu____3504 = f t  in (uu____3504, gs)  in
          Simplified uu____3497
      | Dual (tn,tp,gs) ->
          let uu____3514 =
            let uu____3523 = f tn  in
            let uu____3524 = f tp  in (uu____3523, uu____3524, gs)  in
          Dual uu____3514
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3578 = f t1 t2  in Unchanged uu____3578
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3590 = let uu____3597 = f t1 t2  in (uu____3597, gs)
               in
            Simplified uu____3590
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3611 = let uu____3618 = f t1 t2  in (uu____3618, gs)
               in
            Simplified uu____3611
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3637 =
              let uu____3644 = f t1 t2  in
              (uu____3644, (FStar_List.append gs1 gs2))  in
            Simplified uu____3637
        | uu____3647 ->
            let uu____3656 = explode x  in
            (match uu____3656 with
             | (n1,p1,gs1) ->
                 let uu____3674 = explode y  in
                 (match uu____3674 with
                  | (n2,p2,gs2) ->
                      let uu____3692 =
                        let uu____3701 = f n1 n2  in
                        let uu____3702 = f p1 p2  in
                        (uu____3701, uu____3702, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3692))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3767 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3767
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3810  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3844 =
              let uu____3845 = FStar_Syntax_Subst.compress t  in
              uu____3845.FStar_Syntax_Syntax.n  in
            match uu____3844 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3857 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3857 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3881 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3881 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3899;
                   FStar_Syntax_Syntax.vars = uu____3900;_},(p,uu____3902)::
                 (q,uu____3904)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3944 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3944
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3947 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3947 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3953 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3953.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3957;
                   FStar_Syntax_Syntax.vars = uu____3958;_},(p,uu____3960)::
                 (q,uu____3962)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____4002 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4002
                   in
                let xq =
                  let uu____4004 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____4004
                   in
                let r1 =
                  let uu____4006 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____4006 p  in
                let r2 =
                  let uu____4008 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____4008 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4011,Unchanged uu____4012) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4022 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4022.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4025 ->
                     let uu____4030 = explode r1  in
                     (match uu____4030 with
                      | (pn,pp,gs1) ->
                          let uu____4048 = explode r2  in
                          (match uu____4048 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4069 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4070 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4069
                                   uu____4070
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4122  ->
                       fun r  ->
                         match uu____4122 with
                         | (a,q) ->
                             let r' = traverse f pol e a  in
                             comb2
                               (fun a1  -> fun args1  -> (a1, q) :: args1) r'
                               r) args (tpure [])
                   in
                comb2
                  (fun hd2  ->
                     fun args1  -> FStar_Syntax_Syntax.Tm_app (hd2, args1))
                  r0 r1
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____4240 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4240 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4274  ->
                            match uu____4274 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4288 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___62_4312 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___62_4312.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___62_4312.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4288 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4332 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4332.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4378 = traverse f pol e t1  in
                let uu____4383 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4383 uu____4378
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___63_4421 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___63_4421.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___63_4421.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4428 =
                f pol e
                  (let uu___64_4432 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___64_4432.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___64_4432.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4428
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___65_4442 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___65_4442.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___65_4442.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4443 = explode rp  in
              (match uu____4443 with
               | (uu____4452,p',gs') ->
                   Dual
                     ((let uu___66_4466 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___66_4466.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___66_4466.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
  
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t
         in
      FStar_Syntax_Util.un_squash tn
  
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_Options.optionstate)
        FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun env  ->
    fun goal  ->
      (let uu____4501 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4501);
      (let uu____4522 = FStar_ST.op_Bang tacdbg  in
       if uu____4522
       then
         let uu____4542 =
           let uu____4543 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4543
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4544 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4542
           uu____4544
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4573 =
         let uu____4580 = traverse by_tactic_interp Pos env goal  in
         match uu____4580 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4598 -> failwith "no"  in
       match uu____4573 with
       | (t',gs) ->
           ((let uu____4620 = FStar_ST.op_Bang tacdbg  in
             if uu____4620
             then
               let uu____4640 =
                 let uu____4641 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4641
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4642 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4640 uu____4642
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4689  ->
                    fun g  ->
                      match uu____4689 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4734 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty
                               in
                            match uu____4734 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4737 =
                                  let uu____4742 =
                                    let uu____4743 =
                                      FStar_Syntax_Print.term_to_string
                                        g.FStar_Tactics_Types.goal_ty
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____4743
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____4742)
                                   in
                                FStar_Errors.raise_error uu____4737
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4746 = FStar_ST.op_Bang tacdbg  in
                            if uu____4746
                            then
                              let uu____4766 = FStar_Util.string_of_int n1
                                 in
                              let uu____4767 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4766 uu____4767
                            else ());
                           (let gt' =
                              let uu____4770 =
                                let uu____4771 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4771
                                 in
                              FStar_TypeChecker_Util.label uu____4770
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs
                in
             let uu____4786 = s1  in
             match uu____4786 with
             | (uu____4807,gs1) ->
                 let uu____4825 =
                   let uu____4832 = FStar_Options.peek ()  in
                   (env, t', uu____4832)  in
                 uu____4825 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4843 =
        let uu____4844 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4844  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4843 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4845 =
      let uu____4846 =
        let uu____4847 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4848 =
          let uu____4851 = FStar_Syntax_Syntax.as_arg a  in [uu____4851]  in
        uu____4847 :: uu____4848  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4846  in
    uu____4845 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4864 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____4864);
        (let uu____4884 =
           let uu____4891 = reify_tactic tau  in
           run_tactic_on_typ uu____4891 env typ  in
         match uu____4884 with
         | (gs,w) ->
             let uu____4898 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4902 =
                      let uu____4903 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4903  in
                    Prims.op_Negation uu____4902) gs
                in
             if uu____4898
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "synthesis left open goals") typ.FStar_Syntax_Syntax.pos
             else w)
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      (let uu____4918 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4918);
      (let typ = FStar_Syntax_Syntax.t_decls  in
       let uu____4939 =
         let uu____4946 = reify_tactic tau  in
         run_tactic_on_typ uu____4946 env typ  in
       match uu____4939 with
       | (gs,w) ->
           ((let uu____4956 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4960 =
                      let uu____4961 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty
                         in
                      FStar_Option.isSome uu____4961  in
                    Prims.op_Negation uu____4960) gs
                in
             if uu____4956
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "splice left open goals") typ.FStar_Syntax_Syntax.pos
             else ());
            (let w1 =
               FStar_TypeChecker_Normalize.normalize
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant;
                 FStar_TypeChecker_Normalize.Primops;
                 FStar_TypeChecker_Normalize.Unascribe;
                 FStar_TypeChecker_Normalize.Unmeta] env w
                in
             let uu____4966 =
               let uu____4971 =
                 FStar_Syntax_Embeddings.unembed_list
                   FStar_Reflection_Embeddings.unembed_sigelt
                  in
               uu____4971 w1  in
             FStar_All.pipe_left FStar_Util.must uu____4966)))
  