open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mktot1' :
  'Auu____30 'Auu____31 'Auu____32 'Auu____33 .
    Prims.int ->
      Prims.string ->
        ('Auu____30 -> 'Auu____31) ->
          'Auu____30 FStar_Syntax_Embeddings.embedding ->
            'Auu____31 FStar_Syntax_Embeddings.embedding ->
              ('Auu____32 -> 'Auu____33) ->
                'Auu____32 FStar_TypeChecker_NBETerm.embedding ->
                  'Auu____33 FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity  ->
    fun nm  ->
      fun f  ->
        fun ea  ->
          fun er  ->
            fun nf  ->
              fun ena  ->
                fun enr  ->
                  let uu___9_104 =
                    FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena
                      enr
                     in
                  let uu____105 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____105;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___9_104.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___9_104.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___9_104.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___9_104.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___9_104.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___9_104.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___9_104.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot2' :
  'Auu____140 'Auu____141 'Auu____142 'Auu____143 'Auu____144 'Auu____145 .
    Prims.int ->
      Prims.string ->
        ('Auu____140 -> 'Auu____141 -> 'Auu____142) ->
          'Auu____140 FStar_Syntax_Embeddings.embedding ->
            'Auu____141 FStar_Syntax_Embeddings.embedding ->
              'Auu____142 FStar_Syntax_Embeddings.embedding ->
                ('Auu____143 -> 'Auu____144 -> 'Auu____145) ->
                  'Auu____143 FStar_TypeChecker_NBETerm.embedding ->
                    'Auu____144 FStar_TypeChecker_NBETerm.embedding ->
                      'Auu____145 FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity  ->
    fun nm  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun er  ->
              fun nf  ->
                fun ena  ->
                  fun enb  ->
                    fun enr  ->
                      let uu___21_244 =
                        FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er
                          nf ena enb enr
                         in
                      let uu____245 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm)
                         in
                      {
                        FStar_TypeChecker_Cfg.name = uu____245;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___21_244.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___21_244.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___21_244.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___21_244.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___21_244.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___21_244.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___21_244.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
  
let rec e_tactic_thunk :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____551 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____558  ->
         fun uu____559  ->
           fun uu____560  ->
             fun uu____561  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____575 =
               let uu____578 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____578 ()  in
             FStar_Pervasives_Native.Some uu____575) uu____551

and e_tactic_nbe_thunk :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____590 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____596  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____605 =
             let uu____608 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____608 ()  in
           FStar_Pervasives_Native.Some uu____605)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____590

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____623 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____633  ->
           fun uu____634  ->
             fun uu____635  ->
               fun uu____636  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____652 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____652) uu____623

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____670 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____679  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____690 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____690)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____670

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____702  ->
    let uu____705 =
      let uu____708 =
        mktot1' Prims.int_zero "tracepoint" FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate FStar_Syntax_Embeddings.e_unit
          FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____711 =
        let uu____714 =
          mktot2' Prims.int_zero "set_proofstate_range"
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_range
            FStar_Tactics_Embedding.e_proofstate_nbe
           in
        let uu____717 =
          let uu____720 =
            mktot1' Prims.int_zero "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____723 =
            let uu____726 =
              mktot1' Prims.int_zero "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____729 =
              let uu____732 =
                let uu____733 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____738 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mktot1' Prims.int_zero "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____733
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____738
                 in
              let uu____749 =
                let uu____752 =
                  let uu____753 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____758 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mktot1' Prims.int_zero "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____753
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____758
                   in
                let uu____769 =
                  let uu____772 =
                    mktot1' Prims.int_zero "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____775 =
                    let uu____778 =
                      mktot1' Prims.int_zero "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____781 =
                      let uu____784 =
                        mktot1' Prims.int_zero "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____787 =
                        let uu____790 =
                          mktot1' Prims.int_zero "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____795 =
                          let uu____798 =
                            mktot1' Prims.int_zero "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string
                             in
                          let uu____803 =
                            let uu____806 =
                              mktot2' Prims.int_zero "set_label"
                                FStar_Tactics_Types.set_label
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Types.set_label
                                FStar_TypeChecker_NBETerm.e_string
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_Tactics_Embedding.e_goal_nbe
                               in
                            let uu____811 =
                              let uu____814 =
                                FStar_Tactics_InterpFuns.mktot2
                                  Prims.int_zero "push_binder"
                                  (fun env  ->
                                     fun b  ->
                                       FStar_TypeChecker_Env.push_binders env
                                         [b])
                                  FStar_Reflection_Embeddings.e_env
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Reflection_Embeddings.e_env
                                  (fun env  ->
                                     fun b  ->
                                       FStar_TypeChecker_Env.push_binders env
                                         [b])
                                  FStar_Reflection_NBEEmbeddings.e_env
                                  FStar_Reflection_NBEEmbeddings.e_binder
                                  FStar_Reflection_NBEEmbeddings.e_env
                                 in
                              let uu____873 =
                                let uu____876 =
                                  let uu____877 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal
                                     in
                                  let uu____882 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe
                                     in
                                  FStar_Tactics_InterpFuns.mktac1
                                    Prims.int_zero "set_goals"
                                    FStar_Tactics_Basic.set_goals uu____877
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Basic.set_goals uu____882
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____893 =
                                  let uu____896 =
                                    let uu____897 =
                                      FStar_Syntax_Embeddings.e_list
                                        FStar_Tactics_Embedding.e_goal
                                       in
                                    let uu____902 =
                                      FStar_TypeChecker_NBETerm.e_list
                                        FStar_Tactics_Embedding.e_goal_nbe
                                       in
                                    FStar_Tactics_InterpFuns.mktac1
                                      Prims.int_zero "set_smt_goals"
                                      FStar_Tactics_Basic.set_smt_goals
                                      uu____897
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.set_smt_goals
                                      uu____902
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____913 =
                                    let uu____916 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        Prims.int_zero "trivial"
                                        FStar_Tactics_Basic.trivial
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.trivial
                                        FStar_TypeChecker_NBETerm.e_unit
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____919 =
                                      let uu____922 =
                                        let uu____923 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____928 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____935 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        let uu____940 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        FStar_Tactics_InterpFuns.mktac2
                                          Prims.int_one "catch"
                                          (fun uu____962  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____923 uu____928
                                          (fun uu____964  ->
                                             FStar_Tactics_Basic.catch)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____935 uu____940
                                         in
                                      let uu____965 =
                                        let uu____968 =
                                          let uu____969 =
                                            e_tactic_thunk
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____974 =
                                            FStar_Syntax_Embeddings.e_either
                                              FStar_Tactics_Embedding.e_exn
                                              FStar_Syntax_Embeddings.e_any
                                             in
                                          let uu____981 =
                                            e_tactic_nbe_thunk
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          let uu____986 =
                                            FStar_TypeChecker_NBETerm.e_either
                                              FStar_Tactics_Embedding.e_exn_nbe
                                              FStar_TypeChecker_NBETerm.e_any
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            Prims.int_one "recover"
                                            (fun uu____1008  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_Syntax_Embeddings.e_any
                                            uu____969 uu____974
                                            (fun uu____1010  ->
                                               FStar_Tactics_Basic.recover)
                                            FStar_TypeChecker_NBETerm.e_any
                                            uu____981 uu____986
                                           in
                                        let uu____1011 =
                                          let uu____1014 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              Prims.int_zero "intro"
                                              FStar_Tactics_Basic.intro
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Tactics_Basic.intro
                                              FStar_TypeChecker_NBETerm.e_unit
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                             in
                                          let uu____1017 =
                                            let uu____1020 =
                                              let uu____1021 =
                                                FStar_Syntax_Embeddings.e_tuple2
                                                  FStar_Reflection_Embeddings.e_binder
                                                  FStar_Reflection_Embeddings.e_binder
                                                 in
                                              let uu____1028 =
                                                FStar_TypeChecker_NBETerm.e_tuple2
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                 in
                                              FStar_Tactics_InterpFuns.mktac1
                                                Prims.int_zero "intro_rec"
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_Syntax_Embeddings.e_unit
                                                uu____1021
                                                FStar_Tactics_Basic.intro_rec
                                                FStar_TypeChecker_NBETerm.e_unit
                                                uu____1028
                                               in
                                            let uu____1045 =
                                              let uu____1048 =
                                                let uu____1049 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step
                                                   in
                                                let uu____1054 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step
                                                   in
                                                FStar_Tactics_InterpFuns.mktac1
                                                  Prims.int_zero "norm"
                                                  FStar_Tactics_Basic.norm
                                                  uu____1049
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.norm
                                                  uu____1054
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                 in
                                              let uu____1065 =
                                                let uu____1068 =
                                                  let uu____1069 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____1074 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac3
                                                    Prims.int_zero
                                                    "norm_term_env"
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_Embeddings.e_env
                                                    uu____1069
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Tactics_Basic.norm_term_env
                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                    uu____1074
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                   in
                                                let uu____1085 =
                                                  let uu____1088 =
                                                    let uu____1089 =
                                                      FStar_Syntax_Embeddings.e_list
                                                        FStar_Syntax_Embeddings.e_norm_step
                                                       in
                                                    let uu____1094 =
                                                      FStar_TypeChecker_NBETerm.e_list
                                                        FStar_TypeChecker_NBETerm.e_norm_step
                                                       in
                                                    FStar_Tactics_InterpFuns.mktac2
                                                      Prims.int_zero
                                                      "norm_binder_type"
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1089
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_unit
                                                      FStar_Tactics_Basic.norm_binder_type
                                                      uu____1094
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_unit
                                                     in
                                                  let uu____1105 =
                                                    let uu____1108 =
                                                      FStar_Tactics_InterpFuns.mktac2
                                                        Prims.int_zero
                                                        "rename_to"
                                                        FStar_Tactics_Basic.rename_to
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Syntax_Embeddings.e_string
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.rename_to
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_string
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                       in
                                                    let uu____1113 =
                                                      let uu____1116 =
                                                        FStar_Tactics_InterpFuns.mktac1
                                                          Prims.int_zero
                                                          "binder_retype"
                                                          FStar_Tactics_Basic.binder_retype
                                                          FStar_Reflection_Embeddings.e_binder
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.binder_retype
                                                          FStar_Reflection_NBEEmbeddings.e_binder
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                         in
                                                      let uu____1119 =
                                                        let uu____1122 =
                                                          FStar_Tactics_InterpFuns.mktac1
                                                            Prims.int_zero
                                                            "revert"
                                                            FStar_Tactics_Basic.revert
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_Basic.revert
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                           in
                                                        let uu____1125 =
                                                          let uu____1128 =
                                                            FStar_Tactics_InterpFuns.mktac1
                                                              Prims.int_zero
                                                              "clear_top"
                                                              FStar_Tactics_Basic.clear_top
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.clear_top
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                             in
                                                          let uu____1131 =
                                                            let uu____1134 =
                                                              FStar_Tactics_InterpFuns.mktac1
                                                                Prims.int_zero
                                                                "clear"
                                                                FStar_Tactics_Basic.clear
                                                                FStar_Reflection_Embeddings.e_binder
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.clear
                                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____1137 =
                                                              let uu____1140
                                                                =
                                                                FStar_Tactics_InterpFuns.mktac1
                                                                  Prims.int_zero
                                                                  "rewrite"
                                                                  FStar_Tactics_Basic.rewrite
                                                                  FStar_Reflection_Embeddings.e_binder
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Tactics_Basic.rewrite
                                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                 in
                                                              let uu____1143
                                                                =
                                                                let uu____1146
                                                                  =
                                                                  FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "refine_intro"
                                                                    FStar_Tactics_Basic.refine_intro
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.refine_intro
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                   in
                                                                let uu____1149
                                                                  =
                                                                  let uu____1152
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "t_exact"
                                                                    FStar_Tactics_Basic.t_exact
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_exact
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                  let uu____1159
                                                                    =
                                                                    let uu____1162
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_one
                                                                    "t_apply"
                                                                    FStar_Tactics_Basic.t_apply
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_apply
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1169
                                                                    =
                                                                    let uu____1172
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "apply_lemma"
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1175
                                                                    =
                                                                    let uu____1178
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "set_options"
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1183
                                                                    =
                                                                    let uu____1186
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "tcc"
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_comp
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_comp
                                                                     in
                                                                    let uu____1189
                                                                    =
                                                                    let uu____1192
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "tc"
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1195
                                                                    =
                                                                    let uu____1198
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "unshelve"
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1201
                                                                    =
                                                                    let uu____1204
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1209
                                                                     ->
                                                                    fun
                                                                    uu____1210
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1214
                                                                    =
                                                                    let uu____1217
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "prune"
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1222
                                                                    =
                                                                    let uu____1225
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "addns"
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1230
                                                                    =
                                                                    let uu____1233
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "print"
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1238
                                                                    =
                                                                    let uu____1241
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "debugging"
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1246
                                                                    =
                                                                    let uu____1249
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1254
                                                                    =
                                                                    let uu____1257
                                                                    =
                                                                    let uu____1258
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1263
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "t_pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1258
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1263
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1274
                                                                    =
                                                                    let uu____1277
                                                                    =
                                                                    let uu____1278
                                                                    =
                                                                    let uu____1291
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1291
                                                                     in
                                                                    let uu____1305
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1310
                                                                    =
                                                                    let uu____1323
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1323
                                                                     in
                                                                    let uu____1337
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1278
                                                                    uu____1305
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1310
                                                                    uu____1337
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1368
                                                                    =
                                                                    let uu____1371
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1374
                                                                    =
                                                                    let uu____1377
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1380
                                                                    =
                                                                    let uu____1383
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "tadmit_t"
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1386
                                                                    =
                                                                    let uu____1389
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "join"
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1392
                                                                    =
                                                                    let uu____1395
                                                                    =
                                                                    let uu____1396
                                                                    =
                                                                    let uu____1405
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1405
                                                                     in
                                                                    let uu____1416
                                                                    =
                                                                    let uu____1425
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1425
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1396
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1416
                                                                     in
                                                                    let uu____1450
                                                                    =
                                                                    let uu____1453
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                     in
                                                                    let uu____1456
                                                                    =
                                                                    let uu____1459
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                     in
                                                                    let uu____1462
                                                                    =
                                                                    let uu____1465
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1468
                                                                    =
                                                                    let uu____1471
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    let uu____1474
                                                                    =
                                                                    let uu____1477
                                                                    =
                                                                    let uu____1478
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1483
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1478
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1483
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1494
                                                                    =
                                                                    let uu____1497
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "unify_env"
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1502
                                                                    =
                                                                    let uu____1505
                                                                    =
                                                                    let uu____1506
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1513
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1506
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1513
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1534
                                                                    =
                                                                    let uu____1537
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_zero
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_bv
                                                                     in
                                                                    let uu____1542
                                                                    =
                                                                    let uu____1545
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1548
                                                                    =
                                                                    let uu____1551
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                     in
                                                                    let uu____1554
                                                                    =
                                                                    let uu____1557
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1560
                                                                    =
                                                                    let uu____1563
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    Prims.int_zero
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1568
                                                                    =
                                                                    let uu____1571
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1578
                                                                     ->
                                                                    fun
                                                                    uu____1579
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1582
                                                                    =
                                                                    let uu____1585
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    Prims.int_one
                                                                    "lset"
                                                                    FStar_Tactics_Basic.lset
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    (fun
                                                                    uu____1593
                                                                     ->
                                                                    fun
                                                                    uu____1594
                                                                     ->
                                                                    fun
                                                                    uu____1595
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____1585]
                                                                     in
                                                                    uu____1571
                                                                    ::
                                                                    uu____1582
                                                                     in
                                                                    uu____1563
                                                                    ::
                                                                    uu____1568
                                                                     in
                                                                    uu____1557
                                                                    ::
                                                                    uu____1560
                                                                     in
                                                                    uu____1551
                                                                    ::
                                                                    uu____1554
                                                                     in
                                                                    uu____1545
                                                                    ::
                                                                    uu____1548
                                                                     in
                                                                    uu____1537
                                                                    ::
                                                                    uu____1542
                                                                     in
                                                                    uu____1505
                                                                    ::
                                                                    uu____1534
                                                                     in
                                                                    uu____1497
                                                                    ::
                                                                    uu____1502
                                                                     in
                                                                    uu____1477
                                                                    ::
                                                                    uu____1494
                                                                     in
                                                                    uu____1471
                                                                    ::
                                                                    uu____1474
                                                                     in
                                                                    uu____1465
                                                                    ::
                                                                    uu____1468
                                                                     in
                                                                    uu____1459
                                                                    ::
                                                                    uu____1462
                                                                     in
                                                                    uu____1453
                                                                    ::
                                                                    uu____1456
                                                                     in
                                                                    uu____1395
                                                                    ::
                                                                    uu____1450
                                                                     in
                                                                    uu____1389
                                                                    ::
                                                                    uu____1392
                                                                     in
                                                                    uu____1383
                                                                    ::
                                                                    uu____1386
                                                                     in
                                                                    uu____1377
                                                                    ::
                                                                    uu____1380
                                                                     in
                                                                    uu____1371
                                                                    ::
                                                                    uu____1374
                                                                     in
                                                                    uu____1277
                                                                    ::
                                                                    uu____1368
                                                                     in
                                                                    uu____1257
                                                                    ::
                                                                    uu____1274
                                                                     in
                                                                    uu____1249
                                                                    ::
                                                                    uu____1254
                                                                     in
                                                                    uu____1241
                                                                    ::
                                                                    uu____1246
                                                                     in
                                                                    uu____1233
                                                                    ::
                                                                    uu____1238
                                                                     in
                                                                    uu____1225
                                                                    ::
                                                                    uu____1230
                                                                     in
                                                                    uu____1217
                                                                    ::
                                                                    uu____1222
                                                                     in
                                                                    uu____1204
                                                                    ::
                                                                    uu____1214
                                                                     in
                                                                    uu____1198
                                                                    ::
                                                                    uu____1201
                                                                     in
                                                                    uu____1192
                                                                    ::
                                                                    uu____1195
                                                                     in
                                                                    uu____1186
                                                                    ::
                                                                    uu____1189
                                                                     in
                                                                    uu____1178
                                                                    ::
                                                                    uu____1183
                                                                     in
                                                                    uu____1172
                                                                    ::
                                                                    uu____1175
                                                                     in
                                                                    uu____1162
                                                                    ::
                                                                    uu____1169
                                                                     in
                                                                  uu____1152
                                                                    ::
                                                                    uu____1159
                                                                   in
                                                                uu____1146 ::
                                                                  uu____1149
                                                                 in
                                                              uu____1140 ::
                                                                uu____1143
                                                               in
                                                            uu____1134 ::
                                                              uu____1137
                                                             in
                                                          uu____1128 ::
                                                            uu____1131
                                                           in
                                                        uu____1122 ::
                                                          uu____1125
                                                         in
                                                      uu____1116 ::
                                                        uu____1119
                                                       in
                                                    uu____1108 :: uu____1113
                                                     in
                                                  uu____1088 :: uu____1105
                                                   in
                                                uu____1068 :: uu____1085  in
                                              uu____1048 :: uu____1065  in
                                            uu____1020 :: uu____1045  in
                                          uu____1014 :: uu____1017  in
                                        uu____968 :: uu____1011  in
                                      uu____922 :: uu____965  in
                                    uu____916 :: uu____919  in
                                  uu____896 :: uu____913  in
                                uu____876 :: uu____893  in
                              uu____814 :: uu____873  in
                            uu____806 :: uu____811  in
                          uu____798 :: uu____803  in
                        uu____790 :: uu____795  in
                      uu____784 :: uu____787  in
                    uu____778 :: uu____781  in
                  uu____772 :: uu____775  in
                uu____752 :: uu____769  in
              uu____732 :: uu____749  in
            uu____726 :: uu____729  in
          uu____720 :: uu____723  in
        uu____714 :: uu____717  in
      uu____708 :: uu____711  in
    let uu____1598 =
      let uu____1601 = FStar_Tactics_InterpFuns.native_tactics_steps ()  in
      FStar_List.append FStar_Reflection_Interpreter.reflection_primops
        uu____1601
       in
    FStar_List.append uu____705 uu____1598

and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            'Aa -> 'Ar FStar_Tactics_Basic.tac
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          fun x  ->
            let rng = FStar_Range.dummyRange  in
            let x_tm = FStar_Tactics_InterpFuns.embed ea rng x ncb  in
            let app =
              let uu____1619 =
                let uu____1624 =
                  let uu____1625 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____1625]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1624  in
              uu____1619 FStar_Pervasives_Native.None rng  in
            unembed_tactic_0 er app ncb

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun embedded_tac_b  ->
      fun ncb  ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state  ->
             let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
             let embedded_tac_b1 = FStar_Syntax_Util.mk_reify embedded_tac_b
                in
             let tm =
               let uu____1675 =
                 let uu____1680 =
                   let uu____1681 =
                     let uu____1690 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1690  in
                   [uu____1681]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1680  in
               uu____1675 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1731 = FStar_Options.tactics_nbe ()  in
               if uu____1731
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             let result =
               let uu____1753 = primitive_steps ()  in
               norm_f uu____1753 steps
                 proof_state.FStar_Tactics_Types.main_context tm
                in
             let res =
               let uu____1761 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Tactics_InterpFuns.unembed uu____1761 result ncb  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1774 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1774
                   (fun uu____1778  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1783 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1783
                   (fun uu____1787  -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1790 =
                   let uu____1796 =
                     let uu____1798 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1798
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1796)  in
                 FStar_Errors.raise_error uu____1790
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

and unembed_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.nbe_cbs ->
          FStar_TypeChecker_NBETerm.t -> 'Aa -> 'Ar FStar_Tactics_Basic.tac
  =
  fun ea  ->
    fun er  ->
      fun cb  ->
        fun f  ->
          fun x  ->
            let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x  in
            let app =
              let uu____1815 =
                let uu____1816 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____1816]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1815  in
            unembed_tactic_nbe_0 er cb app

and unembed_tactic_nbe_0 :
  'Ab .
    'Ab FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun cb  ->
      fun embedded_tac_b  ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state  ->
             let result =
               let uu____1842 =
                 let uu____1843 =
                   let uu____1848 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1848  in
                 [uu____1843]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1842
                in
             let res =
               let uu____1862 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1862 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1875 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1875
                   (fun uu____1879  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____1884 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1884
                   (fun uu____1888  -> FStar_Tactics_Basic.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____1891 =
                   let uu____1897 =
                     let uu____1899 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1899
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1897)  in
                 FStar_Errors.raise_error uu____1891
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

and unembed_tactic_1_alt :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            ('Aa -> 'Ar FStar_Tactics_Basic.tac)
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          FStar_Pervasives_Native.Some
            (fun x  ->
               let rng = FStar_Range.dummyRange  in
               let x_tm = FStar_Tactics_InterpFuns.embed ea rng x ncb  in
               let app =
                 let uu____1929 =
                   let uu____1934 =
                     let uu____1935 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1935]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1934  in
                 uu____1929 FStar_Pervasives_Native.None rng  in
               unembed_tactic_0 er app ncb)

and e_tactic_1_alt :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa ->
           FStar_Tactics_Types.proofstate ->
             'Ar FStar_Tactics_Result.__result)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let em uu____1992 uu____1993 uu____1994 uu____1995 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n1 =
        let uu____2044 = unembed_tactic_1_alt ea er t0 n1  in
        match uu____2044 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2084 = f x  in FStar_Tactics_Basic.run uu____2084))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____2100 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____2100

let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____2140 =
               let uu____2142 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____2144 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2142 uu____2144 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2140, rng)) is
         in
      FStar_Errors.add_errors errs; FStar_Errors.stop_if_err ()
  
let (run_tactic_on_typ' :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.typ ->
            (FStar_Range.range ->
               FStar_TypeChecker_Env.env ->
                 (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
              ->
              (FStar_Tactics_Types.goal Prims.list *
                FStar_Syntax_Syntax.term))
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun typ  ->
            fun initial_proofstate  ->
              (let uu____2211 = FStar_ST.op_Bang tacdbg  in
               if uu____2211
               then
                 let uu____2235 = FStar_Syntax_Print.term_to_string tactic
                    in
                 FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____2235
               else ());
              (let uu____2240 = FStar_TypeChecker_TcTerm.tc_tactic env tactic
                  in
               match uu____2240 with
               | (uu____2253,uu____2254,g) ->
                   ((let uu____2257 = FStar_ST.op_Bang tacdbg  in
                     if uu____2257 then FStar_Util.print_string "}\n" else ());
                    FStar_TypeChecker_Rel.force_trivial_guard env g;
                    FStar_Errors.stop_if_err ();
                    (let tau =
                       unembed_tactic_1 FStar_Syntax_Embeddings.e_unit
                         FStar_Syntax_Embeddings.e_unit tactic
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let uu____2293 =
                       FStar_TypeChecker_Env.clear_expected_typ env  in
                     match uu____2293 with
                     | (env1,uu____2307) ->
                         let env2 =
                           let uu___190_2313 = env1  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___190_2313.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___190_2313.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___190_2313.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___190_2313.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___190_2313.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___190_2313.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___190_2313.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___190_2313.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___190_2313.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___190_2313.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___190_2313.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp = false;
                             FStar_TypeChecker_Env.effects =
                               (uu___190_2313.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___190_2313.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___190_2313.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___190_2313.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___190_2313.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___190_2313.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___190_2313.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___190_2313.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___190_2313.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___190_2313.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___190_2313.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___190_2313.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___190_2313.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___190_2313.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___190_2313.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___190_2313.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___190_2313.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___190_2313.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___190_2313.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___190_2313.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___190_2313.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___190_2313.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___190_2313.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___190_2313.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___190_2313.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___190_2313.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___190_2313.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___190_2313.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___190_2313.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___190_2313.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___190_2313.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___190_2313.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___190_2313.FStar_TypeChecker_Env.strict_args_tab)
                           }  in
                         let env3 =
                           let uu___193_2316 = env2  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___193_2316.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___193_2316.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___193_2316.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___193_2316.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___193_2316.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___193_2316.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___193_2316.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___193_2316.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___193_2316.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___193_2316.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___193_2316.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___193_2316.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___193_2316.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___193_2316.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___193_2316.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___193_2316.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___193_2316.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___193_2316.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___193_2316.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___193_2316.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___193_2316.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes = true;
                             FStar_TypeChecker_Env.phase1 =
                               (uu___193_2316.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___193_2316.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___193_2316.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___193_2316.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___193_2316.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___193_2316.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___193_2316.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___193_2316.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___193_2316.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___193_2316.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___193_2316.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___193_2316.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___193_2316.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___193_2316.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___193_2316.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___193_2316.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___193_2316.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___193_2316.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___193_2316.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___193_2316.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___193_2316.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___193_2316.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___193_2316.FStar_TypeChecker_Env.strict_args_tab)
                           }  in
                         let env4 =
                           let uu___196_2319 = env3  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___196_2319.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___196_2319.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___196_2319.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___196_2319.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___196_2319.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___196_2319.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___196_2319.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___196_2319.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___196_2319.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___196_2319.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___196_2319.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___196_2319.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___196_2319.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___196_2319.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___196_2319.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___196_2319.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___196_2319.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___196_2319.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___196_2319.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___196_2319.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___196_2319.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___196_2319.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___196_2319.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard = true;
                             FStar_TypeChecker_Env.nosynth =
                               (uu___196_2319.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___196_2319.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___196_2319.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___196_2319.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___196_2319.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___196_2319.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___196_2319.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___196_2319.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___196_2319.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___196_2319.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___196_2319.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___196_2319.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___196_2319.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___196_2319.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___196_2319.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___196_2319.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___196_2319.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___196_2319.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___196_2319.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___196_2319.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___196_2319.FStar_TypeChecker_Env.strict_args_tab)
                           }  in
                         let rng =
                           let uu____2322 = FStar_Range.use_range rng_goal
                              in
                           let uu____2323 = FStar_Range.use_range rng_tac  in
                           FStar_Range.range_of_rng uu____2322 uu____2323  in
                         let uu____2324 = initial_proofstate rng env4  in
                         (match uu____2324 with
                          | (ps,w) ->
                              (FStar_ST.op_Colon_Equals
                                 FStar_Reflection_Basic.env_hook
                                 (FStar_Pervasives_Native.Some env4);
                               (let uu____2362 = FStar_ST.op_Bang tacdbg  in
                                if uu____2362
                                then
                                  let uu____2386 =
                                    FStar_Syntax_Print.term_to_string typ  in
                                  FStar_Util.print1
                                    "Running tactic with goal = (%s) {\n"
                                    uu____2386
                                else ());
                               (let uu____2391 =
                                  FStar_Util.record_time
                                    (fun uu____2403  ->
                                       let uu____2404 = tau ()  in
                                       FStar_Tactics_Basic.run_safe
                                         uu____2404 ps)
                                   in
                                match uu____2391 with
                                | (res,ms) ->
                                    ((let uu____2422 =
                                        FStar_ST.op_Bang tacdbg  in
                                      if uu____2422
                                      then FStar_Util.print_string "}\n"
                                      else ());
                                     (let uu____2450 =
                                        (FStar_ST.op_Bang tacdbg) ||
                                          (FStar_Options.tactics_info ())
                                         in
                                      if uu____2450
                                      then
                                        let uu____2474 =
                                          FStar_Syntax_Print.term_to_string
                                            tactic
                                           in
                                        let uu____2476 =
                                          FStar_Util.string_of_int ms  in
                                        let uu____2478 =
                                          FStar_Syntax_Print.lid_to_string
                                            env4.FStar_TypeChecker_Env.curmodule
                                           in
                                        FStar_Util.print3
                                          "Tactic %s ran in %s ms (%s)\n"
                                          uu____2474 uu____2476 uu____2478
                                      else ());
                                     (match res with
                                      | FStar_Tactics_Result.Success
                                          (uu____2489,ps1) ->
                                          ((let uu____2492 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2492
                                            then
                                              let uu____2516 =
                                                FStar_Syntax_Print.term_to_string
                                                  w
                                                 in
                                              FStar_Util.print1
                                                "Tactic generated proofterm %s\n"
                                                uu____2516
                                            else ());
                                           FStar_List.iter
                                             (fun g1  ->
                                                let uu____2526 =
                                                  FStar_Tactics_Basic.is_irrelevant
                                                    g1
                                                   in
                                                if uu____2526
                                                then
                                                  let uu____2529 =
                                                    let uu____2531 =
                                                      FStar_Tactics_Types.goal_env
                                                        g1
                                                       in
                                                    let uu____2532 =
                                                      FStar_Tactics_Types.goal_witness
                                                        g1
                                                       in
                                                    FStar_TypeChecker_Rel.teq_nosmt_force
                                                      uu____2531 uu____2532
                                                      FStar_Syntax_Util.exp_unit
                                                     in
                                                  (if uu____2529
                                                   then ()
                                                   else
                                                     (let uu____2536 =
                                                        let uu____2538 =
                                                          let uu____2540 =
                                                            FStar_Tactics_Types.goal_witness
                                                              g1
                                                             in
                                                          FStar_Syntax_Print.term_to_string
                                                            uu____2540
                                                           in
                                                        FStar_Util.format1
                                                          "Irrelevant tactic witness does not unify with (): %s"
                                                          uu____2538
                                                         in
                                                      failwith uu____2536))
                                                else ())
                                             (FStar_List.append
                                                ps1.FStar_Tactics_Types.goals
                                                ps1.FStar_Tactics_Types.smt_goals);
                                           (let uu____2545 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2545
                                            then
                                              let uu____2569 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print1
                                                "About to check tactic implicits: %s\n"
                                                uu____2569
                                            else ());
                                           (let g1 =
                                              let uu___227_2577 =
                                                FStar_TypeChecker_Env.trivial_guard
                                                 in
                                              {
                                                FStar_TypeChecker_Env.guard_f
                                                  =
                                                  (uu___227_2577.FStar_TypeChecker_Env.guard_f);
                                                FStar_TypeChecker_Env.deferred
                                                  =
                                                  (uu___227_2577.FStar_TypeChecker_Env.deferred);
                                                FStar_TypeChecker_Env.univ_ineqs
                                                  =
                                                  (uu___227_2577.FStar_TypeChecker_Env.univ_ineqs);
                                                FStar_TypeChecker_Env.implicits
                                                  =
                                                  (ps1.FStar_Tactics_Types.all_implicits)
                                              }  in
                                            let g2 =
                                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                                env4 g1
                                               in
                                            (let uu____2580 =
                                               FStar_ST.op_Bang tacdbg  in
                                             if uu____2580
                                             then
                                               let uu____2604 =
                                                 FStar_Util.string_of_int
                                                   (FStar_List.length
                                                      ps1.FStar_Tactics_Types.all_implicits)
                                                  in
                                               let uu____2606 =
                                                 FStar_Common.string_of_list
                                                   (fun imp  ->
                                                      FStar_Syntax_Print.ctx_uvar_to_string
                                                        imp.FStar_TypeChecker_Env.imp_uvar)
                                                   ps1.FStar_Tactics_Types.all_implicits
                                                  in
                                               FStar_Util.print2
                                                 "Checked %s implicits (1): %s\n"
                                                 uu____2604 uu____2606
                                             else ());
                                            (let g3 =
                                               FStar_TypeChecker_Rel.resolve_implicits_tac
                                                 env4 g2
                                                in
                                             (let uu____2615 =
                                                FStar_ST.op_Bang tacdbg  in
                                              if uu____2615
                                              then
                                                let uu____2639 =
                                                  FStar_Util.string_of_int
                                                    (FStar_List.length
                                                       ps1.FStar_Tactics_Types.all_implicits)
                                                   in
                                                let uu____2641 =
                                                  FStar_Common.string_of_list
                                                    (fun imp  ->
                                                       FStar_Syntax_Print.ctx_uvar_to_string
                                                         imp.FStar_TypeChecker_Env.imp_uvar)
                                                    ps1.FStar_Tactics_Types.all_implicits
                                                   in
                                                FStar_Util.print2
                                                  "Checked %s implicits (2): %s\n"
                                                  uu____2639 uu____2641
                                              else ());
                                             report_implicits rng_goal
                                               g3.FStar_TypeChecker_Env.implicits;
                                             (let uu____2650 =
                                                FStar_ST.op_Bang tacdbg  in
                                              if uu____2650
                                              then
                                                let uu____2674 =
                                                  let uu____2675 =
                                                    FStar_TypeChecker_Cfg.psc_subst
                                                      ps1.FStar_Tactics_Types.psc
                                                     in
                                                  FStar_Tactics_Types.subst_proof_state
                                                    uu____2675 ps1
                                                   in
                                                FStar_Tactics_Basic.dump_proofstate
                                                  uu____2674
                                                  "at the finish line"
                                              else ());
                                             ((FStar_List.append
                                                 ps1.FStar_Tactics_Types.goals
                                                 ps1.FStar_Tactics_Types.smt_goals),
                                               w))))
                                      | FStar_Tactics_Result.Failed (e,ps1)
                                          ->
                                          ((let uu____2684 =
                                              let uu____2685 =
                                                FStar_TypeChecker_Cfg.psc_subst
                                                  ps1.FStar_Tactics_Types.psc
                                                 in
                                              FStar_Tactics_Types.subst_proof_state
                                                uu____2685 ps1
                                               in
                                            FStar_Tactics_Basic.dump_proofstate
                                              uu____2684
                                              "at the time of failure");
                                           (let texn_to_string e1 =
                                              match e1 with
                                              | FStar_Tactics_Types.TacticFailure
                                                  s -> s
                                              | FStar_Tactics_Types.EExn t ->
                                                  let uu____2698 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  Prims.op_Hat
                                                    "uncaught exception: "
                                                    uu____2698
                                              | e2 -> FStar_Exn.raise e2  in
                                            let uu____2703 =
                                              let uu____2709 =
                                                let uu____2711 =
                                                  texn_to_string e  in
                                                FStar_Util.format1
                                                  "user tactic failed: %s"
                                                  uu____2711
                                                 in
                                              (FStar_Errors.Fatal_UserTacticFailure,
                                                uu____2709)
                                               in
                                            FStar_Errors.raise_error
                                              uu____2703
                                              ps1.FStar_Tactics_Types.entry_range))))))))))
  
let (run_tactic_on_typ :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term ->
            (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term))
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun typ  ->
            run_tactic_on_typ' rng_tac rng_goal tactic env typ
              (fun rng  ->
                 fun env1  ->
                   FStar_Tactics_Basic.proofstate_of_goal_ty rng env1 typ)
  
let (run_tactic_on_all_implicits :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_TypeChecker_Env.implicits ->
            (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term))
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun imps  ->
            run_tactic_on_typ' rng_tac rng_goal tactic env
              FStar_Syntax_Syntax.t_unit
              (fun rng  ->
                 fun env1  ->
                   FStar_Tactics_Basic.proofstate_of_all_implicits rng env1
                     imps)
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2814 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2825 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2836 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a * FStar_Tactics_Types.goal Prims.list) 
  | Dual of ('a * 'a * FStar_Tactics_Types.goal Prims.list) 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2895 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2939 -> false
  
let __proj__Simplified__item___0 :
  'a . 'a tres_m -> ('a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2997 -> false
  
let __proj__Dual__item___0 :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____3040 . 'Auu____3040 -> 'Auu____3040 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3070 = FStar_Syntax_Util.head_and_args t  in
        match uu____3070 with
        | (hd1,args) ->
            let uu____3113 =
              let uu____3128 =
                let uu____3129 = FStar_Syntax_Util.un_uinst hd1  in
                uu____3129.FStar_Syntax_Syntax.n  in
              (uu____3128, args)  in
            (match uu____3113 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(tactic,FStar_Pervasives_Native.None )::(assertion,FStar_Pervasives_Native.None
                                                            )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3191 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3191 with
                       | (gs,uu____3199) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3206 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____3206 with
                       | (gs,uu____3214) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3257 =
                        let uu____3264 =
                          let uu____3267 =
                            let uu____3268 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3268
                             in
                          [uu____3267]  in
                        (FStar_Syntax_Util.t_true, uu____3264)  in
                      Simplified uu____3257
                  | Both  ->
                      let uu____3279 =
                        let uu____3288 =
                          let uu____3291 =
                            let uu____3292 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3292
                             in
                          [uu____3291]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____3288)  in
                      Dual uu____3279
                  | Neg  -> Simplified (assertion, []))
             | uu____3305 -> Unchanged t)
  
let explode :
  'a . 'a tres_m -> ('a * 'a * FStar_Tactics_Types.goal Prims.list) =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___0_3397  ->
      match uu___0_3397 with
      | Unchanged t -> let uu____3403 = f t  in Unchanged uu____3403
      | Simplified (t,gs) ->
          let uu____3410 = let uu____3417 = f t  in (uu____3417, gs)  in
          Simplified uu____3410
      | Dual (tn,tp,gs) ->
          let uu____3427 =
            let uu____3436 = f tn  in
            let uu____3437 = f tp  in (uu____3436, uu____3437, gs)  in
          Dual uu____3427
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3501 = f t1 t2  in Unchanged uu____3501
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3513 = let uu____3520 = f t1 t2  in (uu____3520, gs)
               in
            Simplified uu____3513
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3534 = let uu____3541 = f t1 t2  in (uu____3541, gs)
               in
            Simplified uu____3534
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3560 =
              let uu____3567 = f t1 t2  in
              (uu____3567, (FStar_List.append gs1 gs2))  in
            Simplified uu____3560
        | uu____3570 ->
            let uu____3579 = explode x  in
            (match uu____3579 with
             | (n1,p1,gs1) ->
                 let uu____3597 = explode y  in
                 (match uu____3597 with
                  | (n2,p2,gs2) ->
                      let uu____3615 =
                        let uu____3624 = f n1 n2  in
                        let uu____3625 = f p1 p2  in
                        (uu____3624, uu____3625, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3615))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3698 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3698
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3747  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3790 =
              let uu____3791 = FStar_Syntax_Subst.compress t  in
              uu____3791.FStar_Syntax_Syntax.n  in
            match uu____3790 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3803 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3803 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3829 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3829 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3849;
                   FStar_Syntax_Syntax.vars = uu____3850;_},(p,uu____3852)::
                 (q,uu____3854)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3912 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3912 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3926 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3926.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3930;
                   FStar_Syntax_Syntax.vars = uu____3931;_},(p,uu____3933)::
                 (q,uu____3935)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p
                   in
                let xq =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q
                   in
                let r1 =
                  let uu____3993 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3993 p  in
                let r2 =
                  let uu____3995 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3995 q  in
                (match (r1, r2) with
                 | (Unchanged uu____4002,Unchanged uu____4003) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____4021 = FStar_Syntax_Util.mk_iff l r  in
                            uu____4021.FStar_Syntax_Syntax.n) r1 r2
                 | uu____4024 ->
                     let uu____4033 = explode r1  in
                     (match uu____4033 with
                      | (pn,pp,gs1) ->
                          let uu____4051 = explode r2  in
                          (match uu____4051 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____4072 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____4075 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____4072
                                   uu____4075
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4139  ->
                       fun r  ->
                         match uu____4139 with
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
                let uu____4291 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____4291 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____4331  ->
                            match uu____4331 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____4353 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___499_4385 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___499_4385.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___499_4385.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____4353 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4413 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____4413.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4459 = traverse f pol e t1  in
                let uu____4464 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____4464 uu____4459
            | FStar_Syntax_Syntax.Tm_match (sc,brs) ->
                let uu____4539 = traverse f pol e sc  in
                let uu____4544 =
                  let uu____4563 =
                    FStar_List.map
                      (fun br  ->
                         let uu____4580 = FStar_Syntax_Subst.open_branch br
                            in
                         match uu____4580 with
                         | (pat,w,exp) ->
                             let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                             let e1 = FStar_TypeChecker_Env.push_bvs e bvs
                                in
                             let r = traverse f pol e1 exp  in
                             let uu____4607 =
                               comb1
                                 (fun exp1  ->
                                    FStar_Syntax_Subst.close_branch
                                      (pat, w, exp1))
                                in
                             uu____4607 r) brs
                     in
                  comb_list uu____4563  in
                comb2
                  (fun sc1  ->
                     fun brs1  -> FStar_Syntax_Syntax.Tm_match (sc1, brs1))
                  uu____4539 uu____4544
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___531_4693 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___531_4693.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___531_4693.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4700 =
                f pol e
                  (let uu___537_4704 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___537_4704.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___537_4704.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____4700
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___544_4714 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___544_4714.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___544_4714.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____4715 = explode rp  in
              (match uu____4715 with
               | (uu____4724,p',gs') ->
                   Dual
                     ((let uu___551_4734 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___551_4734.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___551_4734.FStar_Syntax_Syntax.vars)
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
          [FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant] e t
         in
      FStar_Syntax_Util.un_squash tn
  
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
        FStar_Options.optionstate) Prims.list)
  =
  fun env  ->
    fun goal  ->
      (let uu____4779 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4779);
      (let uu____4804 = FStar_ST.op_Bang tacdbg  in
       if uu____4804
       then
         let uu____4828 =
           let uu____4830 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4830
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4833 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4828
           uu____4833
       else ());
      (let initial = (Prims.int_one, [])  in
       let uu____4868 =
         let uu____4877 = traverse by_tactic_interp Pos env goal  in
         match uu____4877 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4901 -> failwith "no"  in
       match uu____4868 with
       | (t',gs) ->
           ((let uu____4930 = FStar_ST.op_Bang tacdbg  in
             if uu____4930
             then
               let uu____4954 =
                 let uu____4956 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4956
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4959 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4954 uu____4959
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____5014  ->
                    fun g  ->
                      match uu____5014 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____5063 =
                              let uu____5066 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____5067 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____5066 uu____5067  in
                            match uu____5063 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____5068 =
                                  let uu____5074 =
                                    let uu____5076 =
                                      let uu____5078 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____5078
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____5076
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____5074)
                                   in
                                FStar_Errors.raise_error uu____5068
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____5083 = FStar_ST.op_Bang tacdbg  in
                            if uu____5083
                            then
                              let uu____5107 = FStar_Util.string_of_int n1
                                 in
                              let uu____5109 =
                                let uu____5111 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____5111
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____5107 uu____5109
                            else ());
                           (let label1 =
                              let uu____5117 =
                                let uu____5119 =
                                  FStar_Tactics_Types.get_label g  in
                                uu____5119 = ""  in
                              if uu____5117
                              then
                                let uu____5125 = FStar_Util.string_of_int n1
                                   in
                                Prims.op_Hat "Could not prove goal #"
                                  uu____5125
                              else
                                (let uu____5130 =
                                   let uu____5132 =
                                     FStar_Util.string_of_int n1  in
                                   let uu____5134 =
                                     let uu____5136 =
                                       let uu____5138 =
                                         FStar_Tactics_Types.get_label g  in
                                       Prims.op_Hat uu____5138 ")"  in
                                     Prims.op_Hat " (" uu____5136  in
                                   Prims.op_Hat uu____5132 uu____5134  in
                                 Prims.op_Hat "Could not prove goal #"
                                   uu____5130)
                               in
                            let gt' =
                              FStar_TypeChecker_Util.label label1
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____5144 =
                              let uu____5153 =
                                let uu____5160 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____5160, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____5153 :: gs1  in
                            ((n1 + Prims.int_one), uu____5144)))) s gs
                in
             let uu____5177 = s1  in
             match uu____5177 with
             | (uu____5199,gs1) ->
                 let uu____5219 =
                   let uu____5226 = FStar_Options.peek ()  in
                   (env, t', uu____5226)  in
                 uu____5219 :: gs1)))
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        if env.FStar_TypeChecker_Env.nosynth
        then
          let uu____5250 =
            let uu____5255 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____5256 =
              let uu____5257 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5257]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____5255 uu____5256  in
          uu____5250 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____5285 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____5285);
           (let uu____5309 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____5309 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____5330 =
                        let uu____5333 = FStar_Tactics_Types.goal_env g  in
                        let uu____5334 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____5333 uu____5334  in
                      match uu____5330 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____5337 = FStar_ST.op_Bang tacdbg  in
                            if uu____5337
                            then
                              let uu____5361 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____5361
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____5376 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____5376 guard))
                      | FStar_Pervasives_Native.None  ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                              "synthesis left open goals")
                            typ.FStar_Syntax_Syntax.pos) gs;
                 w)))
  
let (solve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.implicits -> unit)
  =
  fun env  ->
    fun tau  ->
      fun imps  ->
        (let uu____5396 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
         FStar_ST.op_Colon_Equals tacdbg uu____5396);
        (let uu____5420 =
           let uu____5427 = FStar_TypeChecker_Env.get_range env  in
           run_tactic_on_all_implicits tau.FStar_Syntax_Syntax.pos uu____5427
             tau env imps
            in
         match uu____5420 with
         | (gs,w) ->
             FStar_All.pipe_right gs
               (FStar_List.iter
                  (fun g  ->
                     let uu____5444 =
                       let uu____5447 = FStar_Tactics_Types.goal_env g  in
                       let uu____5448 = FStar_Tactics_Types.goal_type g  in
                       getprop uu____5447 uu____5448  in
                     match uu____5444 with
                     | FStar_Pervasives_Native.Some vc ->
                         ((let uu____5451 = FStar_ST.op_Bang tacdbg  in
                           if uu____5451
                           then
                             let uu____5475 =
                               FStar_Syntax_Print.term_to_string vc  in
                             FStar_Util.print1 "Synthesis left a goal: %s\n"
                               uu____5475
                           else ());
                          (let guard =
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (FStar_TypeChecker_Common.NonTrivial vc);
                               FStar_TypeChecker_Env.deferred = [];
                               FStar_TypeChecker_Env.univ_ineqs = ([], []);
                               FStar_TypeChecker_Env.implicits = []
                             }  in
                           let uu____5490 = FStar_Tactics_Types.goal_env g
                              in
                           FStar_TypeChecker_Rel.force_trivial_guard
                             uu____5490 guard))
                     | FStar_Pervasives_Native.None  ->
                         let uu____5491 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                             "synthesis left open goals") uu____5491)))
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      if env.FStar_TypeChecker_Env.nosynth
      then []
      else
        ((let uu____5513 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____5513);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____5538 =
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos tau env typ
             in
          match uu____5538 with
          | (gs,w) ->
              ((let uu____5554 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____5559 =
                         let uu____5561 =
                           let uu____5564 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____5565 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____5564 uu____5565  in
                         FStar_Option.isSome uu____5561  in
                       Prims.op_Negation uu____5559) gs
                   in
                if uu____5554
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                      "splice left open goals") typ.FStar_Syntax_Syntax.pos
                else ());
               (let w1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Weak;
                    FStar_TypeChecker_Env.HNF;
                    FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant;
                    FStar_TypeChecker_Env.Primops;
                    FStar_TypeChecker_Env.Unascribe;
                    FStar_TypeChecker_Env.Unmeta] env w
                   in
                (let uu____5573 = FStar_ST.op_Bang tacdbg  in
                 if uu____5573
                 then
                   let uu____5597 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____5597
                 else ());
                (let uu____5602 =
                   let uu____5607 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____5607 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____5602 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  
let (postprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun tau  ->
      fun typ  ->
        fun tm  ->
          if env.FStar_TypeChecker_Env.nosynth
          then tm
          else
            ((let uu____5652 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")
                 in
              FStar_ST.op_Colon_Equals tacdbg uu____5652);
             (let uu____5676 =
                FStar_TypeChecker_Env.new_implicit_var_aux "postprocess RHS"
                  tm.FStar_Syntax_Syntax.pos env typ
                  FStar_Syntax_Syntax.Allow_untyped
                  FStar_Pervasives_Native.None
                 in
              match uu____5676 with
              | (uvtm,uu____5695,g_imp) ->
                  let u = env.FStar_TypeChecker_Env.universe_of env typ  in
                  let goal =
                    let uu____5713 = FStar_Syntax_Util.mk_eq2 u typ tm uvtm
                       in
                    FStar_Syntax_Util.mk_squash u uu____5713  in
                  let uu____5714 =
                    run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                      tm.FStar_Syntax_Syntax.pos tau env goal
                     in
                  (match uu____5714 with
                   | (gs,w) ->
                       (FStar_List.iter
                          (fun g  ->
                             let uu____5735 =
                               let uu____5738 =
                                 FStar_Tactics_Types.goal_env g  in
                               let uu____5739 =
                                 FStar_Tactics_Types.goal_type g  in
                               getprop uu____5738 uu____5739  in
                             match uu____5735 with
                             | FStar_Pervasives_Native.Some vc ->
                                 ((let uu____5742 = FStar_ST.op_Bang tacdbg
                                      in
                                   if uu____5742
                                   then
                                     let uu____5766 =
                                       FStar_Syntax_Print.term_to_string vc
                                        in
                                     FStar_Util.print1
                                       "Postprocessing left a goal: %s\n"
                                       uu____5766
                                   else ());
                                  (let guard =
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         (FStar_TypeChecker_Common.NonTrivial
                                            vc);
                                       FStar_TypeChecker_Env.deferred = [];
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         ([], []);
                                       FStar_TypeChecker_Env.implicits = []
                                     }  in
                                   let uu____5781 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     uu____5781 guard))
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Errors.raise_error
                                   (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                                     "postprocessing left open goals")
                                   typ.FStar_Syntax_Syntax.pos) gs;
                        (let g_imp1 =
                           FStar_TypeChecker_Rel.resolve_implicits_tac env
                             g_imp
                            in
                         report_implicits tm.FStar_Syntax_Syntax.pos
                           g_imp1.FStar_TypeChecker_Env.implicits;
                         uvtm)))))
  