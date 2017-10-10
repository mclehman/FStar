open Prims
let embed_binder: FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term =
  fun b  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_binder b
      "reflection.embed_binder" FStar_Pervasives_Native.None
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let uu____9 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____9 FStar_Dyn.undyn
let embed_binders:
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  ->
    FStar_Syntax_Embeddings.embed_list embed_binder
      FStar_Reflection_Data.fstar_refl_binder l
let unembed_binders:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> FStar_Syntax_Embeddings.unembed_list unembed_binder t
let embed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_meta
         (FStar_Syntax_Syntax.tun, (FStar_Syntax_Syntax.Meta_quoted (t, ()))))
      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
let rec unembed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____32 =
      let uu____33 = FStar_Syntax_Subst.compress t in
      uu____33.FStar_Syntax_Syntax.n in
    match uu____32 with
    | FStar_Syntax_Syntax.Tm_meta
        ({ FStar_Syntax_Syntax.n = uu____36;
           FStar_Syntax_Syntax.pos = uu____37;
           FStar_Syntax_Syntax.vars = uu____38;_},FStar_Syntax_Syntax.Meta_quoted
         (qt,qi))
        -> qt
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____50) -> unembed_term t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____56,uu____57) ->
        unembed_term t1
    | uu____98 ->
        let uu____99 =
          let uu____100 =
            let uu____105 =
              let uu____106 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.format1 "Not an embedded term: %s" uu____106 in
            (uu____105, (t.FStar_Syntax_Syntax.pos)) in
          FStar_Errors.Error uu____100 in
        FStar_Exn.raise uu____99
let embed_fvar: FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_fvar fv
      "reflection.embed_fvar" FStar_Pervasives_Native.None
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____115 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____115 FStar_Dyn.undyn
let embed_comp: FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term =
  fun c  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_comp c
      "reflection.embed_comp" FStar_Pervasives_Native.None
let unembed_comp: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp =
  fun t  ->
    let uu____124 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____124 FStar_Dyn.undyn
let embed_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien FStar_Reflection_Data.fstar_refl_env env
      "tactics_embed_env" FStar_Pervasives_Native.None
let unembed_env: FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env =
  fun t  ->
    let uu____133 = FStar_Syntax_Util.un_alien t in
    FStar_All.pipe_right uu____133 FStar_Dyn.undyn
let embed_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
    | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
    | FStar_Reflection_Data.C_Int i ->
        let uu____139 =
          let uu____140 =
            let uu____141 =
              let uu____142 =
                let uu____143 = FStar_Util.string_of_int i in
                FStar_Syntax_Util.exp_int uu____143 in
              FStar_Syntax_Syntax.as_arg uu____142 in
            [uu____141] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____140 in
        uu____139 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_String s ->
        let uu____147 =
          let uu____148 =
            let uu____149 =
              let uu____150 = FStar_Syntax_Embeddings.embed_string s in
              FStar_Syntax_Syntax.as_arg uu____150 in
            [uu____149] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String
            uu____148 in
        uu____147 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____158 = FStar_Syntax_Util.head_and_args t1 in
    match uu____158 with
    | (hd1,args) ->
        let uu____195 =
          let uu____208 =
            let uu____209 = FStar_Syntax_Util.un_uinst hd1 in
            uu____209.FStar_Syntax_Syntax.n in
          (uu____208, args) in
        (match uu____195 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit_lid
             -> FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True_lid
             -> FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False_lid
             -> FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____267)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____292 = FStar_Syntax_Embeddings.unembed_int i in
             FStar_Reflection_Data.C_Int uu____292
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____295)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____320 = FStar_Syntax_Embeddings.unembed_string s in
             FStar_Reflection_Data.C_String uu____320
         | uu____321 -> failwith "not an embedded vconst")
let rec embed_pattern:
  FStar_Reflection_Data.pattern -> FStar_Syntax_Syntax.term =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____339 =
          let uu____340 =
            let uu____341 =
              let uu____342 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____342 in
            [uu____341] in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____340 in
        uu____339 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____351 =
          let uu____352 =
            let uu____353 =
              let uu____354 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____354 in
            let uu____355 =
              let uu____358 =
                let uu____359 =
                  FStar_Syntax_Embeddings.embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps in
                FStar_Syntax_Syntax.as_arg uu____359 in
              [uu____358] in
            uu____353 :: uu____355 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____352 in
        uu____351 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____363 =
          let uu____364 =
            let uu____365 =
              let uu____366 =
                let uu____367 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____367 in
              FStar_Syntax_Syntax.as_arg uu____366 in
            [uu____365] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____364 in
        uu____363 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____371 =
          let uu____372 =
            let uu____373 =
              let uu____374 =
                let uu____375 = FStar_Syntax_Syntax.mk_binder bv in
                embed_binder uu____375 in
              FStar_Syntax_Syntax.as_arg uu____374 in
            [uu____373] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____372 in
        uu____371 FStar_Pervasives_Native.None FStar_Range.dummyRange
let rec unembed_pattern:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____383 = FStar_Syntax_Util.head_and_args t1 in
    match uu____383 with
    | (hd1,args) ->
        let uu____420 =
          let uu____433 =
            let uu____434 = FStar_Syntax_Util.un_uinst hd1 in
            uu____434.FStar_Syntax_Syntax.n in
          (uu____433, args) in
        (match uu____420 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____447)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____472 = unembed_const c in
             FStar_Reflection_Data.Pat_Constant uu____472
         | (FStar_Syntax_Syntax.Tm_fvar fv,(f,uu____475)::(ps,uu____477)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____512 =
               let uu____519 = unembed_fvar f in
               let uu____520 =
                 FStar_Syntax_Embeddings.unembed_list unembed_pattern ps in
               (uu____519, uu____520) in
             FStar_Reflection_Data.Pat_Cons uu____512
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____527)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____552 =
               let uu____553 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____553 in
             FStar_Reflection_Data.Pat_Var uu____552
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____560)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____585 =
               let uu____586 = unembed_binder b in
               FStar_Pervasives_Native.fst uu____586 in
             FStar_Reflection_Data.Pat_Wild uu____585
         | uu____591 -> failwith "not an embedded pattern")
let embed_branch:
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  FStar_Syntax_Embeddings.embed_pair embed_pattern
    FStar_Reflection_Data.fstar_refl_pattern embed_term
    FStar_Syntax_Syntax.t_term
let unembed_branch:
  FStar_Syntax_Syntax.term ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = FStar_Syntax_Embeddings.unembed_pair unembed_pattern unembed_term
let embed_aqualv: FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.term =
  fun q  ->
    match q with
    | FStar_Reflection_Data.Q_Explicit  ->
        FStar_Reflection_Data.ref_Q_Explicit
    | FStar_Reflection_Data.Q_Implicit  ->
        FStar_Reflection_Data.ref_Q_Implicit
let unembed_aqualv: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.aqualv
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____627 = FStar_Syntax_Util.head_and_args t1 in
    match uu____627 with
    | (hd1,args) ->
        let uu____664 =
          let uu____677 =
            let uu____678 = FStar_Syntax_Util.un_uinst hd1 in
            uu____678.FStar_Syntax_Syntax.n in
          (uu____677, args) in
        (match uu____664 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Explicit_lid
             -> FStar_Reflection_Data.Q_Explicit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Q_Implicit_lid
             -> FStar_Reflection_Data.Q_Implicit
         | uu____719 -> failwith "not an embedded aqualv")
let embed_argv:
  (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  FStar_Syntax_Embeddings.embed_pair embed_term FStar_Syntax_Syntax.t_term
    embed_aqualv FStar_Reflection_Data.fstar_refl_aqualv
let unembed_argv:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Reflection_Data.aqualv)
      FStar_Pervasives_Native.tuple2
  = FStar_Syntax_Embeddings.unembed_pair unembed_term unembed_aqualv
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____751 =
          let uu____752 =
            let uu____753 =
              let uu____754 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____754 in
            [uu____753] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____752 in
        uu____751 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____758 =
          let uu____759 =
            let uu____760 =
              let uu____761 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____761 in
            [uu____760] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____759 in
        uu____758 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____766 =
          let uu____767 =
            let uu____768 =
              let uu____769 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____769 in
            let uu____770 =
              let uu____773 =
                let uu____774 = embed_argv a in
                FStar_Syntax_Syntax.as_arg uu____774 in
              [uu____773] in
            uu____768 :: uu____770 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____767 in
        uu____766 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____779 =
          let uu____780 =
            let uu____781 =
              let uu____782 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____782 in
            let uu____783 =
              let uu____786 =
                let uu____787 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____787 in
              [uu____786] in
            uu____781 :: uu____783 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____780 in
        uu____779 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____792 =
          let uu____793 =
            let uu____794 =
              let uu____795 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____795 in
            let uu____796 =
              let uu____799 =
                let uu____800 = embed_comp c in
                FStar_Syntax_Syntax.as_arg uu____800 in
              [uu____799] in
            uu____794 :: uu____796 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____793 in
        uu____792 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____804 =
          let uu____805 =
            let uu____806 =
              let uu____807 = FStar_Syntax_Embeddings.embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____807 in
            [uu____806] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____805 in
        uu____804 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____812 =
          let uu____813 =
            let uu____814 =
              let uu____815 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____815 in
            let uu____816 =
              let uu____819 =
                let uu____820 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____820 in
              [uu____819] in
            uu____814 :: uu____816 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____813 in
        uu____812 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____824 =
          let uu____825 =
            let uu____826 =
              let uu____827 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____827 in
            [uu____826] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____825 in
        uu____824 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____832 =
          let uu____833 =
            let uu____834 =
              let uu____835 = FStar_Syntax_Embeddings.embed_int u in
              FStar_Syntax_Syntax.as_arg uu____835 in
            let uu____836 =
              let uu____839 =
                let uu____840 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____840 in
              [uu____839] in
            uu____834 :: uu____836 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____833 in
        uu____832 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let uu____846 =
          let uu____847 =
            let uu____848 =
              let uu____849 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____849 in
            let uu____850 =
              let uu____853 =
                let uu____854 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____854 in
              let uu____855 =
                let uu____858 =
                  let uu____859 = embed_term t2 in
                  FStar_Syntax_Syntax.as_arg uu____859 in
                [uu____858] in
              uu____853 :: uu____855 in
            uu____848 :: uu____850 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let
            uu____847 in
        uu____846 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____868 =
          let uu____869 =
            let uu____870 =
              let uu____871 = embed_term t1 in
              FStar_Syntax_Syntax.as_arg uu____871 in
            let uu____872 =
              let uu____875 =
                let uu____876 =
                  FStar_Syntax_Embeddings.embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs in
                FStar_Syntax_Syntax.as_arg uu____876 in
              [uu____875] in
            uu____870 :: uu____872 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____869 in
        uu____868 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____888 = FStar_Syntax_Util.head_and_args t1 in
    match uu____888 with
    | (hd1,args) ->
        let uu____925 =
          let uu____938 =
            let uu____939 = FStar_Syntax_Util.un_uinst hd1 in
            uu____939.FStar_Syntax_Syntax.n in
          (uu____938, args) in
        (match uu____925 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____952)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____977 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____977
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____980)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1005 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1005
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1008)::(r,uu____1010)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1045 =
               let uu____1050 = unembed_term l in
               let uu____1051 = unembed_argv r in (uu____1050, uu____1051) in
             FStar_Reflection_Data.Tv_App uu____1045
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1062)::(t2,uu____1064)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1099 =
               let uu____1104 = unembed_binder b in
               let uu____1105 = unembed_term t2 in (uu____1104, uu____1105) in
             FStar_Reflection_Data.Tv_Abs uu____1099
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1108)::(t2,uu____1110)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1145 =
               let uu____1150 = unembed_binder b in
               let uu____1151 = unembed_comp t2 in (uu____1150, uu____1151) in
             FStar_Reflection_Data.Tv_Arrow uu____1145
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1154)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             ->
             (FStar_Syntax_Embeddings.unembed_unit u;
              FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1182)::(t2,uu____1184)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1219 =
               let uu____1224 = unembed_binder b in
               let uu____1225 = unembed_term t2 in (uu____1224, uu____1225) in
             FStar_Reflection_Data.Tv_Refine uu____1219
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1228)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1253 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1253
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1256)::(t2,uu____1258)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____1293 =
               let uu____1298 = FStar_Syntax_Embeddings.unembed_int u in
               let uu____1299 = unembed_term t2 in (uu____1298, uu____1299) in
             FStar_Reflection_Data.Tv_Uvar uu____1293
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1302)::(t11,uu____1304)::(t2,uu____1306)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Let_lid
             ->
             let uu____1351 =
               let uu____1358 = unembed_binder b in
               let uu____1359 = unembed_term t11 in
               let uu____1360 = unembed_term t2 in
               (uu____1358, uu____1359, uu____1360) in
             FStar_Reflection_Data.Tv_Let uu____1351
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____1363)::(brs,uu____1365)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____1400 =
               let uu____1407 = unembed_term t2 in
               let uu____1408 =
                 FStar_Syntax_Embeddings.unembed_list unembed_branch brs in
               (uu____1407, uu____1408) in
             FStar_Reflection_Data.Tv_Match uu____1400
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1440 -> failwith "not an embedded term_view")
let embed_comp_view:
  FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.term =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t ->
        let uu____1458 =
          let uu____1459 =
            let uu____1460 =
              let uu____1461 = embed_term t in
              FStar_Syntax_Syntax.as_arg uu____1461 in
            [uu____1460] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Total
            uu____1459 in
        uu____1458 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_Lemma (pre,post) ->
        let uu____1466 =
          let uu____1467 =
            let uu____1468 =
              let uu____1469 = embed_term pre in
              FStar_Syntax_Syntax.as_arg uu____1469 in
            let uu____1470 =
              let uu____1473 =
                let uu____1474 = embed_term post in
                FStar_Syntax_Syntax.as_arg uu____1474 in
              [uu____1473] in
            uu____1468 :: uu____1470 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Lemma
            uu____1467 in
        uu____1466 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_Unknown  -> FStar_Reflection_Data.ref_C_Unknown
let unembed_comp_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.comp_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1482 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1482 with
    | (hd1,args) ->
        let uu____1519 =
          let uu____1532 =
            let uu____1533 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1533.FStar_Syntax_Syntax.n in
          (uu____1532, args) in
        (match uu____1519 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(t2,uu____1546)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Total_lid
             ->
             let uu____1571 = unembed_term t2 in
             FStar_Reflection_Data.C_Total uu____1571
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(pre,uu____1574)::(post,uu____1576)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Lemma_lid
             ->
             let uu____1611 =
               let uu____1616 = unembed_term pre in
               let uu____1617 = unembed_term post in (uu____1616, uu____1617) in
             FStar_Reflection_Data.C_Lemma uu____1611
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unknown_lid
             -> FStar_Reflection_Data.C_Unknown
         | uu____1633 -> failwith "not an embedded comp_view")
let rec last: 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____1660::xs -> last xs
let rec init: 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____1686 = init xs in x :: uu____1686
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1697 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1697
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1706 = FStar_Parser_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1706
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)
let inspect_const: FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst
  =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____1716) ->
        let uu____1729 = FStar_Util.int_of_string s in
        FStar_Reflection_Data.C_Int uu____1729
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s,uu____1731) ->
        FStar_Reflection_Data.C_String s
    | uu____1732 ->
        let uu____1733 =
          let uu____1734 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____1734 in
        failwith uu____1733
let rec inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____1742) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1748 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1748
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1791 = last args in
        (match uu____1791 with
         | (a,q) ->
             let q' =
               match q with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                   uu____1811) -> FStar_Reflection_Data.Q_Implicit
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )
                   -> FStar_Reflection_Data.Q_Explicit
               | FStar_Pervasives_Native.None  ->
                   FStar_Reflection_Data.Q_Explicit in
             let uu____1812 =
               let uu____1817 =
                 let uu____1820 =
                   let uu____1821 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1821 in
                 uu____1820 FStar_Pervasives_Native.None
                   t2.FStar_Syntax_Syntax.pos in
               (uu____1817, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____1812)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1840,uu____1841) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____1883 = FStar_Syntax_Subst.open_term bs t3 in
        (match uu____1883 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1910 =
                    let uu____1915 = FStar_Syntax_Util.abs bs2 t4 k in
                    (b, uu____1915) in
                  FStar_Reflection_Data.Tv_Abs uu____1910))
    | FStar_Syntax_Syntax.Tm_type uu____1920 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____1936 ->
        let uu____1949 = FStar_Syntax_Util.arrow_one t2 in
        (match uu____1949 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1973 = FStar_Syntax_Subst.open_term [b] t3 in
        (match uu____1973 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2002 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t4))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2012 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____2012
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____2039 =
          let uu____2044 = FStar_Syntax_Unionfind.uvar_id u in
          (uu____2044, t3) in
        FStar_Reflection_Data.Tv_Uvar uu____2039
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____2064 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____2067 = FStar_Syntax_Subst.open_term [b] t21 in
               (match uu____2067 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____2096 ->
                          failwith
                            "impossible: open_term returned different amount of binders" in
                    FStar_Reflection_Data.Tv_Let
                      (b1, (lb.FStar_Syntax_Syntax.lbdef), t22)))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2154 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____2154
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2173 =
                let uu____2180 =
                  FStar_List.map
                    (fun uu____2192  ->
                       match uu____2192 with
                       | (p1,uu____2200) -> inspect_pat p1) ps in
                (fv, uu____2180) in
              FStar_Reflection_Data.Pat_Cons uu____2173
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2209 ->
              failwith "NYI: Pat_dot_term" in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
        let brs2 =
          FStar_List.map
            (fun uu___103_2253  ->
               match uu___103_2253 with
               | (pat,uu____2275,t4) ->
                   let uu____2293 = inspect_pat pat in (uu____2293, t4)) brs1 in
        FStar_Reflection_Data.Tv_Match (t3, brs2)
    | uu____2306 ->
        ((let uu____2308 = FStar_Syntax_Print.tag_of_term t2 in
          let uu____2309 = FStar_Syntax_Print.term_to_string t2 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2308 uu____2309);
         FStar_Reflection_Data.Tv_Unknown)
let inspect_comp: FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____2315) ->
        FStar_Reflection_Data.C_Total t
    | FStar_Syntax_Syntax.Comp ct ->
        if
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre,uu____2326)::(post,uu____2328)::uu____2329 ->
               FStar_Reflection_Data.C_Lemma (pre, post)
           | uu____2362 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else FStar_Reflection_Data.C_Unknown
    | FStar_Syntax_Syntax.GTotal uu____2372 ->
        FStar_Reflection_Data.C_Unknown
let pack_comp: FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp =
  fun cv  ->
    match cv with
    | FStar_Reflection_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | uu____2386 ->
        failwith "sorry, can embed comp_views other than C_Total for now"
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2392 =
          let uu____2403 = FStar_Util.string_of_int i in
          (uu____2403, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____2392
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2420) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        (match q with
         | FStar_Reflection_Data.Q_Explicit  ->
             let uu____2429 =
               let uu____2438 = FStar_Syntax_Syntax.as_arg r in [uu____2438] in
             FStar_Syntax_Util.mk_app l uu____2429
         | FStar_Reflection_Data.Q_Implicit  ->
             let uu____2439 =
               let uu____2448 = FStar_Syntax_Syntax.iarg r in [uu____2448] in
             FStar_Syntax_Util.mk_app l uu____2439)
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,c) -> FStar_Syntax_Util.arrow [b] c
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2454),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2461 =
          let uu____2464 =
            let uu____2465 = pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____2465 in
          FStar_Syntax_Syntax.mk uu____2464 in
        uu____2461 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        FStar_Syntax_Util.uvar_from_id u t
    | FStar_Reflection_Data.Tv_Let (b,t1,t2) ->
        let bv = FStar_Pervasives_Native.fst b in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 in
        let uu____2476 =
          let uu____2479 =
            let uu____2480 =
              let uu____2493 = FStar_Syntax_Subst.close [b] t2 in
              ((false, [lb]), uu____2493) in
            FStar_Syntax_Syntax.Tm_let uu____2480 in
          FStar_Syntax_Syntax.mk uu____2479 in
        uu____2476 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2522 =
                let uu____2523 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____2523 in
              FStar_All.pipe_left wrap uu____2522
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2532 =
                let uu____2533 =
                  let uu____2546 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2560 = pack_pat p1 in (uu____2560, false))
                      ps in
                  (fv, uu____2546) in
                FStar_Syntax_Syntax.Pat_cons uu____2533 in
              FStar_All.pipe_left wrap uu____2532
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv) in
        let brs1 =
          FStar_List.map
            (fun uu___104_2606  ->
               match uu___104_2606 with
               | (pat,t1) ->
                   let uu____2623 = pack_pat pat in
                   (uu____2623, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        failwith "pack: unexpected term view"
let embed_order: FStar_Order.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Order.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Order.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Order.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Order.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____2644 = FStar_Syntax_Util.head_and_args t1 in
    match uu____2644 with
    | (hd1,args) ->
        let uu____2681 =
          let uu____2694 =
            let uu____2695 = FStar_Syntax_Util.un_uinst hd1 in
            uu____2695.FStar_Syntax_Syntax.n in
          (uu____2694, args) in
        (match uu____2681 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Order.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Order.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Order.Gt
         | uu____2751 -> failwith "not an embedded order")
let compare_binder:
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Order.order
  =
  fun x  ->
    fun y  ->
      let n1 =
        FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x)
          (FStar_Pervasives_Native.fst y) in
      if n1 < (Prims.parse_int "0")
      then FStar_Order.Lt
      else
        if n1 = (Prims.parse_int "0") then FStar_Order.Eq else FStar_Order.Gt
let is_free:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    fun t  -> FStar_Syntax_Util.is_free_in (FStar_Pervasives_Native.fst x) t
let lookup_typ:
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list -> FStar_Reflection_Data.sigelt_view
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns in
      let res = FStar_TypeChecker_Env.lookup_qname env lid in
      match res with
      | FStar_Pervasives_Native.None  -> FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____2835,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____2936,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1 in
               let ctor1 dc_lid =
                 let uu____2953 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid in
                 match uu____2953 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3026,n1,uu____3028) ->
                          let uu____3033 =
                            let uu____3038 = FStar_Ident.path_of_lid lid2 in
                            (uu____3038, t1) in
                          FStar_Reflection_Data.Ctor uu____3033
                      | uu____3043 -> failwith "wat 1")
                 | uu____3044 -> failwith "wat 2" in
               let ctors = FStar_List.map ctor1 dc_lids in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____3073) ->
               let fv =
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv -> fv
                 | FStar_Util.Inl uu____3088 ->
                     failwith "global Sig_let has bv" in
               FStar_Reflection_Data.Sg_Let
                 (fv, (lb.FStar_Syntax_Syntax.lbtyp),
                   (lb.FStar_Syntax_Syntax.lbdef))
           | uu____3093 -> FStar_Reflection_Data.Unk)
let embed_ctor: FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____3100 =
          let uu____3101 =
            let uu____3102 =
              let uu____3103 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____3103 in
            let uu____3104 =
              let uu____3107 =
                let uu____3108 = embed_term t in
                FStar_Syntax_Syntax.as_arg uu____3108 in
              [uu____3107] in
            uu____3102 :: uu____3104 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____3101 in
        uu____3100 FStar_Pervasives_Native.None FStar_Range.dummyRange
let unembed_ctor: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3116 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3116 with
    | (hd1,args) ->
        let uu____3153 =
          let uu____3166 =
            let uu____3167 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3167.FStar_Syntax_Syntax.n in
          (uu____3166, args) in
        (match uu____3153 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3180)::(t2,uu____3182)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3217 =
               let uu____3222 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3225 = unembed_term t2 in (uu____3222, uu____3225) in
             FStar_Reflection_Data.Ctor uu____3217
         | uu____3228 -> failwith "not an embedded ctor")
let embed_sigelt_view:
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3257 =
          let uu____3258 =
            let uu____3259 =
              let uu____3260 = FStar_Syntax_Embeddings.embed_string_list nm in
              FStar_Syntax_Syntax.as_arg uu____3260 in
            let uu____3261 =
              let uu____3264 =
                let uu____3265 = embed_binders bs in
                FStar_Syntax_Syntax.as_arg uu____3265 in
              let uu____3266 =
                let uu____3269 =
                  let uu____3270 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3270 in
                let uu____3271 =
                  let uu____3274 =
                    let uu____3275 =
                      FStar_Syntax_Embeddings.embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs in
                    FStar_Syntax_Syntax.as_arg uu____3275 in
                  [uu____3274] in
                uu____3269 :: uu____3271 in
              uu____3264 :: uu____3266 in
            uu____3259 :: uu____3261 in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____3258 in
        uu____3257 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Sg_Let (fv,ty,t) ->
        let uu____3281 =
          let uu____3282 =
            let uu____3283 =
              let uu____3284 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____3284 in
            let uu____3285 =
              let uu____3288 =
                let uu____3289 = embed_term ty in
                FStar_Syntax_Syntax.as_arg uu____3289 in
              let uu____3290 =
                let uu____3293 =
                  let uu____3294 = embed_term t in
                  FStar_Syntax_Syntax.as_arg uu____3294 in
                [uu____3293] in
              uu____3288 :: uu____3290 in
            uu____3283 :: uu____3285 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let
            uu____3282 in
        uu____3281 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
let unembed_sigelt_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____3302 = FStar_Syntax_Util.head_and_args t1 in
    match uu____3302 with
    | (hd1,args) ->
        let uu____3339 =
          let uu____3352 =
            let uu____3353 = FStar_Syntax_Util.un_uinst hd1 in
            uu____3353.FStar_Syntax_Syntax.n in
          (uu____3352, args) in
        (match uu____3339 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3366)::(bs,uu____3368)::(t2,uu____3370)::(dcs,uu____3372)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3427 =
               let uu____3440 =
                 FStar_Syntax_Embeddings.unembed_string_list nm in
               let uu____3443 = unembed_binders bs in
               let uu____3446 = unembed_term t2 in
               let uu____3447 =
                 FStar_Syntax_Embeddings.unembed_list unembed_ctor dcs in
               (uu____3440, uu____3443, uu____3446, uu____3447) in
             FStar_Reflection_Data.Sg_Inductive uu____3427
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(fvar1,uu____3458)::(ty,uu____3460)::(t2,uu____3462)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Let_lid
             ->
             let uu____3507 =
               let uu____3514 = unembed_fvar fvar1 in
               let uu____3515 = unembed_term ty in
               let uu____3516 = unembed_term t2 in
               (uu____3514, uu____3515, uu____3516) in
             FStar_Reflection_Data.Sg_Let uu____3507
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____3532 -> failwith "not an embedded sigelt_view")
let binders_of_env: FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders
  = fun e  -> FStar_TypeChecker_Env.all_binders e
let type_of_binder:
  'Auu____3553 .
    (FStar_Syntax_Syntax.bv,'Auu____3553) FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun b  -> match b with | (b1,uu____3569) -> b1.FStar_Syntax_Syntax.sort
let term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  FStar_Syntax_Util.term_eq
let fresh_binder:
  'Auu____3580 .
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.bv,'Auu____3580 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____3591 =
      FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t in
    (uu____3591, FStar_Pervasives_Native.None)
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  FStar_Syntax_Print.term_to_string