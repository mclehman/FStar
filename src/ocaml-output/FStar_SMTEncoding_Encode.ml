open Prims
let add_fuel:
  'Auu____7 . 'Auu____7 -> 'Auu____7 Prims.list -> 'Auu____7 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____22 = FStar_Options.unthrottle_inductives () in
      if uu____22 then tl1 else x :: tl1
let withenv:
  'Auu____36 'Auu____37 'Auu____38 .
    'Auu____38 ->
      ('Auu____37,'Auu____36) FStar_Pervasives_Native.tuple2 ->
        ('Auu____37,'Auu____36,'Auu____38) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____56  -> match uu____56 with | (a,b) -> (a, b, c)
let vargs:
  'Auu____71 'Auu____72 'Auu____73 .
    (('Auu____73,'Auu____72) FStar_Util.either,'Auu____71)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____73,'Auu____72) FStar_Util.either,'Auu____71)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___124_119  ->
         match uu___124_119 with
         | (FStar_Util.Inl uu____128,uu____129) -> false
         | uu____134 -> true) args
let subst_lcomp_opt:
  'Auu____149 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.lcomp,'Auu____149) FStar_Util.either
        FStar_Pervasives_Native.option ->
        (FStar_Syntax_Syntax.lcomp,'Auu____149) FStar_Util.either
          FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
          let uu____185 =
            let uu____190 =
              let uu____191 =
                let uu____194 = l1.FStar_Syntax_Syntax.comp () in
                FStar_Syntax_Subst.subst_comp s uu____194 in
              FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____191 in
            FStar_Util.Inl uu____190 in
          FStar_Pervasives_Native.Some uu____185
      | uu____201 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___147_221 = a in
        let uu____222 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____222;
          FStar_Syntax_Syntax.index =
            (uu___147_221.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___147_221.FStar_Syntax_Syntax.sort)
        } in
      let uu____223 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____223
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____239 =
          let uu____240 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____240 in
        let uu____241 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____241 with
        | (uu____246,t) ->
            let uu____248 =
              let uu____249 = FStar_Syntax_Subst.compress t in
              uu____249.FStar_Syntax_Syntax.n in
            (match uu____248 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____270 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____270 with
                  | (binders,uu____276) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____291 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____300 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____300
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____309 =
        let uu____314 = mk_term_projector_name lid a in
        (uu____314,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____309
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____323 =
        let uu____328 = mk_term_projector_name_by_pos lid i in
        (uu____328,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____323
let mk_data_tester:
  'Auu____337 .
    'Auu____337 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
type varops_t =
  {
  push: Prims.unit -> Prims.unit;
  pop: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}[@@deriving show]
let __proj__Mkvarops_t__item__push: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
let __proj__Mkvarops_t__item__pop: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
let __proj__Mkvarops_t__item__new_var:
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
let __proj__Mkvarops_t__item__new_fvar:
  varops_t -> FStar_Ident.lident -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
let __proj__Mkvarops_t__item__fresh: varops_t -> Prims.string -> Prims.string
  =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
let __proj__Mkvarops_t__item__string_const:
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
let __proj__Mkvarops_t__item__next_id: varops_t -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
let __proj__Mkvarops_t__item__mk_unique:
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____718 =
    let uu____719 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____722 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____719, uu____722) in
  let scopes =
    let uu____742 = let uu____753 = new_scope () in [uu____753] in
    FStar_Util.mk_ref uu____742 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____794 =
        let uu____797 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu____797
          (fun uu____899  ->
             match uu____899 with
             | (names1,uu____911) -> FStar_Util.smap_try_find names1 y1) in
      match uu____794 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____920 ->
          (FStar_Util.incr ctr;
           (let uu____943 =
              let uu____944 =
                let uu____945 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____945 in
              Prims.strcat "__" uu____944 in
            Prims.strcat y1 uu____943)) in
    let top_scope =
      let uu____1009 =
        let uu____1018 = FStar_ST.op_Bang scopes in FStar_List.hd uu____1018 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1009 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1146 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1233 =
      let uu____1234 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1234 in
    FStar_Util.format2 "%s_%s" pfx uu____1233 in
  let string_const s =
    let uu____1239 =
      let uu____1242 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1242
        (fun uu____1344  ->
           match uu____1344 with
           | (uu____1355,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1239 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____1368 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1368 in
        let top_scope =
          let uu____1372 =
            let uu____1381 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1381 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1372 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1498 =
    let uu____1499 =
      let uu____1510 = new_scope () in
      let uu____1519 = FStar_ST.op_Bang scopes in uu____1510 :: uu____1519 in
    FStar_ST.op_Colon_Equals scopes uu____1499 in
  let pop1 uu____1701 =
    let uu____1702 =
      let uu____1713 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1713 in
    FStar_ST.op_Colon_Equals scopes uu____1702 in
  {
    push = push1;
    pop = pop1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  }
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___148_1896 = x in
    let uu____1897 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1897;
      FStar_Syntax_Syntax.index = (uu___148_1896.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___148_1896.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4[@@deriving show]
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1931 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1969 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____2020 'Auu____2021 .
    'Auu____2021 ->
      ('Auu____2021,'Auu____2020 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_assumption_names: Prims.string Prims.list;}[@@deriving show]
let __proj__Mkcache_entry__item__cache_symbol_name:
  cache_entry -> Prims.string =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
let __proj__Mkcache_entry__item__cache_symbol_arg_sorts:
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
let __proj__Mkcache_entry__item__cache_symbol_decls:
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
let __proj__Mkcache_entry__item__cache_symbol_assumption_names:
  cache_entry -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_assumption_names
type env_t =
  {
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache: cache_entry FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}[@@deriving show]
let __proj__Mkenv_t__item__bindings: env_t -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__bindings
let __proj__Mkenv_t__item__depth: env_t -> Prims.int =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__depth
let __proj__Mkenv_t__item__tcenv: env_t -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__tcenv
let __proj__Mkenv_t__item__warn: env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__warn
let __proj__Mkenv_t__item__cache: env_t -> cache_entry FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__cache
let __proj__Mkenv_t__item__nolabels: env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__nolabels
let __proj__Mkenv_t__item__use_zfuel_name: env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__use_zfuel_name
let __proj__Mkenv_t__item__encode_non_total_function_typ: env_t -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__encode_non_total_function_typ
let __proj__Mkenv_t__item__current_module_name: env_t -> Prims.string =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__current_module_name
let mk_cache_entry:
  'Auu____2335 .
    'Auu____2335 ->
      Prims.string ->
        FStar_SMTEncoding_Term.sort Prims.list ->
          FStar_SMTEncoding_Term.decl Prims.list -> cache_entry
  =
  fun env  ->
    fun tsym  ->
      fun cvar_sorts  ->
        fun t_decls  ->
          let names1 =
            FStar_All.pipe_right t_decls
              (FStar_List.collect
                 (fun uu___125_2369  ->
                    match uu___125_2369 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2373 -> [])) in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls;
            cache_symbol_assumption_names = names1
          }
let use_cache_entry: cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____2384 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___126_2394  ->
              match uu___126_2394 with
              | Binding_var (x,uu____2396) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2398,uu____2399,uu____2400) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2384 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2417 .
    env_t ->
      (binding -> 'Auu____2417 FStar_Pervasives_Native.option) ->
        'Auu____2417 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2447 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2447
      then
        let uu____2450 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2450
      else FStar_Pervasives_Native.None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____2465 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2465)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___149_2483 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___149_2483.tcenv);
           warn = (uu___149_2483.warn);
           cache = (uu___149_2483.cache);
           nolabels = (uu___149_2483.nolabels);
           use_zfuel_name = (uu___149_2483.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___149_2483.encode_non_total_function_typ);
           current_module_name = (uu___149_2483.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___150_2503 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___150_2503.depth);
           tcenv = (uu___150_2503.tcenv);
           warn = (uu___150_2503.warn);
           cache = (uu___150_2503.cache);
           nolabels = (uu___150_2503.nolabels);
           use_zfuel_name = (uu___150_2503.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___150_2503.encode_non_total_function_typ);
           current_module_name = (uu___150_2503.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___151_2527 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___151_2527.depth);
             tcenv = (uu___151_2527.tcenv);
             warn = (uu___151_2527.warn);
             cache = (uu___151_2527.cache);
             nolabels = (uu___151_2527.nolabels);
             use_zfuel_name = (uu___151_2527.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___151_2527.encode_non_total_function_typ);
             current_module_name = (uu___151_2527.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___152_2540 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___152_2540.depth);
          tcenv = (uu___152_2540.tcenv);
          warn = (uu___152_2540.warn);
          cache = (uu___152_2540.cache);
          nolabels = (uu___152_2540.nolabels);
          use_zfuel_name = (uu___152_2540.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___152_2540.encode_non_total_function_typ);
          current_module_name = (uu___152_2540.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___127_2566  ->
             match uu___127_2566 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2579 -> FStar_Pervasives_Native.None) in
      let uu____2584 = aux a in
      match uu____2584 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2596 = aux a2 in
          (match uu____2596 with
           | FStar_Pervasives_Native.None  ->
               let uu____2607 =
                 let uu____2608 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2609 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2608 uu____2609 in
               failwith uu____2607
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____2638 =
        let uu___153_2639 = env in
        let uu____2640 =
          let uu____2643 =
            let uu____2644 =
              let uu____2657 =
                let uu____2660 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                  uu____2660 in
              (x, fname, uu____2657, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2644 in
          uu____2643 :: (env.bindings) in
        {
          bindings = uu____2640;
          depth = (uu___153_2639.depth);
          tcenv = (uu___153_2639.tcenv);
          warn = (uu___153_2639.warn);
          cache = (uu___153_2639.cache);
          nolabels = (uu___153_2639.nolabels);
          use_zfuel_name = (uu___153_2639.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___153_2639.encode_non_total_function_typ);
          current_module_name = (uu___153_2639.current_module_name)
        } in
      (fname, ftok, uu____2638)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___128_2704  ->
           match uu___128_2704 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2743 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2762 =
        lookup_binding env
          (fun uu___129_2770  ->
             match uu___129_2770 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2785 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2762 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun a  ->
      let uu____2806 = try_lookup_lid env a in
      match uu____2806 with
      | FStar_Pervasives_Native.None  ->
          let uu____2839 =
            let uu____2840 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2840 in
          failwith uu____2839
      | FStar_Pervasives_Native.Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___154_2892 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___154_2892.depth);
            tcenv = (uu___154_2892.tcenv);
            warn = (uu___154_2892.warn);
            cache = (uu___154_2892.cache);
            nolabels = (uu___154_2892.nolabels);
            use_zfuel_name = (uu___154_2892.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_2892.encode_non_total_function_typ);
            current_module_name = (uu___154_2892.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2909 = lookup_lid env x in
        match uu____2909 with
        | (t1,t2,uu____2922) ->
            let t3 =
              let uu____2932 =
                let uu____2939 =
                  let uu____2942 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2942] in
                (f, uu____2939) in
              FStar_SMTEncoding_Util.mkApp uu____2932 in
            let uu___155_2947 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___155_2947.depth);
              tcenv = (uu___155_2947.tcenv);
              warn = (uu___155_2947.warn);
              cache = (uu___155_2947.cache);
              nolabels = (uu___155_2947.nolabels);
              use_zfuel_name = (uu___155_2947.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___155_2947.encode_non_total_function_typ);
              current_module_name = (uu___155_2947.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2962 = try_lookup_lid env l in
      match uu____2962 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3011 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3019,fuel::[]) ->
                         let uu____3023 =
                           let uu____3024 =
                             let uu____3025 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____3025
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____3024 "fuel" in
                         if uu____3023
                         then
                           let uu____3028 =
                             let uu____3029 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3029
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_Pervasives_Native.Some _0_42)
                             uu____3028
                         else FStar_Pervasives_Native.Some t
                     | uu____3033 -> FStar_Pervasives_Native.Some t)
                | uu____3034 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____3049 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____3049 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3053 =
            let uu____3054 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____3054 in
          failwith uu____3053
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____3067 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3067 with | (x,uu____3079,uu____3080) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____3107 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3107 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3143;
                 FStar_SMTEncoding_Term.rng = uu____3144;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3159 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3183 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___130_3201  ->
           match uu___130_3201 with
           | Binding_fvar (uu____3204,nm',tok,uu____3207) when nm = nm' ->
               tok
           | uu____3216 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____3223 .
    'Auu____3223 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3241  ->
      match uu____3241 with
      | (pats,vars,body) ->
          let fallback uu____3266 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3271 = FStar_Options.unthrottle_inductives () in
          if uu____3271
          then fallback ()
          else
            (let uu____3273 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3273 with
             | (fsym,fterm) ->
                 let add_fuel1 tms =
                   FStar_All.pipe_right tms
                     (FStar_List.map
                        (fun p  ->
                           match p.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var "HasType",args) ->
                               FStar_SMTEncoding_Util.mkApp
                                 ("HasTypeFuel", (fterm :: args))
                           | uu____3304 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3325 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3325
                         | uu____3328 ->
                             let uu____3329 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3329 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3334 -> body in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____3378 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3391 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3398 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3399 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3416 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3433 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3435 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3435 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3453;
             FStar_Syntax_Syntax.vars = uu____3454;_},uu____3455)
          ->
          let uu____3476 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3476 FStar_Option.isNone
      | uu____3493 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3502 =
        let uu____3503 = FStar_Syntax_Util.un_uinst t in
        uu____3503.FStar_Syntax_Syntax.n in
      match uu____3502 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3506,uu____3507,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___131_3528  ->
                  match uu___131_3528 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3529 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3531 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3531 FStar_Option.isSome
      | uu____3548 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3557 = head_normal env t in
      if uu____3557
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let norm: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let trivial_post: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____3571 =
      let uu____3572 = FStar_Syntax_Syntax.null_binder t in [uu____3572] in
    let uu____3573 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3571 uu____3573 FStar_Pervasives_Native.None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____3613 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3613
                | s ->
                    let uu____3618 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3618) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___132_3636  ->
    match uu___132_3636 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3637 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____3676;
                       FStar_SMTEncoding_Term.rng = uu____3677;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3700) ->
              let uu____3709 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3720 -> false) args (FStar_List.rev xs)) in
              if uu____3709
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3724,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3728 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3732 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3732)) in
              if uu____3728
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3736 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list;}[@@deriving show]
let __proj__Mkpattern__item__pat_vars:
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
let __proj__Mkpattern__item__pat_term:
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
let __proj__Mkpattern__item__guard:
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
let __proj__Mkpattern__item__projections:
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____3966 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3971 -> false
let as_function_typ:
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____3992 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4005 ->
            let uu____4012 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____4012
        | uu____4013 ->
            if norm1
            then let uu____4014 = whnf env t1 in aux false uu____4014
            else
              (let uu____4016 =
                 let uu____4017 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____4018 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4017 uu____4018 in
               failwith uu____4016) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____4050 ->
        let uu____4051 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4051)
let is_arithmetic_primitive:
  'Auu____4068 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4068 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4088::uu____4089::[]) ->
          ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.op_Subtraction))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.op_Multiply))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4093::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4096 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4118 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4134 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4141 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4141)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4180)::uu____4181::uu____4182::[]) ->
          (((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_and_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_xor_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_or_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_shift_left_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_shift_right_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_udiv_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.bv_mod_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_uext_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4233)::uu____4234::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4271 -> false
let rec encode_const:
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____4478 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4478, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4481 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4481, [])
      | FStar_Const.Const_char c1 ->
          let uu____4485 =
            let uu____4486 =
              let uu____4493 =
                let uu____4496 =
                  let uu____4497 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4497 in
                [uu____4496] in
              ("FStar.Char.Char", uu____4493) in
            FStar_SMTEncoding_Util.mkApp uu____4486 in
          (uu____4485, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4513 =
            let uu____4514 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4514 in
          (uu____4513, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4535) ->
          let uu____4536 = varops.string_const s in (uu____4536, [])
      | FStar_Const.Const_range r ->
          (FStar_SMTEncoding_Term.mk_Range_const, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4545 =
            let uu____4546 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4546 in
          failwith uu____4545
and encode_binders:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____4575 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4575
         then
           let uu____4576 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4576
         else ());
        (let uu____4578 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4662  ->
                   fun b  ->
                     match uu____4662 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4741 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4757 = gen_term_var env1 x in
                           match uu____4757 with
                           | (xxsym,xx,env') ->
                               let uu____4781 =
                                 let uu____4786 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4786 env1 xx in
                               (match uu____4781 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4741 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4578 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4945 = encode_term t env in
          match uu____4945 with
          | (t1,decls) ->
              let uu____4956 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4956, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4967 = encode_term t env in
          match uu____4967 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4982 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4982, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4984 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4984, decls))
and encode_arith_term:
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____4990 = encode_args args_e env in
        match uu____4990 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5009 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5018 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5018 in
            let binary arg_tms1 =
              let uu____5031 =
                let uu____5032 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5032 in
              let uu____5033 =
                let uu____5034 =
                  let uu____5035 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5035 in
                FStar_SMTEncoding_Term.unboxInt uu____5034 in
              (uu____5031, uu____5033) in
            let mk_default uu____5041 =
              let uu____5042 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5042 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5093 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5093
              then
                let uu____5094 = let uu____5095 = mk_args ts in op uu____5095 in
                FStar_All.pipe_right uu____5094 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5124 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5124
              then
                let uu____5125 = binary ts in
                match uu____5125 with
                | (t1,t2) ->
                    let uu____5132 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5132
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5136 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5136
                 then
                   let uu____5137 = op (binary ts) in
                   FStar_All.pipe_right uu____5137
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)] in
            let uu____5268 =
              let uu____5277 =
                FStar_List.tryFind
                  (fun uu____5299  ->
                     match uu____5299 with
                     | (l,uu____5309) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5277 FStar_Util.must in
            (match uu____5268 with
             | (uu____5348,op) ->
                 let uu____5358 = op arg_tms in (uu____5358, decls))
and encode_BitVector_term:
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5366 = FStar_List.hd args_e in
        match uu____5366 with
        | (tm_sz,uu____5374) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5384 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5384 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5392 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5392);
                   t_decls) in
            let uu____5393 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5413::(sz_arg,uu____5415)::uu____5416::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5465 =
                    let uu____5468 = FStar_List.tail args_e in
                    FStar_List.tail uu____5468 in
                  let uu____5471 =
                    let uu____5474 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5474 in
                  (uu____5465, uu____5471)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5480::(sz_arg,uu____5482)::uu____5483::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5532 =
                    let uu____5533 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5533 in
                  failwith uu____5532
              | uu____5542 ->
                  let uu____5549 = FStar_List.tail args_e in
                  (uu____5549, FStar_Pervasives_Native.None) in
            (match uu____5393 with
             | (arg_tms,ext_sz) ->
                 let uu____5572 = encode_args arg_tms env in
                 (match uu____5572 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5593 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5602 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5602 in
                      let unary_arith arg_tms2 =
                        let uu____5611 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5611 in
                      let binary arg_tms2 =
                        let uu____5624 =
                          let uu____5625 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5625 in
                        let uu____5626 =
                          let uu____5627 =
                            let uu____5628 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5628 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5627 in
                        (uu____5624, uu____5626) in
                      let binary_arith arg_tms2 =
                        let uu____5643 =
                          let uu____5644 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5644 in
                        let uu____5645 =
                          let uu____5646 =
                            let uu____5647 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5647 in
                          FStar_SMTEncoding_Term.unboxInt uu____5646 in
                        (uu____5643, uu____5645) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5696 =
                          let uu____5697 = mk_args ts in op uu____5697 in
                        FStar_All.pipe_right uu____5696 resBox in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool in
                      let bv_uext arg_tms2 =
                        let uu____5787 =
                          let uu____5790 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5790 in
                        let uu____5792 =
                          let uu____5795 =
                            let uu____5796 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5796 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5795 in
                        mk_bv uu____5787 unary uu____5792 arg_tms2 in
                      let to_int =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu____5971 =
                        let uu____5980 =
                          FStar_List.tryFind
                            (fun uu____6002  ->
                               match uu____6002 with
                               | (l,uu____6012) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5980 FStar_Util.must in
                      (match uu____5971 with
                       | (uu____6053,op) ->
                           let uu____6063 = op arg_tms1 in
                           (uu____6063, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6074 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6074
       then
         let uu____6075 = FStar_Syntax_Print.tag_of_term t in
         let uu____6076 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6077 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6075 uu____6076
           uu____6077
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6083 ->
           let uu____6108 =
             let uu____6109 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6110 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6111 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6112 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6109
               uu____6110 uu____6111 uu____6112 in
           failwith uu____6108
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6117 =
             let uu____6118 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6119 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6120 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6121 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6118
               uu____6119 uu____6120 uu____6121 in
           failwith uu____6117
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6127 =
             let uu____6128 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6128 in
           failwith uu____6127
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6135) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6176;
              FStar_Syntax_Syntax.vars = uu____6177;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6194 = varops.fresh "t" in
             (uu____6194, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6197 =
               let uu____6208 =
                 let uu____6211 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6211 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6208) in
             FStar_SMTEncoding_Term.DeclFun uu____6197 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = uu____6218;
              FStar_Syntax_Syntax.pos = uu____6219;
              FStar_Syntax_Syntax.vars = uu____6220;_},FStar_Syntax_Syntax.Meta_quoted
            (qt,qi))
           ->
           let tsym =
             let uu____6236 = varops.fresh "t" in
             (uu____6236, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6239 =
               let uu____6250 =
                 let uu____6253 =
                   let uu____6254 = FStar_Syntax_Print.term_to_string qt in
                   FStar_Util.format1 "quoted term -- %s" uu____6254 in
                 FStar_Pervasives_Native.Some uu____6253 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6250) in
             FStar_SMTEncoding_Term.DeclFun uu____6239 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6262) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6272 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6272, [])
       | FStar_Syntax_Syntax.Tm_type uu____6275 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6279) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6304 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6304 with
            | (binders1,res) ->
                let uu____6315 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6315
                then
                  let uu____6320 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6320 with
                   | (vars,guards,env',decls,uu____6345) ->
                       let fsym =
                         let uu____6363 = varops.fresh "f" in
                         (uu____6363, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6366 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___156_6375 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___156_6375.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___156_6375.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___156_6375.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___156_6375.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___156_6375.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___156_6375.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___156_6375.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___156_6375.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___156_6375.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___156_6375.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___156_6375.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___156_6375.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___156_6375.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___156_6375.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___156_6375.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___156_6375.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___156_6375.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___156_6375.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___156_6375.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___156_6375.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___156_6375.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___156_6375.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___156_6375.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___156_6375.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___156_6375.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___156_6375.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___156_6375.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___156_6375.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___156_6375.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___156_6375.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___156_6375.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___156_6375.FStar_TypeChecker_Env.dsenv)
                            }) res in
                       (match uu____6366 with
                        | (pre_opt,res_t) ->
                            let uu____6386 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6386 with
                             | (res_pred,decls') ->
                                 let uu____6397 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6410 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6410, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6414 =
                                         encode_formula pre env' in
                                       (match uu____6414 with
                                        | (guard,decls0) ->
                                            let uu____6427 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6427, decls0)) in
                                 (match uu____6397 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6439 =
                                          let uu____6450 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6450) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6439 in
                                      let cvars =
                                        let uu____6468 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6468
                                          (FStar_List.filter
                                             (fun uu____6482  ->
                                                match uu____6482 with
                                                | (x,uu____6488) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6507 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6507 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6515 =
                                             let uu____6516 =
                                               let uu____6523 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6523) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6516 in
                                           (uu____6515,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6543 =
                                               let uu____6544 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6544 in
                                             varops.mk_unique uu____6543 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6555 =
                                               FStar_Options.log_queries () in
                                             if uu____6555
                                             then
                                               let uu____6558 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6558
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6566 =
                                               let uu____6573 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6573) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6566 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6585 =
                                               let uu____6592 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6592,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6585 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym in
                                             let uu____6613 =
                                               let uu____6620 =
                                                 let uu____6621 =
                                                   let uu____6632 =
                                                     let uu____6633 =
                                                       let uu____6638 =
                                                         let uu____6639 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6639 in
                                                       (f_has_t, uu____6638) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6633 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6632) in
                                                 mkForall_fuel uu____6621 in
                                               (uu____6620,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6613 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6662 =
                                               let uu____6669 =
                                                 let uu____6670 =
                                                   let uu____6681 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6681) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6670 in
                                               (uu____6669,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6662 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6706 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6706);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____6721 =
                       let uu____6728 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6728,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6721 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6740 =
                       let uu____6747 =
                         let uu____6748 =
                           let uu____6759 =
                             let uu____6760 =
                               let uu____6765 =
                                 let uu____6766 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6766 in
                               (f_has_t, uu____6765) in
                             FStar_SMTEncoding_Util.mkImp uu____6760 in
                           ([[f_has_t]], [fsym], uu____6759) in
                         mkForall_fuel uu____6748 in
                       (uu____6747, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6740 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6793 ->
           let uu____6800 =
             let uu____6805 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6805 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6812;
                 FStar_Syntax_Syntax.vars = uu____6813;_} ->
                 let uu____6820 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6820 with
                  | (b,f1) ->
                      let uu____6845 =
                        let uu____6846 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6846 in
                      (uu____6845, f1))
             | uu____6855 -> failwith "impossible" in
           (match uu____6800 with
            | (x,f) ->
                let uu____6866 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6866 with
                 | (base_t,decls) ->
                     let uu____6877 = gen_term_var env x in
                     (match uu____6877 with
                      | (x1,xtm,env') ->
                          let uu____6891 = encode_formula f env' in
                          (match uu____6891 with
                           | (refinement,decls') ->
                               let uu____6902 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6902 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6918 =
                                        let uu____6921 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6928 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6921
                                          uu____6928 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6918 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6961  ->
                                              match uu____6961 with
                                              | (y,uu____6967) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____7000 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____7000 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7008 =
                                           let uu____7009 =
                                             let uu____7016 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7016) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7009 in
                                         (uu____7008,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7037 =
                                             let uu____7038 =
                                               let uu____7039 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7039 in
                                             Prims.strcat module_name
                                               uu____7038 in
                                           varops.mk_unique uu____7037 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                         let t1 =
                                           let uu____7053 =
                                             let uu____7060 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7060) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7053 in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1 in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1 in
                                         let t_haseq1 =
                                           let uu____7075 =
                                             let uu____7082 =
                                               let uu____7083 =
                                                 let uu____7094 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7094) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7083 in
                                             (uu____7082,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7075 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7120 =
                                             let uu____7127 =
                                               let uu____7128 =
                                                 let uu____7139 =
                                                   let uu____7140 =
                                                     let uu____7145 =
                                                       let uu____7146 =
                                                         let uu____7157 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7157) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7146 in
                                                     (uu____7145, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7140 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7139) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7128 in
                                             (uu____7127,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7120 in
                                         let t_kinding =
                                           let uu____7195 =
                                             let uu____7202 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7202,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7195 in
                                         let t_interp =
                                           let uu____7220 =
                                             let uu____7227 =
                                               let uu____7228 =
                                                 let uu____7239 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7239) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7228 in
                                             let uu____7262 =
                                               let uu____7265 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7265 in
                                             (uu____7227, uu____7262,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7220 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7272 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7272);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7302 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7302 in
           let uu____7303 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7303 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7315 =
                    let uu____7322 =
                      let uu____7323 =
                        let uu____7324 =
                          let uu____7325 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7325 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7324 in
                      varops.mk_unique uu____7323 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7322) in
                  FStar_SMTEncoding_Util.mkAssume uu____7315 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7330 ->
           let uu____7345 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7345 with
            | (head1,args_e) ->
                let uu____7386 =
                  let uu____7399 =
                    let uu____7400 = FStar_Syntax_Subst.compress head1 in
                    uu____7400.FStar_Syntax_Syntax.n in
                  (uu____7399, args_e) in
                (match uu____7386 with
                 | uu____7415 when head_redex env head1 ->
                     let uu____7428 = whnf env t in
                     encode_term uu____7428 env
                 | uu____7429 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7448 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7462;
                       FStar_Syntax_Syntax.vars = uu____7463;_},uu____7464),uu____7465::
                    (v1,uu____7467)::(v2,uu____7469)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7520 = encode_term v1 env in
                     (match uu____7520 with
                      | (v11,decls1) ->
                          let uu____7531 = encode_term v2 env in
                          (match uu____7531 with
                           | (v21,decls2) ->
                               let uu____7542 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7542,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7546::(v1,uu____7548)::(v2,uu____7550)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7597 = encode_term v1 env in
                     (match uu____7597 with
                      | (v11,decls1) ->
                          let uu____7608 = encode_term v2 env in
                          (match uu____7608 with
                           | (v21,decls2) ->
                               let uu____7619 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7619,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7622) ->
                     let e0 =
                       let uu____7640 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7640 in
                     ((let uu____7648 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7648
                       then
                         let uu____7649 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7649
                       else ());
                      (let e =
                         let uu____7654 =
                           let uu____7655 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7656 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7655
                             uu____7656 in
                         uu____7654 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7665),(arg,uu____7667)::[]) -> encode_term arg env
                 | uu____7692 ->
                     let uu____7705 = encode_args args_e env in
                     (match uu____7705 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7760 = encode_term head1 env in
                            match uu____7760 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7824 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7824 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7902  ->
                                                 fun uu____7903  ->
                                                   match (uu____7902,
                                                           uu____7903)
                                                   with
                                                   | ((bv,uu____7925),
                                                      (a,uu____7927)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7945 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7945
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7950 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7950 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7965 =
                                                   let uu____7972 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7981 =
                                                     let uu____7982 =
                                                       let uu____7983 =
                                                         let uu____7984 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7984 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7983 in
                                                     varops.mk_unique
                                                       uu____7982 in
                                                   (uu____7972,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7981) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7965 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____8001 = lookup_free_var_sym env fv in
                            match uu____8001 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args)) in
                                (tm, decls) in
                          let head2 = FStar_Syntax_Subst.compress head1 in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____8032;
                                   FStar_Syntax_Syntax.vars = uu____8033;_},uu____8034)
                                ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.pos = uu____8045;
                                   FStar_Syntax_Syntax.vars = uu____8046;_},uu____8047)
                                ->
                                let uu____8052 =
                                  let uu____8053 =
                                    let uu____8058 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8058
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8053
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8052
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8088 =
                                  let uu____8089 =
                                    let uu____8094 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8094
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8089
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8088
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8123,(FStar_Util.Inl t1,uu____8125),uu____8126)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8175,(FStar_Util.Inr c,uu____8177),uu____8178)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8227 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8254 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8254 in
                               let uu____8255 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8255 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8271;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8272;_},uu____8273)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____8287 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____8336 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8336 with
            | (bs1,body1,opening) ->
                let fallback uu____8359 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8366 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8366, [decl]) in
                let is_impure rc =
                  let uu____8373 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8373 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8383 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8383
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8403 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8403
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8407 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8407)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8414 =
                         let uu____8415 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8415 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8414);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8417 =
                       (is_impure rc) &&
                         (let uu____8419 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8419) in
                     if uu____8417
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8426 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8426 with
                        | (vars,guards,envbody,decls,uu____8451) ->
                            let body2 =
                              let uu____8465 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8465
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8467 = encode_term body2 envbody in
                            (match uu____8467 with
                             | (body3,decls') ->
                                 let uu____8478 =
                                   let uu____8487 = codomain_eff rc in
                                   match uu____8487 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8506 = encode_term tfun env in
                                       (match uu____8506 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8478 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8538 =
                                          let uu____8549 =
                                            let uu____8550 =
                                              let uu____8555 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8555, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8550 in
                                          ([], vars, uu____8549) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8538 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8567 =
                                              let uu____8570 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8570
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8567 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8589 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8589 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8597 =
                                             let uu____8598 =
                                               let uu____8605 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8605) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8598 in
                                           (uu____8597,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8616 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8616 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8627 =
                                                    let uu____8628 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8628 = cache_size in
                                                  if uu____8627
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'') in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1 in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name in
                                                  let fsym =
                                                    let uu____8644 =
                                                      let uu____8645 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8645 in
                                                    varops.mk_unique
                                                      uu____8644 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8652 =
                                                    let uu____8659 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8659) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8652 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1 in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym in
                                                      let uu____8677 =
                                                        let uu____8678 =
                                                          let uu____8685 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8685,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8678 in
                                                      [uu____8677] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8698 =
                                                    let uu____8705 =
                                                      let uu____8706 =
                                                        let uu____8717 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8717) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8706 in
                                                    (uu____8705,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8698 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8734 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8734);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8737,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8738;
                          FStar_Syntax_Syntax.lbunivs = uu____8739;
                          FStar_Syntax_Syntax.lbtyp = uu____8740;
                          FStar_Syntax_Syntax.lbeff = uu____8741;
                          FStar_Syntax_Syntax.lbdef = uu____8742;_}::uu____8743),uu____8744)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8770;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8772;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8793 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)
and encode_let:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____8863 = encode_term e1 env in
              match uu____8863 with
              | (ee1,decls1) ->
                  let uu____8874 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8874 with
                   | (xs,e21) ->
                       let uu____8899 = FStar_List.hd xs in
                       (match uu____8899 with
                        | (x1,uu____8913) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8915 = encode_body e21 env' in
                            (match uu____8915 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____8947 =
              let uu____8954 =
                let uu____8955 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8955 in
              gen_term_var env uu____8954 in
            match uu____8947 with
            | (scrsym,scr',env1) ->
                let uu____8963 = encode_term e env1 in
                (match uu____8963 with
                 | (scr,decls) ->
                     let uu____8974 =
                       let encode_branch b uu____8999 =
                         match uu____8999 with
                         | (else_case,decls1) ->
                             let uu____9018 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9018 with
                              | (p,w,br) ->
                                  let uu____9044 = encode_pat env1 p in
                                  (match uu____9044 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9081  ->
                                                   match uu____9081 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9088 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9110 =
                                               encode_term w1 env2 in
                                             (match uu____9110 with
                                              | (w2,decls2) ->
                                                  let uu____9123 =
                                                    let uu____9124 =
                                                      let uu____9129 =
                                                        let uu____9130 =
                                                          let uu____9135 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9135) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9130 in
                                                      (guard, uu____9129) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9124 in
                                                  (uu____9123, decls2)) in
                                       (match uu____9088 with
                                        | (guard1,decls2) ->
                                            let uu____9148 =
                                              encode_br br env2 in
                                            (match uu____9148 with
                                             | (br1,decls3) ->
                                                 let uu____9161 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9161,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8974 with
                      | (match_tm,decls1) ->
                          let uu____9180 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9180, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9220 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9220
       then
         let uu____9221 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9221
       else ());
      (let uu____9223 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9223 with
       | (vars,pat_term) ->
           let uu____9240 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9293  ->
                     fun v1  ->
                       match uu____9293 with
                       | (env1,vars1) ->
                           let uu____9345 = gen_term_var env1 v1 in
                           (match uu____9345 with
                            | (xx,uu____9367,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9240 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9446 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9447 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9448 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9456 = encode_const c env1 in
                      (match uu____9456 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9470::uu____9471 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9474 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9497 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9497 with
                        | (uu____9504,uu____9505::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9508 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9541  ->
                                  match uu____9541 with
                                  | (arg,uu____9549) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9555 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9555)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9582) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9613 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9636 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9680  ->
                                  match uu____9680 with
                                  | (arg,uu____9694) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9700 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9700)) in
                      FStar_All.pipe_right uu____9636 FStar_List.flatten in
                let pat_term1 uu____9728 = encode_term pat_term env1 in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern)))
and encode_args:
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun env  ->
      let uu____9738 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9776  ->
                fun uu____9777  ->
                  match (uu____9776, uu____9777) with
                  | ((tms,decls),(t,uu____9813)) ->
                      let uu____9834 = encode_term t env in
                      (match uu____9834 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9738 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9891 = FStar_Syntax_Util.list_elements e in
        match uu____9891 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9912 =
          let uu____9927 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9927 FStar_Syntax_Util.head_and_args in
        match uu____9912 with
        | (head1,args) ->
            let uu____9966 =
              let uu____9979 =
                let uu____9980 = FStar_Syntax_Util.un_uinst head1 in
                uu____9980.FStar_Syntax_Syntax.n in
              (uu____9979, args) in
            (match uu____9966 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9994,uu____9995)::(e,uu____9997)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10032 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10068 =
            let uu____10083 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10083 FStar_Syntax_Util.head_and_args in
          match uu____10068 with
          | (head1,args) ->
              let uu____10124 =
                let uu____10137 =
                  let uu____10138 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10138.FStar_Syntax_Syntax.n in
                (uu____10137, args) in
              (match uu____10124 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10155)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10182 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10204 = smt_pat_or1 t1 in
            (match uu____10204 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10220 = list_elements1 e in
                 FStar_All.pipe_right uu____10220
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10238 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10238
                           (FStar_List.map one_pat)))
             | uu____10249 ->
                 let uu____10254 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10254])
        | uu____10275 ->
            let uu____10278 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10278] in
      let uu____10299 =
        let uu____10318 =
          let uu____10319 = FStar_Syntax_Subst.compress t in
          uu____10319.FStar_Syntax_Syntax.n in
        match uu____10318 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10358 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10358 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10401;
                        FStar_Syntax_Syntax.effect_name = uu____10402;
                        FStar_Syntax_Syntax.result_typ = uu____10403;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10405)::(post,uu____10407)::(pats,uu____10409)::[];
                        FStar_Syntax_Syntax.flags = uu____10410;_}
                      ->
                      let uu____10451 = lemma_pats pats in
                      (binders1, pre, post, uu____10451)
                  | uu____10468 -> failwith "impos"))
        | uu____10487 -> failwith "Impos" in
      match uu____10299 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___157_10535 = env in
            {
              bindings = (uu___157_10535.bindings);
              depth = (uu___157_10535.depth);
              tcenv = (uu___157_10535.tcenv);
              warn = (uu___157_10535.warn);
              cache = (uu___157_10535.cache);
              nolabels = (uu___157_10535.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___157_10535.encode_non_total_function_typ);
              current_module_name = (uu___157_10535.current_module_name)
            } in
          let uu____10536 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10536 with
           | (vars,guards,env2,decls,uu____10561) ->
               let uu____10574 =
                 let uu____10587 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10631 =
                             let uu____10640 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10640
                               FStar_List.unzip in
                           match uu____10631 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10587 FStar_List.unzip in
               (match uu____10574 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___158_10749 = env2 in
                      {
                        bindings = (uu___158_10749.bindings);
                        depth = (uu___158_10749.depth);
                        tcenv = (uu___158_10749.tcenv);
                        warn = (uu___158_10749.warn);
                        cache = (uu___158_10749.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___158_10749.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___158_10749.encode_non_total_function_typ);
                        current_module_name =
                          (uu___158_10749.current_module_name)
                      } in
                    let uu____10750 =
                      let uu____10755 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10755 env3 in
                    (match uu____10750 with
                     | (pre1,decls'') ->
                         let uu____10762 =
                           let uu____10767 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10767 env3 in
                         (match uu____10762 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10777 =
                                let uu____10778 =
                                  let uu____10789 =
                                    let uu____10790 =
                                      let uu____10795 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10795, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10790 in
                                  (pats, vars, uu____10789) in
                                FStar_SMTEncoding_Util.mkForall uu____10778 in
                              (uu____10777, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10814 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10814
        then
          let uu____10815 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10816 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10815 uu____10816
        else () in
      let enc f r l =
        let uu____10849 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10877 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10877 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10849 with
        | (decls,args) ->
            let uu____10906 =
              let uu___159_10907 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___159_10907.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___159_10907.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10906, decls) in
      let const_op f r uu____10938 =
        let uu____10951 = f r in (uu____10951, []) in
      let un_op f l =
        let uu____10970 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10970 in
      let bin_op f uu___133_10986 =
        match uu___133_10986 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10997 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11031 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11054  ->
                 match uu____11054 with
                 | (t,uu____11068) ->
                     let uu____11069 = encode_formula t env in
                     (match uu____11069 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11031 with
        | (decls,phis) ->
            let uu____11098 =
              let uu___160_11099 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___160_11099.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___160_11099.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11098, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11160  ->
               match uu____11160 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11179) -> false
                    | uu____11180 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11195 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11195
        else
          (let uu____11209 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11209 r rf) in
      let mk_imp1 r uu___134_11234 =
        match uu___134_11234 with
        | (lhs,uu____11240)::(rhs,uu____11242)::[] ->
            let uu____11269 = encode_formula rhs env in
            (match uu____11269 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11284) ->
                      (l1, decls1)
                  | uu____11289 ->
                      let uu____11290 = encode_formula lhs env in
                      (match uu____11290 with
                       | (l2,decls2) ->
                           let uu____11301 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11301, (FStar_List.append decls1 decls2)))))
        | uu____11304 -> failwith "impossible" in
      let mk_ite r uu___135_11325 =
        match uu___135_11325 with
        | (guard,uu____11331)::(_then,uu____11333)::(_else,uu____11335)::[]
            ->
            let uu____11372 = encode_formula guard env in
            (match uu____11372 with
             | (g,decls1) ->
                 let uu____11383 = encode_formula _then env in
                 (match uu____11383 with
                  | (t,decls2) ->
                      let uu____11394 = encode_formula _else env in
                      (match uu____11394 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11408 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11433 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11433 in
      let connectives =
        let uu____11451 =
          let uu____11464 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11464) in
        let uu____11481 =
          let uu____11496 =
            let uu____11509 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11509) in
          let uu____11526 =
            let uu____11541 =
              let uu____11556 =
                let uu____11569 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11569) in
              let uu____11586 =
                let uu____11601 =
                  let uu____11616 =
                    let uu____11629 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11629) in
                  [uu____11616;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11601 in
              uu____11556 :: uu____11586 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11541 in
          uu____11496 :: uu____11526 in
        uu____11451 :: uu____11481 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11950 = encode_formula phi' env in
            (match uu____11950 with
             | (phi2,decls) ->
                 let uu____11961 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11961, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11962 ->
            let uu____11969 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11969 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12008 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12008 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12020;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12022;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12043 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12043 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12090::(x,uu____12092)::(t,uu____12094)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12141 = encode_term x env in
                 (match uu____12141 with
                  | (x1,decls) ->
                      let uu____12152 = encode_term t env in
                      (match uu____12152 with
                       | (t1,decls') ->
                           let uu____12163 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12163, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12168)::(msg,uu____12170)::(phi2,uu____12172)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12217 =
                   let uu____12222 =
                     let uu____12223 = FStar_Syntax_Subst.compress r in
                     uu____12223.FStar_Syntax_Syntax.n in
                   let uu____12226 =
                     let uu____12227 = FStar_Syntax_Subst.compress msg in
                     uu____12227.FStar_Syntax_Syntax.n in
                   (uu____12222, uu____12226) in
                 (match uu____12217 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12236))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12242 -> fallback phi2)
             | uu____12247 when head_redex env head2 ->
                 let uu____12260 = whnf env phi1 in
                 encode_formula uu____12260 env
             | uu____12261 ->
                 let uu____12274 = encode_term phi1 env in
                 (match uu____12274 with
                  | (tt,decls) ->
                      let uu____12285 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___161_12288 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___161_12288.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___161_12288.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12285, decls)))
        | uu____12289 ->
            let uu____12290 = encode_term phi1 env in
            (match uu____12290 with
             | (tt,decls) ->
                 let uu____12301 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___162_12304 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___162_12304.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___162_12304.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12301, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12340 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12340 with
        | (vars,guards,env2,decls,uu____12379) ->
            let uu____12392 =
              let uu____12405 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12453 =
                          let uu____12462 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12492  ->
                                    match uu____12492 with
                                    | (t,uu____12502) ->
                                        encode_term t
                                          (let uu___163_12504 = env2 in
                                           {
                                             bindings =
                                               (uu___163_12504.bindings);
                                             depth = (uu___163_12504.depth);
                                             tcenv = (uu___163_12504.tcenv);
                                             warn = (uu___163_12504.warn);
                                             cache = (uu___163_12504.cache);
                                             nolabels =
                                               (uu___163_12504.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___163_12504.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___163_12504.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12462 FStar_List.unzip in
                        match uu____12453 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12405 FStar_List.unzip in
            (match uu____12392 with
             | (pats,decls') ->
                 let uu____12603 = encode_formula body env2 in
                 (match uu____12603 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12635;
                             FStar_SMTEncoding_Term.rng = uu____12636;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12651 -> guards in
                      let uu____12656 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12656, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12716  ->
                   match uu____12716 with
                   | (x,uu____12722) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12730 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12742 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12742) uu____12730 tl1 in
             let uu____12745 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12772  ->
                       match uu____12772 with
                       | (b,uu____12778) ->
                           let uu____12779 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12779)) in
             (match uu____12745 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12785) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12799 =
                    let uu____12800 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12800 in
                  FStar_Errors.warn pos uu____12799) in
       let uu____12801 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12801 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12810 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12868  ->
                     match uu____12868 with
                     | (l,uu____12882) -> FStar_Ident.lid_equals op l)) in
           (match uu____12810 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12915,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12955 = encode_q_body env vars pats body in
             match uu____12955 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13000 =
                     let uu____13011 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13011) in
                   FStar_SMTEncoding_Term.mkForall uu____13000
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13030 = encode_q_body env vars pats body in
             match uu____13030 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13074 =
                   let uu____13075 =
                     let uu____13086 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13086) in
                   FStar_SMTEncoding_Term.mkExists uu____13075
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13074, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2;
  is: FStar_Ident.lident -> Prims.bool;}[@@deriving show]
let __proj__Mkprims_t__item__mk:
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
let __proj__Mkprims_t__item__is: prims_t -> FStar_Ident.lident -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
let prims: prims_t =
  let uu____13184 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13184 with
  | (asym,a) ->
      let uu____13191 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13191 with
       | (xsym,x) ->
           let uu____13198 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13198 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13242 =
                      let uu____13253 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13253, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13242 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13279 =
                      let uu____13286 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13286) in
                    FStar_SMTEncoding_Util.mkApp uu____13279 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13299 =
                    let uu____13302 =
                      let uu____13305 =
                        let uu____13308 =
                          let uu____13309 =
                            let uu____13316 =
                              let uu____13317 =
                                let uu____13328 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13328) in
                              FStar_SMTEncoding_Util.mkForall uu____13317 in
                            (uu____13316, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13309 in
                        let uu____13345 =
                          let uu____13348 =
                            let uu____13349 =
                              let uu____13356 =
                                let uu____13357 =
                                  let uu____13368 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13368) in
                                FStar_SMTEncoding_Util.mkForall uu____13357 in
                              (uu____13356,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13349 in
                          [uu____13348] in
                        uu____13308 :: uu____13345 in
                      xtok_decl :: uu____13305 in
                    xname_decl :: uu____13302 in
                  (xtok1, uu____13299) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13459 =
                    let uu____13472 =
                      let uu____13481 =
                        let uu____13482 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13482 in
                      quant axy uu____13481 in
                    (FStar_Parser_Const.op_Eq, uu____13472) in
                  let uu____13491 =
                    let uu____13506 =
                      let uu____13519 =
                        let uu____13528 =
                          let uu____13529 =
                            let uu____13530 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13530 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13529 in
                        quant axy uu____13528 in
                      (FStar_Parser_Const.op_notEq, uu____13519) in
                    let uu____13539 =
                      let uu____13554 =
                        let uu____13567 =
                          let uu____13576 =
                            let uu____13577 =
                              let uu____13578 =
                                let uu____13583 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13584 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13583, uu____13584) in
                              FStar_SMTEncoding_Util.mkLT uu____13578 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13577 in
                          quant xy uu____13576 in
                        (FStar_Parser_Const.op_LT, uu____13567) in
                      let uu____13593 =
                        let uu____13608 =
                          let uu____13621 =
                            let uu____13630 =
                              let uu____13631 =
                                let uu____13632 =
                                  let uu____13637 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13638 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13637, uu____13638) in
                                FStar_SMTEncoding_Util.mkLTE uu____13632 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13631 in
                            quant xy uu____13630 in
                          (FStar_Parser_Const.op_LTE, uu____13621) in
                        let uu____13647 =
                          let uu____13662 =
                            let uu____13675 =
                              let uu____13684 =
                                let uu____13685 =
                                  let uu____13686 =
                                    let uu____13691 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13692 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13691, uu____13692) in
                                  FStar_SMTEncoding_Util.mkGT uu____13686 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13685 in
                              quant xy uu____13684 in
                            (FStar_Parser_Const.op_GT, uu____13675) in
                          let uu____13701 =
                            let uu____13716 =
                              let uu____13729 =
                                let uu____13738 =
                                  let uu____13739 =
                                    let uu____13740 =
                                      let uu____13745 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13746 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13745, uu____13746) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13740 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13739 in
                                quant xy uu____13738 in
                              (FStar_Parser_Const.op_GTE, uu____13729) in
                            let uu____13755 =
                              let uu____13770 =
                                let uu____13783 =
                                  let uu____13792 =
                                    let uu____13793 =
                                      let uu____13794 =
                                        let uu____13799 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13800 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13799, uu____13800) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13794 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13793 in
                                  quant xy uu____13792 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13783) in
                              let uu____13809 =
                                let uu____13824 =
                                  let uu____13837 =
                                    let uu____13846 =
                                      let uu____13847 =
                                        let uu____13848 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13848 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13847 in
                                    quant qx uu____13846 in
                                  (FStar_Parser_Const.op_Minus, uu____13837) in
                                let uu____13857 =
                                  let uu____13872 =
                                    let uu____13885 =
                                      let uu____13894 =
                                        let uu____13895 =
                                          let uu____13896 =
                                            let uu____13901 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13902 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13901, uu____13902) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13896 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13895 in
                                      quant xy uu____13894 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13885) in
                                  let uu____13911 =
                                    let uu____13926 =
                                      let uu____13939 =
                                        let uu____13948 =
                                          let uu____13949 =
                                            let uu____13950 =
                                              let uu____13955 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13956 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13955, uu____13956) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13950 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13949 in
                                        quant xy uu____13948 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13939) in
                                    let uu____13965 =
                                      let uu____13980 =
                                        let uu____13993 =
                                          let uu____14002 =
                                            let uu____14003 =
                                              let uu____14004 =
                                                let uu____14009 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14010 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____14009, uu____14010) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14004 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14003 in
                                          quant xy uu____14002 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13993) in
                                      let uu____14019 =
                                        let uu____14034 =
                                          let uu____14047 =
                                            let uu____14056 =
                                              let uu____14057 =
                                                let uu____14058 =
                                                  let uu____14063 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14064 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14063, uu____14064) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14058 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14057 in
                                            quant xy uu____14056 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14047) in
                                        let uu____14073 =
                                          let uu____14088 =
                                            let uu____14101 =
                                              let uu____14110 =
                                                let uu____14111 =
                                                  let uu____14112 =
                                                    let uu____14117 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14118 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14117,
                                                      uu____14118) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14112 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14111 in
                                              quant xy uu____14110 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14101) in
                                          let uu____14127 =
                                            let uu____14142 =
                                              let uu____14155 =
                                                let uu____14164 =
                                                  let uu____14165 =
                                                    let uu____14166 =
                                                      let uu____14171 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14172 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14171,
                                                        uu____14172) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14166 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14165 in
                                                quant xy uu____14164 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14155) in
                                            let uu____14181 =
                                              let uu____14196 =
                                                let uu____14209 =
                                                  let uu____14218 =
                                                    let uu____14219 =
                                                      let uu____14220 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14220 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14219 in
                                                  quant qx uu____14218 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14209) in
                                              [uu____14196] in
                                            uu____14142 :: uu____14181 in
                                          uu____14088 :: uu____14127 in
                                        uu____14034 :: uu____14073 in
                                      uu____13980 :: uu____14019 in
                                    uu____13926 :: uu____13965 in
                                  uu____13872 :: uu____13911 in
                                uu____13824 :: uu____13857 in
                              uu____13770 :: uu____13809 in
                            uu____13716 :: uu____13755 in
                          uu____13662 :: uu____13701 in
                        uu____13608 :: uu____13647 in
                      uu____13554 :: uu____13593 in
                    uu____13506 :: uu____13539 in
                  uu____13459 :: uu____13491 in
                let mk1 l v1 =
                  let uu____14434 =
                    let uu____14443 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14501  ->
                              match uu____14501 with
                              | (l',uu____14515) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14443
                      (FStar_Option.map
                         (fun uu____14575  ->
                            match uu____14575 with | (uu____14594,b) -> b v1)) in
                  FStar_All.pipe_right uu____14434 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14665  ->
                          match uu____14665 with
                          | (l',uu____14679) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____14720 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14720 with
        | (xxsym,xx) ->
            let uu____14727 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14727 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14737 =
                   let uu____14744 =
                     let uu____14745 =
                       let uu____14756 =
                         let uu____14757 =
                           let uu____14762 =
                             let uu____14763 =
                               let uu____14768 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14768) in
                             FStar_SMTEncoding_Util.mkEq uu____14763 in
                           (xx_has_type, uu____14762) in
                         FStar_SMTEncoding_Util.mkImp uu____14757 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14756) in
                     FStar_SMTEncoding_Util.mkForall uu____14745 in
                   let uu____14793 =
                     let uu____14794 =
                       let uu____14795 =
                         let uu____14796 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14796 in
                       Prims.strcat module_name uu____14795 in
                     varops.mk_unique uu____14794 in
                   (uu____14744, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14793) in
                 FStar_SMTEncoding_Util.mkAssume uu____14737)
let primitive_type_axioms:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____14836 =
      let uu____14837 =
        let uu____14844 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14844, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14837 in
    let uu____14847 =
      let uu____14850 =
        let uu____14851 =
          let uu____14858 =
            let uu____14859 =
              let uu____14870 =
                let uu____14871 =
                  let uu____14876 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14876) in
                FStar_SMTEncoding_Util.mkImp uu____14871 in
              ([[typing_pred]], [xx], uu____14870) in
            mkForall_fuel uu____14859 in
          (uu____14858, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14851 in
      [uu____14850] in
    uu____14836 :: uu____14847 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14918 =
      let uu____14919 =
        let uu____14926 =
          let uu____14927 =
            let uu____14938 =
              let uu____14943 =
                let uu____14946 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14946] in
              [uu____14943] in
            let uu____14951 =
              let uu____14952 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14952 tt in
            (uu____14938, [bb], uu____14951) in
          FStar_SMTEncoding_Util.mkForall uu____14927 in
        (uu____14926, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14919 in
    let uu____14973 =
      let uu____14976 =
        let uu____14977 =
          let uu____14984 =
            let uu____14985 =
              let uu____14996 =
                let uu____14997 =
                  let uu____15002 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____15002) in
                FStar_SMTEncoding_Util.mkImp uu____14997 in
              ([[typing_pred]], [xx], uu____14996) in
            mkForall_fuel uu____14985 in
          (uu____14984, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14977 in
      [uu____14976] in
    uu____14918 :: uu____14973 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15052 =
        let uu____15053 =
          let uu____15060 =
            let uu____15063 =
              let uu____15066 =
                let uu____15069 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15070 =
                  let uu____15073 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15073] in
                uu____15069 :: uu____15070 in
              tt :: uu____15066 in
            tt :: uu____15063 in
          ("Prims.Precedes", uu____15060) in
        FStar_SMTEncoding_Util.mkApp uu____15053 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15052 in
    let precedes_y_x =
      let uu____15077 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15077 in
    let uu____15080 =
      let uu____15081 =
        let uu____15088 =
          let uu____15089 =
            let uu____15100 =
              let uu____15105 =
                let uu____15108 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15108] in
              [uu____15105] in
            let uu____15113 =
              let uu____15114 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15114 tt in
            (uu____15100, [bb], uu____15113) in
          FStar_SMTEncoding_Util.mkForall uu____15089 in
        (uu____15088, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15081 in
    let uu____15135 =
      let uu____15138 =
        let uu____15139 =
          let uu____15146 =
            let uu____15147 =
              let uu____15158 =
                let uu____15159 =
                  let uu____15164 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15164) in
                FStar_SMTEncoding_Util.mkImp uu____15159 in
              ([[typing_pred]], [xx], uu____15158) in
            mkForall_fuel uu____15147 in
          (uu____15146, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15139 in
      let uu____15189 =
        let uu____15192 =
          let uu____15193 =
            let uu____15200 =
              let uu____15201 =
                let uu____15212 =
                  let uu____15213 =
                    let uu____15218 =
                      let uu____15219 =
                        let uu____15222 =
                          let uu____15225 =
                            let uu____15228 =
                              let uu____15229 =
                                let uu____15234 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15235 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15234, uu____15235) in
                              FStar_SMTEncoding_Util.mkGT uu____15229 in
                            let uu____15236 =
                              let uu____15239 =
                                let uu____15240 =
                                  let uu____15245 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15246 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15245, uu____15246) in
                                FStar_SMTEncoding_Util.mkGTE uu____15240 in
                              let uu____15247 =
                                let uu____15250 =
                                  let uu____15251 =
                                    let uu____15256 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15257 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15256, uu____15257) in
                                  FStar_SMTEncoding_Util.mkLT uu____15251 in
                                [uu____15250] in
                              uu____15239 :: uu____15247 in
                            uu____15228 :: uu____15236 in
                          typing_pred_y :: uu____15225 in
                        typing_pred :: uu____15222 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15219 in
                    (uu____15218, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15213 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15212) in
              mkForall_fuel uu____15201 in
            (uu____15200,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15193 in
        [uu____15192] in
      uu____15138 :: uu____15189 in
    uu____15080 :: uu____15135 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15303 =
      let uu____15304 =
        let uu____15311 =
          let uu____15312 =
            let uu____15323 =
              let uu____15328 =
                let uu____15331 = FStar_SMTEncoding_Term.boxString b in
                [uu____15331] in
              [uu____15328] in
            let uu____15336 =
              let uu____15337 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15337 tt in
            (uu____15323, [bb], uu____15336) in
          FStar_SMTEncoding_Util.mkForall uu____15312 in
        (uu____15311, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15304 in
    let uu____15358 =
      let uu____15361 =
        let uu____15362 =
          let uu____15369 =
            let uu____15370 =
              let uu____15381 =
                let uu____15382 =
                  let uu____15387 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15387) in
                FStar_SMTEncoding_Util.mkImp uu____15382 in
              ([[typing_pred]], [xx], uu____15381) in
            mkForall_fuel uu____15370 in
          (uu____15369, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15362 in
      [uu____15361] in
    uu____15303 :: uu____15358 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15440 =
      let uu____15441 =
        let uu____15448 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15448, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15441 in
    [uu____15440] in
  let mk_and_interp env conj uu____15460 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15485 =
      let uu____15486 =
        let uu____15493 =
          let uu____15494 =
            let uu____15505 =
              let uu____15506 =
                let uu____15511 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15511, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15506 in
            ([[l_and_a_b]], [aa; bb], uu____15505) in
          FStar_SMTEncoding_Util.mkForall uu____15494 in
        (uu____15493, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15486 in
    [uu____15485] in
  let mk_or_interp env disj uu____15549 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15574 =
      let uu____15575 =
        let uu____15582 =
          let uu____15583 =
            let uu____15594 =
              let uu____15595 =
                let uu____15600 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15600, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15595 in
            ([[l_or_a_b]], [aa; bb], uu____15594) in
          FStar_SMTEncoding_Util.mkForall uu____15583 in
        (uu____15582, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15575 in
    [uu____15574] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15663 =
      let uu____15664 =
        let uu____15671 =
          let uu____15672 =
            let uu____15683 =
              let uu____15684 =
                let uu____15689 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15689, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15684 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15683) in
          FStar_SMTEncoding_Util.mkForall uu____15672 in
        (uu____15671, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15664 in
    [uu____15663] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____15762 =
      let uu____15763 =
        let uu____15770 =
          let uu____15771 =
            let uu____15782 =
              let uu____15783 =
                let uu____15788 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15788, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15783 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15782) in
          FStar_SMTEncoding_Util.mkForall uu____15771 in
        (uu____15770, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15763 in
    [uu____15762] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15859 =
      let uu____15860 =
        let uu____15867 =
          let uu____15868 =
            let uu____15879 =
              let uu____15880 =
                let uu____15885 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15885, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15880 in
            ([[l_imp_a_b]], [aa; bb], uu____15879) in
          FStar_SMTEncoding_Util.mkForall uu____15868 in
        (uu____15867, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15860 in
    [uu____15859] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15948 =
      let uu____15949 =
        let uu____15956 =
          let uu____15957 =
            let uu____15968 =
              let uu____15969 =
                let uu____15974 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15974, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15969 in
            ([[l_iff_a_b]], [aa; bb], uu____15968) in
          FStar_SMTEncoding_Util.mkForall uu____15957 in
        (uu____15956, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15949 in
    [uu____15948] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16026 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16026 in
    let uu____16029 =
      let uu____16030 =
        let uu____16037 =
          let uu____16038 =
            let uu____16049 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16049) in
          FStar_SMTEncoding_Util.mkForall uu____16038 in
        (uu____16037, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16030 in
    [uu____16029] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b]) in
    let valid_b_x =
      let uu____16109 =
        let uu____16116 =
          let uu____16119 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16119] in
        ("Valid", uu____16116) in
      FStar_SMTEncoding_Util.mkApp uu____16109 in
    let uu____16122 =
      let uu____16123 =
        let uu____16130 =
          let uu____16131 =
            let uu____16142 =
              let uu____16143 =
                let uu____16148 =
                  let uu____16149 =
                    let uu____16160 =
                      let uu____16165 =
                        let uu____16168 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16168] in
                      [uu____16165] in
                    let uu____16173 =
                      let uu____16174 =
                        let uu____16179 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16179, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16174 in
                    (uu____16160, [xx1], uu____16173) in
                  FStar_SMTEncoding_Util.mkForall uu____16149 in
                (uu____16148, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16143 in
            ([[l_forall_a_b]], [aa; bb], uu____16142) in
          FStar_SMTEncoding_Util.mkForall uu____16131 in
        (uu____16130, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16123 in
    [uu____16122] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b]) in
    let valid_b_x =
      let uu____16261 =
        let uu____16268 =
          let uu____16271 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16271] in
        ("Valid", uu____16268) in
      FStar_SMTEncoding_Util.mkApp uu____16261 in
    let uu____16274 =
      let uu____16275 =
        let uu____16282 =
          let uu____16283 =
            let uu____16294 =
              let uu____16295 =
                let uu____16300 =
                  let uu____16301 =
                    let uu____16312 =
                      let uu____16317 =
                        let uu____16320 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16320] in
                      [uu____16317] in
                    let uu____16325 =
                      let uu____16326 =
                        let uu____16331 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16331, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16326 in
                    (uu____16312, [xx1], uu____16325) in
                  FStar_SMTEncoding_Util.mkExists uu____16301 in
                (uu____16300, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16295 in
            ([[l_exists_a_b]], [aa; bb], uu____16294) in
          FStar_SMTEncoding_Util.mkForall uu____16283 in
        (uu____16282, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16275 in
    [uu____16274] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16391 =
      let uu____16392 =
        let uu____16399 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16400 = varops.mk_unique "typing_range_const" in
        (uu____16399, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16400) in
      FStar_SMTEncoding_Util.mkAssume uu____16392 in
    [uu____16391] in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t]) in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t in
      let hastypeS =
        let uu____16434 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16434 x1 t in
      let uu____16435 =
        let uu____16446 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16446) in
      FStar_SMTEncoding_Util.mkForall uu____16435 in
    let uu____16469 =
      let uu____16470 =
        let uu____16477 =
          let uu____16478 =
            let uu____16489 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16489) in
          FStar_SMTEncoding_Util.mkForall uu____16478 in
        (uu____16477,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16470 in
    [uu____16469] in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.forall_lid, mk_forall_interp);
    (FStar_Parser_Const.exists_lid, mk_exists_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____16813 =
            FStar_Util.find_opt
              (fun uu____16839  ->
                 match uu____16839 with
                 | (l,uu____16851) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16813 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16876,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16915 = encode_function_type_as_formula t env in
        match uu____16915 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,env_t)
                FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let uu____16961 =
                ((let uu____16964 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16964) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16961
              then
                let uu____16971 = new_term_constant_and_tok_from_lid env lid in
                match uu____16971 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16990 =
                        let uu____16991 = FStar_Syntax_Subst.compress t_norm in
                        uu____16991.FStar_Syntax_Syntax.n in
                      match uu____16990 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16997) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17027  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17032 -> [] in
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function")) in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function")) in
                    ([d; dd], env1)
              else
                (let uu____17046 = prims.is lid in
                 if uu____17046
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17054 = prims.mk lid vname in
                   match uu____17054 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17078 =
                      let uu____17089 = curried_arrow_formals_comp t_norm in
                      match uu____17089 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17107 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17107
                            then
                              let uu____17108 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___164_17111 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___164_17111.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___164_17111.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___164_17111.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___164_17111.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___164_17111.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___164_17111.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___164_17111.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___164_17111.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___164_17111.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___164_17111.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___164_17111.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___164_17111.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___164_17111.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___164_17111.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___164_17111.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___164_17111.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___164_17111.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___164_17111.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___164_17111.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___164_17111.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___164_17111.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___164_17111.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___164_17111.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___164_17111.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___164_17111.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___164_17111.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___164_17111.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___164_17111.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___164_17111.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___164_17111.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___164_17111.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___164_17111.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17108
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17123 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17123)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17078 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17168 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17168 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17189 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___136_17231  ->
                                       match uu___136_17231 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17235 =
                                             FStar_Util.prefix vars in
                                           (match uu____17235 with
                                            | (uu____17256,(xxsym,uu____17258))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17276 =
                                                  let uu____17277 =
                                                    let uu____17284 =
                                                      let uu____17285 =
                                                        let uu____17296 =
                                                          let uu____17297 =
                                                            let uu____17302 =
                                                              let uu____17303
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17303 in
                                                            (vapp,
                                                              uu____17302) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17297 in
                                                        ([[vapp]], vars,
                                                          uu____17296) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17285 in
                                                    (uu____17284,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17277 in
                                                [uu____17276])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17322 =
                                             FStar_Util.prefix vars in
                                           (match uu____17322 with
                                            | (uu____17343,(xxsym,uu____17345))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  } in
                                                let tp_name =
                                                  mk_term_projector_name d f1 in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx]) in
                                                let uu____17368 =
                                                  let uu____17369 =
                                                    let uu____17376 =
                                                      let uu____17377 =
                                                        let uu____17388 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17388) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17377 in
                                                    (uu____17376,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17369 in
                                                [uu____17368])
                                       | uu____17405 -> [])) in
                             let uu____17406 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17406 with
                              | (vars,guards,env',decls1,uu____17433) ->
                                  let uu____17446 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17455 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17455, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17457 =
                                          encode_formula p env' in
                                        (match uu____17457 with
                                         | (g,ds) ->
                                             let uu____17468 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17468,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17446 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17481 =
                                           let uu____17488 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17488) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17481 in
                                       let uu____17497 =
                                         let vname_decl =
                                           let uu____17505 =
                                             let uu____17516 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17526  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17516,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17505 in
                                         let uu____17535 =
                                           let env2 =
                                             let uu___165_17541 = env1 in
                                             {
                                               bindings =
                                                 (uu___165_17541.bindings);
                                               depth = (uu___165_17541.depth);
                                               tcenv = (uu___165_17541.tcenv);
                                               warn = (uu___165_17541.warn);
                                               cache = (uu___165_17541.cache);
                                               nolabels =
                                                 (uu___165_17541.nolabels);
                                               use_zfuel_name =
                                                 (uu___165_17541.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___165_17541.current_module_name)
                                             } in
                                           let uu____17542 =
                                             let uu____17543 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17543 in
                                           if uu____17542
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17535 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17558::uu____17559 ->
                                                   let ff =
                                                     ("ty",
                                                       FStar_SMTEncoding_Term.Term_sort) in
                                                   let f =
                                                     FStar_SMTEncoding_Util.mkFreeV
                                                       ff in
                                                   let vtok_app_l =
                                                     mk_Apply vtok_tm [ff] in
                                                   let vtok_app_r =
                                                     mk_Apply f
                                                       [(vtok,
                                                          FStar_SMTEncoding_Term.Term_sort)] in
                                                   let guarded_tok_typing =
                                                     let uu____17599 =
                                                       let uu____17610 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17610) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17599 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17637 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17640 =
                                               match formals with
                                               | [] ->
                                                   let uu____17657 =
                                                     let uu____17658 =
                                                       let uu____17661 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17661 in
                                                     push_free_var env1 lid
                                                       vname uu____17658 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17657)
                                               | uu____17666 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17673 =
                                                       let uu____17680 =
                                                         let uu____17681 =
                                                           let uu____17692 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17692) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17681 in
                                                       (uu____17680,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17673 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17640 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17497 with
                                        | (decls2,env2) ->
                                            let uu____17735 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17743 =
                                                encode_term res_t1 env' in
                                              match uu____17743 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17756 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17756, decls) in
                                            (match uu____17735 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17767 =
                                                     let uu____17774 =
                                                       let uu____17775 =
                                                         let uu____17786 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17786) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17775 in
                                                     (uu____17774,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17767 in
                                                 let freshness =
                                                   let uu____17802 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17802
                                                   then
                                                     let uu____17807 =
                                                       let uu____17808 =
                                                         let uu____17819 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17830 =
                                                           varops.next_id () in
                                                         (vname, uu____17819,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17830) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17808 in
                                                     let uu____17833 =
                                                       let uu____17836 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17836] in
                                                     uu____17807 ::
                                                       uu____17833
                                                   else [] in
                                                 let g =
                                                   let uu____17841 =
                                                     let uu____17844 =
                                                       let uu____17847 =
                                                         let uu____17850 =
                                                           let uu____17853 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17853 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17850 in
                                                       FStar_List.append
                                                         decls3 uu____17847 in
                                                     FStar_List.append decls2
                                                       uu____17844 in
                                                   FStar_List.append decls11
                                                     uu____17841 in
                                                 (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string,FStar_SMTEncoding_Term.term
                           FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2,FStar_SMTEncoding_Term.decl
                                              Prims.list,env_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____17888 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17888 with
          | FStar_Pervasives_Native.None  ->
              let uu____17925 = encode_free_var false env x t t_norm [] in
              (match uu____17925 with
               | (decls,env1) ->
                   let uu____17952 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17952 with
                    | (n1,x',uu____17979) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18000) ->
              ((n1, x1), [], env)
let encode_top_level_val:
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm env t in
            let uu____18060 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18060 with
            | (decls,env1) ->
                let uu____18079 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18079
                then
                  let uu____18086 =
                    let uu____18089 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18089 in
                  (uu____18086, env1)
                else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____18144  ->
                fun lb  ->
                  match uu____18144 with
                  | (decls,env1) ->
                      let uu____18164 =
                        let uu____18171 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18171
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18164 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18193 = FStar_Syntax_Util.head_and_args t in
    match uu____18193 with
    | (hd1,args) ->
        let uu____18230 =
          let uu____18231 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18231.FStar_Syntax_Syntax.n in
        (match uu____18230 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18235,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18254 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18279  ->
      fun quals  ->
        match uu____18279 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18355 = FStar_Util.first_N nbinders formals in
              match uu____18355 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18436  ->
                         fun uu____18437  ->
                           match (uu____18436, uu____18437) with
                           | ((formal,uu____18455),(binder,uu____18457)) ->
                               let uu____18466 =
                                 let uu____18473 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18473) in
                               FStar_Syntax_Syntax.NT uu____18466) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18481 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18512  ->
                              match uu____18512 with
                              | (x,i) ->
                                  let uu____18523 =
                                    let uu___166_18524 = x in
                                    let uu____18525 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___166_18524.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___166_18524.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18525
                                    } in
                                  (uu____18523, i))) in
                    FStar_All.pipe_right uu____18481
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18543 =
                      let uu____18544 = FStar_Syntax_Subst.compress body in
                      let uu____18545 =
                        let uu____18546 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18546 in
                      FStar_Syntax_Syntax.extend_app_n uu____18544
                        uu____18545 in
                    uu____18543 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18607 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18607
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___167_18610 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___167_18610.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___167_18610.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___167_18610.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___167_18610.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___167_18610.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___167_18610.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___167_18610.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___167_18610.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___167_18610.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___167_18610.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___167_18610.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___167_18610.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___167_18610.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___167_18610.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___167_18610.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___167_18610.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___167_18610.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___167_18610.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___167_18610.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___167_18610.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___167_18610.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___167_18610.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___167_18610.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___167_18610.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___167_18610.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___167_18610.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___167_18610.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___167_18610.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___167_18610.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___167_18610.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___167_18610.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___167_18610.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18643 = FStar_Syntax_Util.abs_formals e in
                match uu____18643 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18707::uu____18708 ->
                         let uu____18723 =
                           let uu____18724 =
                             let uu____18727 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18727 in
                           uu____18724.FStar_Syntax_Syntax.n in
                         (match uu____18723 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18770 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18770 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18812 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18812
                                   then
                                     let uu____18847 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18847 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18941  ->
                                                   fun uu____18942  ->
                                                     match (uu____18941,
                                                             uu____18942)
                                                     with
                                                     | ((x,uu____18960),
                                                        (b,uu____18962)) ->
                                                         let uu____18971 =
                                                           let uu____18978 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18978) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18971)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18980 =
                                            let uu____19001 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19001) in
                                          (uu____18980, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19069 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19069 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19158) ->
                              let uu____19163 =
                                let uu____19184 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19184 in
                              (uu____19163, true)
                          | uu____19249 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.WHNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____19251 ->
                              let uu____19252 =
                                let uu____19253 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19254 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19253
                                  uu____19254 in
                              failwith uu____19252)
                     | uu____19279 ->
                         let uu____19280 =
                           let uu____19281 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19281.FStar_Syntax_Syntax.n in
                         (match uu____19280 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19326 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19326 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19358 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19358 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19441 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19497 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19497
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19509 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19603  ->
                            fun lb  ->
                              match uu____19603 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19698 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19698
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19701 =
                                      let uu____19716 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19716
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19701 with
                                    | (tok,decl,env2) ->
                                        let uu____19762 =
                                          let uu____19775 =
                                            let uu____19786 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19786, tok) in
                                          uu____19775 :: toks in
                                        (uu____19762, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19509 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten in
                      let typs1 = FStar_List.rev typs in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____19969 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19977 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19977 vars)
                            else
                              (let uu____19979 =
                                 let uu____19986 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19986) in
                               FStar_SMTEncoding_Util.mkApp uu____19979) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20068;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20070;
                             FStar_Syntax_Syntax.lbeff = uu____20071;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20134 =
                              let uu____20141 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20141 with
                              | (tcenv',uu____20159,e_t) ->
                                  let uu____20165 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20176 -> failwith "Impossible" in
                                  (match uu____20165 with
                                   | (e1,t_norm1) ->
                                       ((let uu___170_20192 = env2 in
                                         {
                                           bindings =
                                             (uu___170_20192.bindings);
                                           depth = (uu___170_20192.depth);
                                           tcenv = tcenv';
                                           warn = (uu___170_20192.warn);
                                           cache = (uu___170_20192.cache);
                                           nolabels =
                                             (uu___170_20192.nolabels);
                                           use_zfuel_name =
                                             (uu___170_20192.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___170_20192.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___170_20192.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20134 with
                             | (env',e1,t_norm1) ->
                                 let uu____20202 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20202 with
                                  | ((binders,body,uu____20223,uu____20224),curry)
                                      ->
                                      ((let uu____20235 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20235
                                        then
                                          let uu____20236 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20237 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20236 uu____20237
                                        else ());
                                       (let uu____20239 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20239 with
                                        | (vars,guards,env'1,binder_decls,uu____20266)
                                            ->
                                            let body1 =
                                              let uu____20280 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20280
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20283 =
                                              let uu____20292 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20292
                                              then
                                                let uu____20303 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20304 =
                                                  encode_formula body1 env'1 in
                                                (uu____20303, uu____20304)
                                              else
                                                (let uu____20314 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20314)) in
                                            (match uu____20283 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20337 =
                                                     let uu____20344 =
                                                       let uu____20345 =
                                                         let uu____20356 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20356) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20345 in
                                                     let uu____20367 =
                                                       let uu____20370 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20370 in
                                                     (uu____20344,
                                                       uu____20367,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20337 in
                                                 let uu____20373 =
                                                   let uu____20376 =
                                                     let uu____20379 =
                                                       let uu____20382 =
                                                         let uu____20385 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20385 in
                                                       FStar_List.append
                                                         decls2 uu____20382 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20379 in
                                                   FStar_List.append decls1
                                                     uu____20376 in
                                                 (uu____20373, env2))))))
                        | uu____20390 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20475 = varops.fresh "fuel" in
                          (uu____20475, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20478 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20566  ->
                                  fun uu____20567  ->
                                    match (uu____20566, uu____20567) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20715 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20715 in
                                        let gtok =
                                          let uu____20717 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20717 in
                                        let env4 =
                                          let uu____20719 =
                                            let uu____20722 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20722 in
                                          push_free_var env3 flid gtok
                                            uu____20719 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20478 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20878 t_norm
                              uu____20880 =
                              match (uu____20878, uu____20880) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20924;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20925;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20953 =
                                    let uu____20960 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20960 with
                                    | (tcenv',uu____20982,e_t) ->
                                        let uu____20988 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20999 ->
                                              failwith "Impossible" in
                                        (match uu____20988 with
                                         | (e1,t_norm1) ->
                                             ((let uu___171_21015 = env3 in
                                               {
                                                 bindings =
                                                   (uu___171_21015.bindings);
                                                 depth =
                                                   (uu___171_21015.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___171_21015.warn);
                                                 cache =
                                                   (uu___171_21015.cache);
                                                 nolabels =
                                                   (uu___171_21015.nolabels);
                                                 use_zfuel_name =
                                                   (uu___171_21015.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___171_21015.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___171_21015.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20953 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21030 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____21030
                                         then
                                           let uu____21031 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____21032 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____21033 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21031 uu____21032
                                             uu____21033
                                         else ());
                                        (let uu____21035 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21035 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21072 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21072
                                               then
                                                 let uu____21073 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21074 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21075 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21076 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21073 uu____21074
                                                   uu____21075 uu____21076
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21080 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21080 with
                                               | (vars,guards,env'1,binder_decls,uu____21111)
                                                   ->
                                                   let decl_g =
                                                     let uu____21125 =
                                                       let uu____21136 =
                                                         let uu____21139 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21139 in
                                                       (g, uu____21136,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21125 in
                                                   let env02 =
                                                     push_zfuel_name env01
                                                       flid g in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications")) in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars in
                                                   let app =
                                                     let uu____21164 =
                                                       let uu____21171 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21171) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21164 in
                                                   let gsapp =
                                                     let uu____21181 =
                                                       let uu____21188 =
                                                         let uu____21191 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21191 ::
                                                           vars_tm in
                                                       (g, uu____21188) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21181 in
                                                   let gmax =
                                                     let uu____21197 =
                                                       let uu____21204 =
                                                         let uu____21207 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21207 ::
                                                           vars_tm in
                                                       (g, uu____21204) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21197 in
                                                   let body1 =
                                                     let uu____21213 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21213
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21215 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21215 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21233 =
                                                            let uu____21240 =
                                                              let uu____21241
                                                                =
                                                                let uu____21256
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21256) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21241 in
                                                            let uu____21277 =
                                                              let uu____21280
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21280 in
                                                            (uu____21240,
                                                              uu____21277,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21233 in
                                                        let eqn_f =
                                                          let uu____21284 =
                                                            let uu____21291 =
                                                              let uu____21292
                                                                =
                                                                let uu____21303
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21303) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21292 in
                                                            (uu____21291,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21284 in
                                                        let eqn_g' =
                                                          let uu____21317 =
                                                            let uu____21324 =
                                                              let uu____21325
                                                                =
                                                                let uu____21336
                                                                  =
                                                                  let uu____21337
                                                                    =
                                                                    let uu____21342
                                                                    =
                                                                    let uu____21343
                                                                    =
                                                                    let uu____21350
                                                                    =
                                                                    let uu____21353
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21353
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21350) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21343 in
                                                                    (gsapp,
                                                                    uu____21342) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21337 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21336) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21325 in
                                                            (uu____21324,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21317 in
                                                        let uu____21376 =
                                                          let uu____21385 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21385
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21414)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____21439
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21439
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21444
                                                                  =
                                                                  let uu____21451
                                                                    =
                                                                    let uu____21452
                                                                    =
                                                                    let uu____21463
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21463) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21452 in
                                                                  (uu____21451,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21444 in
                                                              let uu____21484
                                                                =
                                                                let uu____21491
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21491
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21504
                                                                    =
                                                                    let uu____21507
                                                                    =
                                                                    let uu____21508
                                                                    =
                                                                    let uu____21515
                                                                    =
                                                                    let uu____21516
                                                                    =
                                                                    let uu____21527
                                                                    =
                                                                    let uu____21528
                                                                    =
                                                                    let uu____21533
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21533,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21528 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21527) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21516 in
                                                                    (uu____21515,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21508 in
                                                                    [uu____21507] in
                                                                    (d3,
                                                                    uu____21504) in
                                                              (match uu____21484
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21376
                                                         with
                                                         | (aux_decls,g_typing)
                                                             ->
                                                             ((FStar_List.append
                                                                 binder_decls
                                                                 (FStar_List.append
                                                                    decls2
                                                                    (
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                               (FStar_List.append
                                                                  [eqn_g;
                                                                  eqn_g';
                                                                  eqn_f]
                                                                  g_typing),
                                                               env02)))))))) in
                            let uu____21598 =
                              let uu____21611 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21690  ->
                                   fun uu____21691  ->
                                     match (uu____21690, uu____21691) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21846 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21846 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21611 in
                            (match uu____21598 with
                             | (decls2,eqns,env01) ->
                                 let uu____21919 =
                                   let isDeclFun uu___137_21931 =
                                     match uu___137_21931 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21932 -> true
                                     | uu____21943 -> false in
                                   let uu____21944 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21944
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21919 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21984 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___138_21988  ->
                                 match uu___138_21988 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21989 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21995 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21995))) in
                      if uu____21984
                      then (decls1, env1)
                      else
                        (try
                           if Prims.op_Negation is_rec
                           then
                             encode_non_rec_lbdef bindings typs1 toks1 env1
                           else encode_rec_lbdefs bindings typs1 toks1 env1
                         with | Inner_let_rec  -> (decls1, env1)))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____22047 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22047
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____22096 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22096 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22100 = encode_sigelt' env se in
      match uu____22100 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22116 =
                  let uu____22117 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22117 in
                [uu____22116]
            | uu____22118 ->
                let uu____22119 =
                  let uu____22122 =
                    let uu____22123 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22123 in
                  uu____22122 :: g in
                let uu____22124 =
                  let uu____22127 =
                    let uu____22128 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22128 in
                  [uu____22127] in
                FStar_List.append uu____22119 uu____22124 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22141 =
          let uu____22142 = FStar_Syntax_Subst.compress t in
          uu____22142.FStar_Syntax_Syntax.n in
        match uu____22141 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22146)) -> s = "opaque_to_smt"
        | uu____22147 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22152 =
          let uu____22153 = FStar_Syntax_Subst.compress t in
          uu____22153.FStar_Syntax_Syntax.n in
        match uu____22152 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22157)) -> s = "uninterpreted_by_smt"
        | uu____22158 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22163 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22168 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22171 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22174 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22189 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22193 =
            let uu____22194 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22194 Prims.op_Negation in
          if uu____22193
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22220 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____22240 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22240 with
               | (aname,atok,env2) ->
                   let uu____22256 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22256 with
                    | (formals,uu____22274) ->
                        let uu____22287 =
                          let uu____22292 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22292 env2 in
                        (match uu____22287 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22304 =
                                 let uu____22305 =
                                   let uu____22316 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22332  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22316,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22305 in
                               [uu____22304;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22345 =
                               let aux uu____22397 uu____22398 =
                                 match (uu____22397, uu____22398) with
                                 | ((bv,uu____22450),(env3,acc_sorts,acc)) ->
                                     let uu____22488 = gen_term_var env3 bv in
                                     (match uu____22488 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22345 with
                              | (uu____22560,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22583 =
                                      let uu____22590 =
                                        let uu____22591 =
                                          let uu____22602 =
                                            let uu____22603 =
                                              let uu____22608 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22608) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22603 in
                                          ([[app]], xs_sorts, uu____22602) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22591 in
                                      (uu____22590,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22583 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22628 =
                                      let uu____22635 =
                                        let uu____22636 =
                                          let uu____22647 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22647) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22636 in
                                      (uu____22635,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22628 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22666 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22666 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22694,uu____22695)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22696 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22696 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22713,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22719 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___139_22723  ->
                      match uu___139_22723 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22724 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22729 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22730 -> false)) in
            Prims.op_Negation uu____22719 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22739 =
               let uu____22746 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22746 env fv t quals in
             match uu____22739 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22761 =
                   let uu____22764 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22764 in
                 (uu____22761, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22772 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22772 with
           | (uu____22781,f1) ->
               let uu____22783 = encode_formula f1 env in
               (match uu____22783 with
                | (f2,decls) ->
                    let g =
                      let uu____22797 =
                        let uu____22798 =
                          let uu____22805 =
                            let uu____22808 =
                              let uu____22809 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22809 in
                            FStar_Pervasives_Native.Some uu____22808 in
                          let uu____22810 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22805, uu____22810) in
                        FStar_SMTEncoding_Util.mkAssume uu____22798 in
                      [uu____22797] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22816) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22828 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22846 =
                       let uu____22849 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22849.FStar_Syntax_Syntax.fv_name in
                     uu____22846.FStar_Syntax_Syntax.v in
                   let uu____22850 =
                     let uu____22851 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22851 in
                   if uu____22850
                   then
                     let val_decl =
                       let uu___174_22879 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___174_22879.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___174_22879.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___174_22879.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22884 = encode_sigelt' env1 val_decl in
                     match uu____22884 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22828 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22912,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22914;
                          FStar_Syntax_Syntax.lbtyp = uu____22915;
                          FStar_Syntax_Syntax.lbeff = uu____22916;
                          FStar_Syntax_Syntax.lbdef = uu____22917;_}::[]),uu____22918)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22937 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22937 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22966 =
                   let uu____22969 =
                     let uu____22970 =
                       let uu____22977 =
                         let uu____22978 =
                           let uu____22989 =
                             let uu____22990 =
                               let uu____22995 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22995) in
                             FStar_SMTEncoding_Util.mkEq uu____22990 in
                           ([[b2t_x]], [xx], uu____22989) in
                         FStar_SMTEncoding_Util.mkForall uu____22978 in
                       (uu____22977,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22970 in
                   [uu____22969] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22966 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23028,uu____23029) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___140_23038  ->
                  match uu___140_23038 with
                  | FStar_Syntax_Syntax.Discriminator uu____23039 -> true
                  | uu____23040 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23043,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23054 =
                     let uu____23055 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23055.FStar_Ident.idText in
                   uu____23054 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___141_23059  ->
                     match uu___141_23059 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23060 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23064) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___142_23081  ->
                  match uu___142_23081 with
                  | FStar_Syntax_Syntax.Projector uu____23082 -> true
                  | uu____23087 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23090 = try_lookup_free_var env l in
          (match uu____23090 with
           | FStar_Pervasives_Native.Some uu____23097 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___175_23101 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___175_23101.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___175_23101.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___175_23101.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23108) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23126) ->
          let uu____23135 = encode_sigelts env ses in
          (match uu____23135 with
           | (g,env1) ->
               let uu____23152 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___143_23175  ->
                         match uu___143_23175 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23176;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23177;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23178;_}
                             -> false
                         | uu____23181 -> true)) in
               (match uu____23152 with
                | (g',inversions) ->
                    let uu____23196 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___144_23217  ->
                              match uu___144_23217 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23218 ->
                                  true
                              | uu____23229 -> false)) in
                    (match uu____23196 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23247,tps,k,uu____23250,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___145_23267  ->
                    match uu___145_23267 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23268 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23277 = c in
              match uu____23277 with
              | (name,args,uu____23282,uu____23283,uu____23284) ->
                  let uu____23289 =
                    let uu____23290 =
                      let uu____23301 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23318  ->
                                match uu____23318 with
                                | (uu____23325,sort,uu____23327) -> sort)) in
                      (name, uu____23301, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23290 in
                  [uu____23289]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23354 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23360 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23360 FStar_Option.isNone)) in
            if uu____23354
            then []
            else
              (let uu____23392 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23392 with
               | (xxsym,xx) ->
                   let uu____23401 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23440  ->
                             fun l  ->
                               match uu____23440 with
                               | (out,decls) ->
                                   let uu____23460 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23460 with
                                    | (uu____23471,data_t) ->
                                        let uu____23473 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23473 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23519 =
                                                 let uu____23520 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23520.FStar_Syntax_Syntax.n in
                                               match uu____23519 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23531,indices) ->
                                                   indices
                                               | uu____23553 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23577  ->
                                                         match uu____23577
                                                         with
                                                         | (x,uu____23583) ->
                                                             let uu____23584
                                                               =
                                                               let uu____23585
                                                                 =
                                                                 let uu____23592
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23592,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23585 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23584)
                                                    env) in
                                             let uu____23595 =
                                               encode_args indices env1 in
                                             (match uu____23595 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____23621 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23637
                                                                 =
                                                                 let uu____23642
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23642,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23637)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23621
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23645 =
                                                      let uu____23646 =
                                                        let uu____23651 =
                                                          let uu____23652 =
                                                            let uu____23657 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23657,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23652 in
                                                        (out, uu____23651) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23646 in
                                                    (uu____23645,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23401 with
                    | (data_ax,decls) ->
                        let uu____23670 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23670 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23681 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23681 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23685 =
                                 let uu____23692 =
                                   let uu____23693 =
                                     let uu____23704 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23719 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23704,
                                       uu____23719) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23693 in
                                 let uu____23734 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23692,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23734) in
                               FStar_SMTEncoding_Util.mkAssume uu____23685 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23737 =
            let uu____23750 =
              let uu____23751 = FStar_Syntax_Subst.compress k in
              uu____23751.FStar_Syntax_Syntax.n in
            match uu____23750 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23796 -> (tps, k) in
          (match uu____23737 with
           | (formals,res) ->
               let uu____23819 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23819 with
                | (formals1,res1) ->
                    let uu____23830 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23830 with
                     | (vars,guards,env',binder_decls,uu____23855) ->
                         let uu____23868 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23868 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23887 =
                                  let uu____23894 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23894) in
                                FStar_SMTEncoding_Util.mkApp uu____23887 in
                              let uu____23903 =
                                let tname_decl =
                                  let uu____23913 =
                                    let uu____23914 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23946  ->
                                              match uu____23946 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23959 = varops.next_id () in
                                    (tname, uu____23914,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23959, false) in
                                  constructor_or_logic_type_decl uu____23913 in
                                let uu____23968 =
                                  match vars with
                                  | [] ->
                                      let uu____23981 =
                                        let uu____23982 =
                                          let uu____23985 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23985 in
                                        push_free_var env1 t tname
                                          uu____23982 in
                                      ([], uu____23981)
                                  | uu____23992 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24001 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24001 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24015 =
                                          let uu____24022 =
                                            let uu____24023 =
                                              let uu____24038 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24038) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24023 in
                                          (uu____24022,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24015 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23968 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23903 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24078 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24078 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24096 =
                                               let uu____24097 =
                                                 let uu____24104 =
                                                   let uu____24105 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24105 in
                                                 (uu____24104,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24097 in
                                             [uu____24096]
                                           else [] in
                                         let uu____24109 =
                                           let uu____24112 =
                                             let uu____24115 =
                                               let uu____24116 =
                                                 let uu____24123 =
                                                   let uu____24124 =
                                                     let uu____24135 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24135) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24124 in
                                                 (uu____24123,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24116 in
                                             [uu____24115] in
                                           FStar_List.append karr uu____24112 in
                                         FStar_List.append decls1 uu____24109 in
                                   let aux =
                                     let uu____24151 =
                                       let uu____24154 =
                                         inversion_axioms tapp vars in
                                       let uu____24157 =
                                         let uu____24160 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24160] in
                                       FStar_List.append uu____24154
                                         uu____24157 in
                                     FStar_List.append kindingAx uu____24151 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24167,uu____24168,uu____24169,uu____24170,uu____24171)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24179,t,uu____24181,n_tps,uu____24183) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24191 = new_term_constant_and_tok_from_lid env d in
          (match uu____24191 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24208 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24208 with
                | (formals,t_res) ->
                    let uu____24243 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24243 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24257 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24257 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24327 =
                                            mk_term_projector_name d x in
                                          (uu____24327,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24329 =
                                  let uu____24348 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24348, true) in
                                FStar_All.pipe_right uu____24329
                                  FStar_SMTEncoding_Term.constructor_to_decl in
                              let app = mk_Apply ddtok_tm vars in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars) in
                              let uu____24387 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24387 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24399::uu____24400 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff] in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____24445 =
                                           let uu____24456 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24456) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24445
                                     | uu____24481 -> tok_typing in
                                   let uu____24490 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24490 with
                                    | (vars',guards',env'',decls_formals,uu____24515)
                                        ->
                                        let uu____24528 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1 in
                                        (match uu____24528 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24559 ->
                                                   let uu____24566 =
                                                     let uu____24567 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24567 in
                                                   [uu____24566] in
                                             let encode_elim uu____24577 =
                                               let uu____24578 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24578 with
                                               | (head1,args) ->
                                                   let uu____24621 =
                                                     let uu____24622 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24622.FStar_Syntax_Syntax.n in
                                                   (match uu____24621 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24632;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24633;_},uu____24634)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24640 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24640
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____24683
                                                                    ->
                                                                    let uu____24684
                                                                    =
                                                                    let uu____24685
                                                                    =
                                                                    let uu____24690
                                                                    =
                                                                    let uu____24691
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24691 in
                                                                    (uu____24690,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24685 in
                                                                    FStar_Exn.raise
                                                                    uu____24684 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24707
                                                                    =
                                                                    let uu____24708
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24708 in
                                                                    if
                                                                    uu____24707
                                                                    then
                                                                    let uu____24721
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24721]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24723
                                                               =
                                                               let uu____24736
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24786
                                                                     ->
                                                                    fun
                                                                    uu____24787
                                                                     ->
                                                                    match 
                                                                    (uu____24786,
                                                                    uu____24787)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24882
                                                                    =
                                                                    let uu____24889
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24889 in
                                                                    (match uu____24882
                                                                    with
                                                                    | 
                                                                    (uu____24902,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24910
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24910
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24912
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24912
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 uu____24736 in
                                                             (match uu____24723
                                                              with
                                                              | (uu____24927,arg_vars,elim_eqns_or_guards,uu____24930)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____24960
                                                                    =
                                                                    let uu____24967
                                                                    =
                                                                    let uu____24968
                                                                    =
                                                                    let uu____24979
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24990
                                                                    =
                                                                    let uu____24991
                                                                    =
                                                                    let uu____24996
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24996) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24991 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24979,
                                                                    uu____24990) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24968 in
                                                                    (uu____24967,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24960 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25019
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25019,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25021
                                                                    =
                                                                    let uu____25028
                                                                    =
                                                                    let uu____25029
                                                                    =
                                                                    let uu____25040
                                                                    =
                                                                    let uu____25045
                                                                    =
                                                                    let uu____25048
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25048] in
                                                                    [uu____25045] in
                                                                    let uu____25053
                                                                    =
                                                                    let uu____25054
                                                                    =
                                                                    let uu____25059
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25060
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25059,
                                                                    uu____25060) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25054 in
                                                                    (uu____25040,
                                                                    [x],
                                                                    uu____25053) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25029 in
                                                                    let uu____25079
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25028,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25079) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25021
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25086
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____25114
                                                                    =
                                                                    let uu____25115
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25115
                                                                    dapp1 in
                                                                    [uu____25114]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25086
                                                                    FStar_List.flatten in
                                                                    let uu____25122
                                                                    =
                                                                    let uu____25129
                                                                    =
                                                                    let uu____25130
                                                                    =
                                                                    let uu____25141
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25152
                                                                    =
                                                                    let uu____25153
                                                                    =
                                                                    let uu____25158
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25158) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25153 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25141,
                                                                    uu____25152) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25130 in
                                                                    (uu____25129,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25122) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25179 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25179
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____25222
                                                                    ->
                                                                    let uu____25223
                                                                    =
                                                                    let uu____25224
                                                                    =
                                                                    let uu____25229
                                                                    =
                                                                    let uu____25230
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25230 in
                                                                    (uu____25229,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25224 in
                                                                    FStar_Exn.raise
                                                                    uu____25223 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25246
                                                                    =
                                                                    let uu____25247
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25247 in
                                                                    if
                                                                    uu____25246
                                                                    then
                                                                    let uu____25260
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25260]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25262
                                                               =
                                                               let uu____25275
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25325
                                                                     ->
                                                                    fun
                                                                    uu____25326
                                                                     ->
                                                                    match 
                                                                    (uu____25325,
                                                                    uu____25326)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25421
                                                                    =
                                                                    let uu____25428
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25428 in
                                                                    (match uu____25421
                                                                    with
                                                                    | 
                                                                    (uu____25441,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25449
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25449
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25451
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25451
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 uu____25275 in
                                                             (match uu____25262
                                                              with
                                                              | (uu____25466,arg_vars,elim_eqns_or_guards,uu____25469)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____25499
                                                                    =
                                                                    let uu____25506
                                                                    =
                                                                    let uu____25507
                                                                    =
                                                                    let uu____25518
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25529
                                                                    =
                                                                    let uu____25530
                                                                    =
                                                                    let uu____25535
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25535) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25530 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25518,
                                                                    uu____25529) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25507 in
                                                                    (uu____25506,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25499 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25558
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25558,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25560
                                                                    =
                                                                    let uu____25567
                                                                    =
                                                                    let uu____25568
                                                                    =
                                                                    let uu____25579
                                                                    =
                                                                    let uu____25584
                                                                    =
                                                                    let uu____25587
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25587] in
                                                                    [uu____25584] in
                                                                    let uu____25592
                                                                    =
                                                                    let uu____25593
                                                                    =
                                                                    let uu____25598
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25599
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25598,
                                                                    uu____25599) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25593 in
                                                                    (uu____25579,
                                                                    [x],
                                                                    uu____25592) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25568 in
                                                                    let uu____25618
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25567,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25618) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25560
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25625
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____25653
                                                                    =
                                                                    let uu____25654
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25654
                                                                    dapp1 in
                                                                    [uu____25653]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25625
                                                                    FStar_List.flatten in
                                                                    let uu____25661
                                                                    =
                                                                    let uu____25668
                                                                    =
                                                                    let uu____25669
                                                                    =
                                                                    let uu____25680
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25691
                                                                    =
                                                                    let uu____25692
                                                                    =
                                                                    let uu____25697
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25697) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25692 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25680,
                                                                    uu____25691) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25669 in
                                                                    (uu____25668,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25661) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25716 ->
                                                        ((let uu____25718 =
                                                            let uu____25719 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25720 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25719
                                                              uu____25720 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25718);
                                                         ([], []))) in
                                             let uu____25725 = encode_elim () in
                                             (match uu____25725 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25745 =
                                                      let uu____25748 =
                                                        let uu____25751 =
                                                          let uu____25754 =
                                                            let uu____25757 =
                                                              let uu____25758
                                                                =
                                                                let uu____25769
                                                                  =
                                                                  let uu____25772
                                                                    =
                                                                    let uu____25773
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25773 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25772 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25769) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25758 in
                                                            [uu____25757] in
                                                          let uu____25778 =
                                                            let uu____25781 =
                                                              let uu____25784
                                                                =
                                                                let uu____25787
                                                                  =
                                                                  let uu____25790
                                                                    =
                                                                    let uu____25793
                                                                    =
                                                                    let uu____25796
                                                                    =
                                                                    let uu____25797
                                                                    =
                                                                    let uu____25804
                                                                    =
                                                                    let uu____25805
                                                                    =
                                                                    let uu____25816
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25816) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25805 in
                                                                    (uu____25804,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25797 in
                                                                    let uu____25829
                                                                    =
                                                                    let uu____25832
                                                                    =
                                                                    let uu____25833
                                                                    =
                                                                    let uu____25840
                                                                    =
                                                                    let uu____25841
                                                                    =
                                                                    let uu____25852
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25863
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25852,
                                                                    uu____25863) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25841 in
                                                                    (uu____25840,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25833 in
                                                                    [uu____25832] in
                                                                    uu____25796
                                                                    ::
                                                                    uu____25829 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25793 in
                                                                  FStar_List.append
                                                                    uu____25790
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25787 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25784 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25781 in
                                                          FStar_List.append
                                                            uu____25754
                                                            uu____25778 in
                                                        FStar_List.append
                                                          decls3 uu____25751 in
                                                      FStar_List.append
                                                        decls2 uu____25748 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25745 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____25909  ->
              fun se  ->
                match uu____25909 with
                | (g,env1) ->
                    let uu____25929 = encode_sigelt env1 se in
                    (match uu____25929 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25988 =
        match uu____25988 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26020 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____26026 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26026
                   then
                     let uu____26027 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26028 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26029 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26027 uu____26028 uu____26029
                   else ());
                  (let uu____26031 = encode_term t1 env1 in
                   match uu____26031 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26047 =
                         let uu____26054 =
                           let uu____26055 =
                             let uu____26056 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26056
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26055 in
                         new_term_constant_from_string env1 x uu____26054 in
                       (match uu____26047 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26072 = FStar_Options.log_queries () in
                              if uu____26072
                              then
                                let uu____26075 =
                                  let uu____26076 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26077 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26078 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26076 uu____26077 uu____26078 in
                                FStar_Pervasives_Native.Some uu____26075
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26094,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26108 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26108 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26131,se,uu____26133) ->
                 let uu____26138 = encode_sigelt env1 se in
                 (match uu____26138 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26155,se) ->
                 let uu____26161 = encode_sigelt env1 se in
                 (match uu____26161 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26178 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26178 with | (uu____26201,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26216 'Auu____26217 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26217,'Auu____26216)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26285  ->
              match uu____26285 with
              | (l,uu____26297,uu____26298) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26344  ->
              match uu____26344 with
              | (l,uu____26358,uu____26359) ->
                  let uu____26368 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26369 =
                    let uu____26372 =
                      let uu____26373 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26373 in
                    [uu____26372] in
                  uu____26368 :: uu____26369)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26395 =
      let uu____26398 =
        let uu____26399 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26402 =
          let uu____26403 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26403 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26399;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26402
        } in
      [uu____26398] in
    FStar_ST.op_Colon_Equals last_env uu____26395
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26462 = FStar_ST.op_Bang last_env in
      match uu____26462 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26516 ->
          let uu___176_26519 = e in
          let uu____26520 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___176_26519.bindings);
            depth = (uu___176_26519.depth);
            tcenv;
            warn = (uu___176_26519.warn);
            cache = (uu___176_26519.cache);
            nolabels = (uu___176_26519.nolabels);
            use_zfuel_name = (uu___176_26519.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___176_26519.encode_non_total_function_typ);
            current_module_name = uu____26520
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26525 = FStar_ST.op_Bang last_env in
    match uu____26525 with
    | [] -> failwith "Empty env stack"
    | uu____26578::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26635  ->
    let uu____26636 = FStar_ST.op_Bang last_env in
    match uu____26636 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___177_26697 = hd1 in
          {
            bindings = (uu___177_26697.bindings);
            depth = (uu___177_26697.depth);
            tcenv = (uu___177_26697.tcenv);
            warn = (uu___177_26697.warn);
            cache = refs;
            nolabels = (uu___177_26697.nolabels);
            use_zfuel_name = (uu___177_26697.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___177_26697.encode_non_total_function_typ);
            current_module_name = (uu___177_26697.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26751  ->
    let uu____26752 = FStar_ST.op_Bang last_env in
    match uu____26752 with
    | [] -> failwith "Popping an empty stack"
    | uu____26805::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let open_fact_db_tags: env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> []
let place_decl_in_fact_dbs:
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____26903::uu____26904,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___178_26912 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___178_26912.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___178_26912.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___178_26912.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26913 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26930 =
        let uu____26933 =
          let uu____26934 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26934 in
        let uu____26935 = open_fact_db_tags env in uu____26933 :: uu____26935 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26930
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____26959 = encode_sigelt env se in
      match uu____26959 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____26997 = FStar_Options.log_queries () in
        if uu____26997
        then
          let uu____27000 =
            let uu____27001 =
              let uu____27002 =
                let uu____27003 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____27003 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____27002 in
            FStar_SMTEncoding_Term.Caption uu____27001 in
          uu____27000 :: decls
        else decls in
      (let uu____27014 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27014
       then
         let uu____27015 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27015
       else ());
      (let env =
         let uu____27018 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____27018 tcenv in
       let uu____27019 = encode_top_level_facts env se in
       match uu____27019 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27033 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____27033)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____27047 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27047
       then
         let uu____27048 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27048
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27083  ->
                 fun se  ->
                   match uu____27083 with
                   | (g,env2) ->
                       let uu____27103 = encode_top_level_facts env2 se in
                       (match uu____27103 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27126 =
         encode_signature
           (let uu___179_27135 = env in
            {
              bindings = (uu___179_27135.bindings);
              depth = (uu___179_27135.depth);
              tcenv = (uu___179_27135.tcenv);
              warn = false;
              cache = (uu___179_27135.cache);
              nolabels = (uu___179_27135.nolabels);
              use_zfuel_name = (uu___179_27135.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___179_27135.encode_non_total_function_typ);
              current_module_name = (uu___179_27135.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27126 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27152 = FStar_Options.log_queries () in
             if uu____27152
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___180_27160 = env1 in
               {
                 bindings = (uu___180_27160.bindings);
                 depth = (uu___180_27160.depth);
                 tcenv = (uu___180_27160.tcenv);
                 warn = true;
                 cache = (uu___180_27160.cache);
                 nolabels = (uu___180_27160.nolabels);
                 use_zfuel_name = (uu___180_27160.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___180_27160.encode_non_total_function_typ);
                 current_module_name = (uu___180_27160.current_module_name)
               });
            (let uu____27162 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27162
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____27217 =
           let uu____27218 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27218.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27217);
        (let env =
           let uu____27220 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27220 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27232 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27267 = aux rest in
                 (match uu____27267 with
                  | (out,rest1) ->
                      let t =
                        let uu____27297 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27297 with
                        | FStar_Pervasives_Native.Some uu____27302 ->
                            let uu____27303 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27303
                              x.FStar_Syntax_Syntax.sort
                        | uu____27304 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27308 =
                        let uu____27311 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___181_27314 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___181_27314.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___181_27314.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27311 :: out in
                      (uu____27308, rest1))
             | uu____27319 -> ([], bindings1) in
           let uu____27326 = aux bindings in
           match uu____27326 with
           | (closing,bindings1) ->
               let uu____27351 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27351, bindings1) in
         match uu____27232 with
         | (q1,bindings1) ->
             let uu____27374 =
               let uu____27379 =
                 FStar_List.filter
                   (fun uu___146_27384  ->
                      match uu___146_27384 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27385 ->
                          false
                      | uu____27392 -> true) bindings1 in
               encode_env_bindings env uu____27379 in
             (match uu____27374 with
              | (env_decls,env1) ->
                  ((let uu____27410 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27410
                    then
                      let uu____27411 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27411
                    else ());
                   (let uu____27413 = encode_formula q1 env1 in
                    match uu____27413 with
                    | (phi,qdecls) ->
                        let uu____27434 =
                          let uu____27439 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27439 phi in
                        (match uu____27434 with
                         | (labels,phi1) ->
                             let uu____27456 = encode_labels labels in
                             (match uu____27456 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27493 =
                                      let uu____27500 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27501 =
                                        varops.mk_unique "@query" in
                                      (uu____27500,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27501) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27493 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))