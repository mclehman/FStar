open Prims
let int1 m f ua em r args =
  match args with
  | (a,uu____60)::[] ->
      let uu____73 =
        let uu____74 = let uu____75 = ua a  in f uu____75  in em uu____74  in
      Some uu____73
  | uu____76 -> None 
let int2 m f ua ub em r args =
  match args with
  | (a,uu____155)::(b,uu____157)::[] ->
      let uu____178 =
        let uu____179 =
          let uu____180 = ua a  in
          let uu____181 = ub b  in f uu____180 uu____181  in
        em uu____179  in
      Some uu____178
  | uu____182 -> None 
let reflection_primops :
  FStar_TypeChecker_Normalize.primitive_step Prims.list =
  let mklid nm = FStar_Reflection_Data.fstar_refl_syntax_lid nm  in
  let mk1 l arity fn =
    {
      FStar_TypeChecker_Normalize.name = l;
      FStar_TypeChecker_Normalize.arity = arity;
      FStar_TypeChecker_Normalize.strong_reduction_ok = false;
      FStar_TypeChecker_Normalize.interpretation = fn
    }  in
  let mk11 nm f u1 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "1") (int1 l f u1 em)  in
  let mk2 nm f u1 u2 em =
    let l = mklid nm  in mk1 l (Prims.parse_int "2") (int2 l f u1 u2 em)  in
  let uu____309 =
    mk11 "__inspect" FStar_Reflection_Basic.inspect
      FStar_Reflection_Basic.unembed_term
      FStar_Reflection_Basic.embed_term_view
     in
  let uu____310 =
    let uu____312 =
      mk11 "__pack" FStar_Reflection_Basic.pack
        FStar_Reflection_Basic.unembed_term_view
        FStar_Reflection_Basic.embed_term
       in
    let uu____313 =
      let uu____315 =
        mk11 "__inspect_fv" FStar_Reflection_Basic.inspect_fv
          FStar_Reflection_Basic.unembed_fvar
          (FStar_Reflection_Basic.embed_list
             FStar_Reflection_Basic.embed_string
             FStar_TypeChecker_Common.t_string)
         in
      let uu____317 =
        let uu____319 =
          mk11 "__pack_fv" FStar_Reflection_Basic.pack_fv
            (FStar_Reflection_Basic.unembed_list
               FStar_Reflection_Basic.unembed_string)
            FStar_Reflection_Basic.embed_fvar
           in
        let uu____321 =
          let uu____323 =
            mk11 "__inspect_bv" FStar_Reflection_Basic.inspect_bv
              FStar_Reflection_Basic.unembed_binder
              FStar_Reflection_Basic.embed_string
             in
          let uu____324 =
            let uu____326 =
              mk2 "__compare_binder" FStar_Reflection_Basic.order_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.unembed_binder
                FStar_Reflection_Basic.embed_order
               in
            let uu____327 =
              let uu____329 =
                mk11 "__type_of_binder"
                  (fun uu____334  ->
                     match uu____334 with
                     | (b,q) -> b.FStar_Syntax_Syntax.sort)
                  FStar_Reflection_Basic.unembed_binder
                  FStar_Reflection_Basic.embed_term
                 in
              let uu____341 =
                let uu____343 =
                  mk2 "__is_free" FStar_Reflection_Basic.is_free
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_bool
                   in
                let uu____344 =
                  let uu____346 =
                    mk11 "__fresh_binder"
                      (fun t  ->
                         let uu____351 =
                           FStar_Syntax_Syntax.gen_bv "__refl" None t  in
                         (uu____351, None))
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_binder
                     in
                  let uu____353 =
                    let uu____355 =
                      mk2 "__term_eq" FStar_Syntax_Util.term_eq
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.embed_bool
                       in
                    let uu____360 =
                      let uu____362 =
                        mk11 "__term_to_string"
                          FStar_Syntax_Print.term_to_string
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_string
                         in
                      [uu____362]  in
                    uu____355 :: uu____360  in
                  uu____346 :: uu____353  in
                uu____343 :: uu____344  in
              uu____329 :: uu____341  in
            uu____326 :: uu____327  in
          uu____323 :: uu____324  in
        uu____319 :: uu____321  in
      uu____315 :: uu____317  in
    uu____312 :: uu____313  in
  uu____309 :: uu____310 