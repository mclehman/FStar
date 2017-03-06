open Prims
let find_deps_if_needed:
  FStar_Parser_Dep.verify_mode ->
    Prims.string Prims.list -> Prims.string Prims.list
  =
  fun verify_mode  ->
    fun files  ->
      let uu____10 = FStar_Options.explicit_deps () in
      match uu____10 with
      | true  -> files
      | uu____12 ->
          let uu____13 = FStar_Parser_Dep.collect verify_mode files in
          (match uu____13 with
           | (uu____27,deps,uu____29) ->
               (match deps with
                | [] ->
                    (FStar_Util.print_error
                       "Dependency analysis failed; reverting to using only the files provided";
                     files)
                | uu____50 ->
                    let deps = FStar_List.rev deps in
                    let deps =
                      let uu____56 =
                        let uu____57 =
                          let uu____58 = FStar_List.hd deps in
                          FStar_Util.basename uu____58 in
                        uu____57 = "prims.fst" in
                      match uu____56 with
                      | true  -> FStar_List.tl deps
                      | uu____60 ->
                          (FStar_Util.print_error
                             "dependency analysis did not find prims.fst?!";
                           FStar_All.exit (Prims.parse_int "1")) in
                    deps))