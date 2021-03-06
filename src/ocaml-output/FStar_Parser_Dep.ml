open Prims
type verify_mode =
  | VerifyAll 
  | VerifyUserList 
  | VerifyFigureItOut 
let (uu___is_VerifyAll : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyAll  -> true | uu____6 -> false
  
let (uu___is_VerifyUserList : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyUserList  -> true | uu____12 -> false
  
let (uu___is_VerifyFigureItOut : verify_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | VerifyFigureItOut  -> true | uu____18 -> false
  
type files_for_module_name =
  (Prims.string FStar_Pervasives_Native.option,Prims.string
                                                 FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap
type color =
  | White 
  | Gray 
  | Black 
let (uu___is_White : color -> Prims.bool) =
  fun projectee  -> match projectee with | White  -> true | uu____34 -> false 
let (uu___is_Gray : color -> Prims.bool) =
  fun projectee  -> match projectee with | Gray  -> true | uu____40 -> false 
let (uu___is_Black : color -> Prims.bool) =
  fun projectee  -> match projectee with | Black  -> true | uu____46 -> false 
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____52 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____58 -> false
  
let (check_and_strip_suffix :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun f  ->
    let suffixes = [".fsti"; ".fst"; ".fsi"; ".fs"]  in
    let matches =
      FStar_List.map
        (fun ext  ->
           let lext = FStar_String.length ext  in
           let l = FStar_String.length f  in
           let uu____86 =
             (l > lext) &&
               (let uu____98 = FStar_String.substring f (l - lext) lext  in
                uu____98 = ext)
              in
           if uu____86
           then
             let uu____115 =
               FStar_String.substring f (Prims.parse_int "0") (l - lext)  in
             FStar_Pervasives_Native.Some uu____115
           else FStar_Pervasives_Native.None) suffixes
       in
    let uu____127 = FStar_List.filter FStar_Util.is_some matches  in
    match uu____127 with
    | (FStar_Pervasives_Native.Some m)::uu____137 ->
        FStar_Pervasives_Native.Some m
    | uu____144 -> FStar_Pervasives_Native.None
  
let (is_interface : Prims.string -> Prims.bool) =
  fun f  ->
    let uu____154 =
      FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))
       in
    uu____154 = 105
  
let (is_implementation : Prims.string -> Prims.bool) =
  fun f  -> let uu____163 = is_interface f  in Prims.op_Negation uu____163 
let list_of_option :
  'Auu____168 .
    'Auu____168 FStar_Pervasives_Native.option -> 'Auu____168 Prims.list
  =
  fun uu___105_177  ->
    match uu___105_177 with
    | FStar_Pervasives_Native.Some x -> [x]
    | FStar_Pervasives_Native.None  -> []
  
let list_of_pair :
  'Auu____185 .
    ('Auu____185 FStar_Pervasives_Native.option,'Auu____185
                                                  FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> 'Auu____185 Prims.list
  =
  fun uu____200  ->
    match uu____200 with
    | (intf,impl) ->
        FStar_List.append (list_of_option intf) (list_of_option impl)
  
let (module_name_of_file : Prims.string -> Prims.string) =
  fun f  ->
    let uu____224 =
      let uu____227 = FStar_Util.basename f  in
      check_and_strip_suffix uu____227  in
    match uu____224 with
    | FStar_Pervasives_Native.Some longname -> longname
    | FStar_Pervasives_Native.None  ->
        let uu____229 =
          let uu____234 = FStar_Util.format1 "not a valid FStar file: %s\n" f
             in
          (FStar_Errors.Fatal_NotValidFStarFile, uu____234)  in
        FStar_Errors.raise_err uu____229
  
let (lowercase_module_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____240 = module_name_of_file f  in
    FStar_String.lowercase uu____240
  
let (namespace_of_module :
  Prims.string -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun f  ->
    let lid =
      let uu____249 = FStar_Ident.path_of_text f  in
      FStar_Ident.lid_of_path uu____249 FStar_Range.dummyRange  in
    match lid.FStar_Ident.ns with
    | [] -> FStar_Pervasives_Native.None
    | uu____252 ->
        let uu____255 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
        FStar_Pervasives_Native.Some uu____255
  
type file_name = Prims.string
type module_name = Prims.string
type dependence =
  | UseInterface of module_name 
  | PreferInterface of module_name 
  | UseImplementation of module_name 
let (uu___is_UseInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseInterface _0 -> true | uu____277 -> false
  
let (__proj__UseInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseInterface _0 -> _0 
let (uu___is_PreferInterface : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | PreferInterface _0 -> true | uu____291 -> false
  
let (__proj__PreferInterface__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | PreferInterface _0 -> _0 
let (uu___is_UseImplementation : dependence -> Prims.bool) =
  fun projectee  ->
    match projectee with | UseImplementation _0 -> true | uu____305 -> false
  
let (__proj__UseImplementation__item___0 : dependence -> module_name) =
  fun projectee  -> match projectee with | UseImplementation _0 -> _0 
type dependences = dependence Prims.list
let empty_dependences : 'Auu____317 . unit -> 'Auu____317 Prims.list =
  fun uu____320  -> [] 
type dependence_graph =
  | Deps of (dependences,color) FStar_Pervasives_Native.tuple2
  FStar_Util.smap 
let (uu___is_Deps : dependence_graph -> Prims.bool) = fun projectee  -> true 
let (__proj__Deps__item___0 :
  dependence_graph ->
    (dependences,color) FStar_Pervasives_Native.tuple2 FStar_Util.smap)
  = fun projectee  -> match projectee with | Deps _0 -> _0 
type deps =
  | Mk of (dependence_graph,files_for_module_name,file_name Prims.list)
  FStar_Pervasives_Native.tuple3 
let (uu___is_Mk : deps -> Prims.bool) = fun projectee  -> true 
let (__proj__Mk__item___0 :
  deps ->
    (dependence_graph,files_for_module_name,file_name Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Mk _0 -> _0 
let (deps_try_find :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun uu____423  ->
    fun k  -> match uu____423 with | Deps m -> FStar_Util.smap_try_find m k
  
let (deps_add_dep :
  dependence_graph ->
    Prims.string ->
      (dependences,color) FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun uu____458  ->
    fun k  ->
      fun v1  -> match uu____458 with | Deps m -> FStar_Util.smap_add m k v1
  
let (deps_keys : dependence_graph -> Prims.string Prims.list) =
  fun uu____482  -> match uu____482 with | Deps m -> FStar_Util.smap_keys m 
let (deps_empty : unit -> dependence_graph) =
  fun uu____500  ->
    let uu____501 = FStar_Util.smap_create (Prims.parse_int "41")  in
    Deps uu____501
  
let (empty_deps : deps) =
  let uu____512 =
    let uu____521 = deps_empty ()  in
    let uu____522 = FStar_Util.smap_create (Prims.parse_int "0")  in
    (uu____521, uu____522, [])  in
  Mk uu____512 
let (module_name_of_dep : dependence -> module_name) =
  fun uu___106_537  ->
    match uu___106_537 with
    | UseInterface m -> m
    | PreferInterface m -> m
    | UseImplementation m -> m
  
let (resolve_module_name :
  files_for_module_name ->
    module_name -> module_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____555 = FStar_Util.smap_try_find file_system_map key  in
      match uu____555 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some fn,uu____577) ->
          let uu____592 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____592
      | FStar_Pervasives_Native.Some
          (uu____593,FStar_Pervasives_Native.Some fn) ->
          let uu____609 = lowercase_module_name fn  in
          FStar_Pervasives_Native.Some uu____609
      | uu____610 -> FStar_Pervasives_Native.None
  
let (interface_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____635 = FStar_Util.smap_try_find file_system_map key  in
      match uu____635 with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some iface,uu____657) ->
          FStar_Pervasives_Native.Some iface
      | uu____672 -> FStar_Pervasives_Native.None
  
let (implementation_of :
  files_for_module_name ->
    module_name -> file_name FStar_Pervasives_Native.option)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____697 = FStar_Util.smap_try_find file_system_map key  in
      match uu____697 with
      | FStar_Pervasives_Native.Some
          (uu____718,FStar_Pervasives_Native.Some impl) ->
          FStar_Pervasives_Native.Some impl
      | uu____734 -> FStar_Pervasives_Native.None
  
let (has_interface : files_for_module_name -> module_name -> Prims.bool) =
  fun file_system_map  ->
    fun key  ->
      let uu____755 = interface_of file_system_map key  in
      FStar_Option.isSome uu____755
  
let (has_implementation : files_for_module_name -> module_name -> Prims.bool)
  =
  fun file_system_map  ->
    fun key  ->
      let uu____768 = implementation_of file_system_map key  in
      FStar_Option.isSome uu____768
  
let (cache_file_name : Prims.string -> Prims.string) =
  fun fn  ->
    let uu____776 =
      let uu____777 = FStar_Options.lax ()  in
      if uu____777
      then Prims.strcat fn ".checked.lax"
      else Prims.strcat fn ".checked"  in
    FStar_Options.prepend_cache_dir uu____776
  
let (file_of_dep_aux :
  Prims.bool ->
    files_for_module_name -> file_name Prims.list -> dependence -> file_name)
  =
  fun use_checked_file  ->
    fun file_system_map  ->
      fun all_cmd_line_files  ->
        fun d  ->
          let cmd_line_has_impl key =
            FStar_All.pipe_right all_cmd_line_files
              (FStar_Util.for_some
                 (fun fn  ->
                    (is_implementation fn) &&
                      (let uu____814 = lowercase_module_name fn  in
                       key = uu____814)))
             in
          let maybe_add_suffix f =
            if use_checked_file then cache_file_name f else f  in
          match d with
          | UseInterface key ->
              let uu____823 = interface_of file_system_map key  in
              (match uu____823 with
               | FStar_Pervasives_Native.None  ->
                   let uu____827 =
                     let uu____832 =
                       FStar_Util.format1
                         "Expected an interface for module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingInterface, uu____832)  in
                   FStar_Errors.raise_err uu____827
               | FStar_Pervasives_Native.Some f ->
                   if use_checked_file
                   then
                     FStar_Options.prepend_cache_dir
                       (Prims.strcat f ".source")
                   else f)
          | PreferInterface key when has_interface file_system_map key ->
              let uu____836 =
                (cmd_line_has_impl key) &&
                  (let uu____838 = FStar_Options.dep ()  in
                   FStar_Option.isNone uu____838)
                 in
              if uu____836
              then
                let uu____841 = FStar_Options.expose_interfaces ()  in
                (if uu____841
                 then
                   let uu____842 =
                     let uu____843 = implementation_of file_system_map key
                        in
                     FStar_Option.get uu____843  in
                   maybe_add_suffix uu____842
                 else
                   (let uu____847 =
                      let uu____852 =
                        let uu____853 =
                          let uu____854 =
                            implementation_of file_system_map key  in
                          FStar_Option.get uu____854  in
                        let uu____857 =
                          let uu____858 = interface_of file_system_map key
                             in
                          FStar_Option.get uu____858  in
                        FStar_Util.format3
                          "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option '--expose_interfaces'"
                          key uu____853 uu____857
                         in
                      (FStar_Errors.Fatal_MissingExposeInterfacesOption,
                        uu____852)
                       in
                    FStar_Errors.raise_err uu____847))
              else
                (let uu____862 =
                   let uu____863 = interface_of file_system_map key  in
                   FStar_Option.get uu____863  in
                 maybe_add_suffix uu____862)
          | PreferInterface key ->
              let uu____867 = implementation_of file_system_map key  in
              (match uu____867 with
               | FStar_Pervasives_Native.None  ->
                   let uu____871 =
                     let uu____876 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____876)
                      in
                   FStar_Errors.raise_err uu____871
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
          | UseImplementation key ->
              let uu____879 = implementation_of file_system_map key  in
              (match uu____879 with
               | FStar_Pervasives_Native.None  ->
                   let uu____883 =
                     let uu____888 =
                       FStar_Util.format1
                         "Expected an implementation of module %s, but couldn't find one"
                         key
                        in
                     (FStar_Errors.Fatal_MissingImplementation, uu____888)
                      in
                   FStar_Errors.raise_err uu____883
               | FStar_Pervasives_Native.Some f -> maybe_add_suffix f)
  
let (file_of_dep :
  files_for_module_name -> file_name Prims.list -> dependence -> file_name) =
  file_of_dep_aux false 
let (dependences_of :
  files_for_module_name ->
    dependence_graph ->
      file_name Prims.list -> file_name -> file_name Prims.list)
  =
  fun file_system_map  ->
    fun deps  ->
      fun all_cmd_line_files  ->
        fun fn  ->
          let uu____932 = deps_try_find deps fn  in
          match uu____932 with
          | FStar_Pervasives_Native.None  -> empty_dependences ()
          | FStar_Pervasives_Native.Some (deps1,uu____946) ->
              FStar_List.map (file_of_dep file_system_map all_cmd_line_files)
                deps1
  
let (add_dependence : dependence_graph -> file_name -> file_name -> unit) =
  fun deps  ->
    fun from  ->
      fun to_  ->
        let add_dep uu____987 to_1 =
          match uu____987 with
          | (d,color) ->
              let uu____1007 = is_interface to_1  in
              if uu____1007
              then
                let uu____1014 =
                  let uu____1017 =
                    let uu____1018 = lowercase_module_name to_1  in
                    PreferInterface uu____1018  in
                  uu____1017 :: d  in
                (uu____1014, color)
              else
                (let uu____1022 =
                   let uu____1025 =
                     let uu____1026 = lowercase_module_name to_1  in
                     UseImplementation uu____1026  in
                   uu____1025 :: d  in
                 (uu____1022, color))
           in
        let uu____1029 = deps_try_find deps from  in
        match uu____1029 with
        | FStar_Pervasives_Native.None  ->
            let uu____1040 = add_dep ((empty_dependences ()), White) to_  in
            deps_add_dep deps from uu____1040
        | FStar_Pervasives_Native.Some key_deps ->
            let uu____1056 = add_dep key_deps to_  in
            deps_add_dep deps from uu____1056
  
let (print_graph : dependence_graph -> unit) =
  fun graph  ->
    FStar_Util.print_endline
      "A DOT-format graph has been dumped in the current directory as dep.graph";
    FStar_Util.print_endline
      "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
    FStar_Util.print_endline
      "Hint: cat dep.graph | grep -v _ | grep -v prims";
    (let uu____1069 =
       let uu____1070 =
         let uu____1071 =
           let uu____1072 =
             let uu____1075 =
               let uu____1078 = deps_keys graph  in
               FStar_List.unique uu____1078  in
             FStar_List.collect
               (fun k  ->
                  let deps =
                    let uu____1087 =
                      let uu____1092 = deps_try_find graph k  in
                      FStar_Util.must uu____1092  in
                    FStar_Pervasives_Native.fst uu____1087  in
                  let r s = FStar_Util.replace_char s 46 95  in
                  let print7 dep1 =
                    FStar_Util.format2 "  \"%s\" -> \"%s\"" (r k)
                      (r (module_name_of_dep dep1))
                     in
                  FStar_List.map print7 deps) uu____1075
              in
           FStar_String.concat "\n" uu____1072  in
         Prims.strcat uu____1071 "\n}\n"  in
       Prims.strcat "digraph {\n" uu____1070  in
     FStar_Util.write_file "dep.graph" uu____1069)
  
let (build_inclusion_candidates_list :
  unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____1127  ->
    let include_directories = FStar_Options.include_path ()  in
    let include_directories1 =
      FStar_List.map FStar_Util.normalize_file_path include_directories  in
    let include_directories2 = FStar_List.unique include_directories1  in
    let cwd =
      let uu____1144 = FStar_Util.getcwd ()  in
      FStar_Util.normalize_file_path uu____1144  in
    FStar_List.concatMap
      (fun d  ->
         if FStar_Util.file_exists d
         then
           let files = FStar_Util.readdir d  in
           FStar_List.filter_map
             (fun f  ->
                let f1 = FStar_Util.basename f  in
                let uu____1170 = check_and_strip_suffix f1  in
                FStar_All.pipe_right uu____1170
                  (FStar_Util.map_option
                     (fun longname  ->
                        let full_path =
                          if d = cwd then f1 else FStar_Util.join_paths d f1
                           in
                        (longname, full_path)))) files
         else
           (let uu____1191 =
              let uu____1196 =
                FStar_Util.format1 "not a valid include directory: %s\n" d
                 in
              (FStar_Errors.Fatal_NotValidIncludeDirectory, uu____1196)  in
            FStar_Errors.raise_err uu____1191)) include_directories2
  
let (build_map : Prims.string Prims.list -> files_for_module_name) =
  fun filenames  ->
    let map1 = FStar_Util.smap_create (Prims.parse_int "41")  in
    let add_entry key full_path =
      let uu____1242 = FStar_Util.smap_try_find map1 key  in
      match uu____1242 with
      | FStar_Pervasives_Native.Some (intf,impl) ->
          let uu____1279 = is_interface full_path  in
          if uu____1279
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path), impl)
          else
            FStar_Util.smap_add map1 key
              (intf, (FStar_Pervasives_Native.Some full_path))
      | FStar_Pervasives_Native.None  ->
          let uu____1313 = is_interface full_path  in
          if uu____1313
          then
            FStar_Util.smap_add map1 key
              ((FStar_Pervasives_Native.Some full_path),
                FStar_Pervasives_Native.None)
          else
            FStar_Util.smap_add map1 key
              (FStar_Pervasives_Native.None,
                (FStar_Pervasives_Native.Some full_path))
       in
    (let uu____1340 = build_inclusion_candidates_list ()  in
     FStar_List.iter
       (fun uu____1354  ->
          match uu____1354 with
          | (longname,full_path) ->
              add_entry (FStar_String.lowercase longname) full_path)
       uu____1340);
    FStar_List.iter
      (fun f  ->
         let uu____1365 = lowercase_module_name f  in add_entry uu____1365 f)
      filenames;
    map1
  
let (enter_namespace :
  files_for_module_name ->
    files_for_module_name -> Prims.string -> Prims.bool)
  =
  fun original_map  ->
    fun working_map  ->
      fun prefix1  ->
        let found = FStar_Util.mk_ref false  in
        let prefix2 = Prims.strcat prefix1 "."  in
        (let uu____1386 =
           let uu____1389 = FStar_Util.smap_keys original_map  in
           FStar_List.unique uu____1389  in
         FStar_List.iter
           (fun k  ->
              if FStar_Util.starts_with k prefix2
              then
                let suffix =
                  FStar_String.substring k (FStar_String.length prefix2)
                    ((FStar_String.length k) - (FStar_String.length prefix2))
                   in
                let filename =
                  let uu____1415 = FStar_Util.smap_try_find original_map k
                     in
                  FStar_Util.must uu____1415  in
                (FStar_Util.smap_add working_map suffix filename;
                 FStar_ST.op_Colon_Equals found true)
              else ()) uu____1386);
        FStar_ST.op_Bang found
  
let (string_of_lid : FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let suffix =
        if last1 then [(l.FStar_Ident.ident).FStar_Ident.idText] else []  in
      let names =
        let uu____1561 =
          FStar_List.map (fun x  -> x.FStar_Ident.idText) l.FStar_Ident.ns
           in
        FStar_List.append uu____1561 suffix  in
      FStar_String.concat "." names
  
let (lowercase_join_longident :
  FStar_Ident.lident -> Prims.bool -> Prims.string) =
  fun l  ->
    fun last1  ->
      let uu____1576 = string_of_lid l last1  in
      FStar_String.lowercase uu____1576
  
let (namespace_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____1582 = FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns
       in
    FStar_String.concat "_" uu____1582
  
let (check_module_declaration_against_filename :
  FStar_Ident.lident -> Prims.string -> unit) =
  fun lid  ->
    fun filename  ->
      let k' = lowercase_join_longident lid true  in
      let uu____1596 =
        let uu____1597 =
          let uu____1598 =
            let uu____1599 =
              let uu____1602 = FStar_Util.basename filename  in
              check_and_strip_suffix uu____1602  in
            FStar_Util.must uu____1599  in
          FStar_String.lowercase uu____1598  in
        uu____1597 <> k'  in
      if uu____1596
      then
        let uu____1603 = FStar_Ident.range_of_lid lid  in
        let uu____1604 =
          let uu____1609 =
            let uu____1610 = string_of_lid lid true  in
            FStar_Util.format2
              "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n"
              uu____1610 filename
             in
          (FStar_Errors.Error_ModuleFileNameMismatch, uu____1609)  in
        FStar_Errors.log_issue uu____1603 uu____1604
      else ()
  
exception Exit 
let (uu___is_Exit : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1617 -> false
  
let (hard_coded_dependencies :
  Prims.string ->
    (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun full_filename  ->
    let filename = FStar_Util.basename full_filename  in
    let corelibs =
      let uu____1633 = FStar_Options.prims_basename ()  in
      let uu____1634 =
        let uu____1637 = FStar_Options.pervasives_basename ()  in
        let uu____1638 =
          let uu____1641 = FStar_Options.pervasives_native_basename ()  in
          [uu____1641]  in
        uu____1637 :: uu____1638  in
      uu____1633 :: uu____1634  in
    if FStar_List.mem filename corelibs
    then []
    else
      (let implicit_deps =
         [(FStar_Parser_Const.fstar_ns_lid, Open_namespace);
         (FStar_Parser_Const.prims_lid, Open_module);
         (FStar_Parser_Const.pervasives_lid, Open_module)]  in
       let uu____1676 =
         let uu____1679 = lowercase_module_name full_filename  in
         namespace_of_module uu____1679  in
       match uu____1676 with
       | FStar_Pervasives_Native.None  -> implicit_deps
       | FStar_Pervasives_Native.Some ns ->
           FStar_List.append implicit_deps [(ns, Open_namespace)])
  
let (collect_one :
  files_for_module_name ->
    Prims.string ->
      (dependence Prims.list,dependence Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun original_map  ->
    fun filename  ->
      let deps = FStar_Util.mk_ref []  in
      let mo_roots = FStar_Util.mk_ref []  in
      let add_dep deps1 d =
        let uu____1905 =
          let uu____1906 =
            let uu____1907 = FStar_ST.op_Bang deps1  in
            FStar_List.existsML (fun d'  -> d' = d) uu____1907  in
          Prims.op_Negation uu____1906  in
        if uu____1905
        then
          let uu____1981 =
            let uu____1984 = FStar_ST.op_Bang deps1  in d :: uu____1984  in
          FStar_ST.op_Colon_Equals deps1 uu____1981
        else ()  in
      let working_map = FStar_Util.smap_copy original_map  in
      let add_dependence_edge original_or_working_map lid =
        let key = lowercase_join_longident lid true  in
        let uu____2157 = resolve_module_name original_or_working_map key  in
        match uu____2157 with
        | FStar_Pervasives_Native.Some module_name ->
            (add_dep deps (PreferInterface module_name);
             (let uu____2196 =
                (has_interface original_or_working_map module_name) &&
                  (has_implementation original_or_working_map module_name)
                 in
              if uu____2196
              then add_dep mo_roots (UseImplementation module_name)
              else ());
             true)
        | uu____2231 -> false  in
      let record_open_module let_open lid =
        let uu____2245 =
          (let_open && (add_dependence_edge working_map lid)) ||
            ((Prims.op_Negation let_open) &&
               (add_dependence_edge original_map lid))
           in
        if uu____2245
        then true
        else
          (if let_open
           then
             (let uu____2248 = FStar_Ident.range_of_lid lid  in
              let uu____2249 =
                let uu____2254 =
                  let uu____2255 = string_of_lid lid true  in
                  FStar_Util.format1 "Module not found: %s" uu____2255  in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2254)
                 in
              FStar_Errors.log_issue uu____2248 uu____2249)
           else ();
           false)
         in
      let record_open_namespace lid =
        let key = lowercase_join_longident lid true  in
        let r = enter_namespace original_map working_map key  in
        if Prims.op_Negation r
        then
          let uu____2265 = FStar_Ident.range_of_lid lid  in
          let uu____2266 =
            let uu____2271 =
              let uu____2272 = string_of_lid lid true  in
              FStar_Util.format1
                "No modules in namespace %s and no file with that name either"
                uu____2272
               in
            (FStar_Errors.Warning_ModuleOrFileNotFoundWarning, uu____2271)
             in
          FStar_Errors.log_issue uu____2265 uu____2266
        else ()  in
      let record_open let_open lid =
        let uu____2285 = record_open_module let_open lid  in
        if uu____2285
        then ()
        else
          if Prims.op_Negation let_open
          then record_open_namespace lid
          else ()
         in
      let record_open_module_or_namespace uu____2297 =
        match uu____2297 with
        | (lid,kind) ->
            (match kind with
             | Open_namespace  -> record_open_namespace lid
             | Open_module  ->
                 let uu____2304 = record_open_module false lid  in ())
         in
      let record_module_alias ident lid =
        let key =
          let uu____2317 = FStar_Ident.text_of_id ident  in
          FStar_String.lowercase uu____2317  in
        let alias = lowercase_join_longident lid true  in
        let uu____2319 = FStar_Util.smap_try_find original_map alias  in
        match uu____2319 with
        | FStar_Pervasives_Native.Some deps_of_aliased_module ->
            (FStar_Util.smap_add working_map key deps_of_aliased_module; true)
        | FStar_Pervasives_Native.None  ->
            ((let uu____2373 = FStar_Ident.range_of_lid lid  in
              let uu____2374 =
                let uu____2379 =
                  FStar_Util.format1 "module not found in search path: %s\n"
                    alias
                   in
                (FStar_Errors.Warning_ModuleOrFileNotFoundWarning,
                  uu____2379)
                 in
              FStar_Errors.log_issue uu____2373 uu____2374);
             false)
         in
      let record_lid lid =
        match lid.FStar_Ident.ns with
        | [] -> ()
        | uu____2386 ->
            let module_name = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
            let uu____2390 = add_dependence_edge working_map module_name  in
            if uu____2390
            then ()
            else
              (let uu____2392 = FStar_Options.debug_any ()  in
               if uu____2392
               then
                 let uu____2393 = FStar_Ident.range_of_lid lid  in
                 let uu____2394 =
                   let uu____2399 =
                     let uu____2400 = FStar_Ident.string_of_lid module_name
                        in
                     FStar_Util.format1 "Unbound module reference %s"
                       uu____2400
                      in
                   (FStar_Errors.Warning_UnboundModuleReference, uu____2399)
                    in
                 FStar_Errors.log_issue uu____2393 uu____2394
               else ())
         in
      let auto_open = hard_coded_dependencies filename  in
      FStar_List.iter record_open_module_or_namespace auto_open;
      (let num_of_toplevelmods = FStar_Util.mk_ref (Prims.parse_int "0")  in
       let rec collect_module uu___107_2516 =
         match uu___107_2516 with
         | FStar_Parser_AST.Module (lid,decls) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2525 =
                   let uu____2526 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2526  in
                 ())
              else ();
              collect_decls decls)
         | FStar_Parser_AST.Interface (lid,decls,uu____2530) ->
             (check_module_declaration_against_filename lid filename;
              if
                (FStar_List.length lid.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                (let uu____2537 =
                   let uu____2538 = namespace_of_lid lid  in
                   enter_namespace original_map working_map uu____2538  in
                 ())
              else ();
              collect_decls decls)
       
       and collect_decls decls =
         FStar_List.iter
           (fun x  ->
              collect_decl x.FStar_Parser_AST.d;
              FStar_List.iter collect_term x.FStar_Parser_AST.attrs) decls
       
       and collect_decl uu___108_2547 =
         match uu___108_2547 with
         | FStar_Parser_AST.Include lid -> record_open false lid
         | FStar_Parser_AST.Open lid -> record_open false lid
         | FStar_Parser_AST.ModuleAbbrev (ident,lid) ->
             let uu____2552 = record_module_alias ident lid  in
             if uu____2552
             then
               let uu____2553 =
                 let uu____2554 = lowercase_join_longident lid true  in
                 PreferInterface uu____2554  in
               add_dep deps uu____2553
             else ()
         | FStar_Parser_AST.TopLevelLet (uu____2589,patterms) ->
             FStar_List.iter
               (fun uu____2611  ->
                  match uu____2611 with
                  | (pat,t) -> (collect_pattern pat; collect_term t))
               patterms
         | FStar_Parser_AST.Main t -> collect_term t
         | FStar_Parser_AST.Splice (uu____2620,t) -> collect_term t
         | FStar_Parser_AST.Assume (uu____2626,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2628;
               FStar_Parser_AST.mdest = uu____2629;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift t;_}
             -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2631;
               FStar_Parser_AST.mdest = uu____2632;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree t;_}
             -> collect_term t
         | FStar_Parser_AST.Val (uu____2634,t) -> collect_term t
         | FStar_Parser_AST.SubEffect
             { FStar_Parser_AST.msource = uu____2636;
               FStar_Parser_AST.mdest = uu____2637;
               FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift
                 (t0,t1);_}
             -> (collect_term t0; collect_term t1)
         | FStar_Parser_AST.Tycon (uu____2641,ts) ->
             let ts1 =
               FStar_List.map
                 (fun uu____2671  -> match uu____2671 with | (x,docnik) -> x)
                 ts
                in
             FStar_List.iter collect_tycon ts1
         | FStar_Parser_AST.Exception (uu____2684,t) ->
             FStar_Util.iter_opt t collect_term
         | FStar_Parser_AST.NewEffect ed -> collect_effect_decl ed
         | FStar_Parser_AST.Fsdoc uu____2691 -> ()
         | FStar_Parser_AST.Pragma uu____2692 -> ()
         | FStar_Parser_AST.TopLevelModule lid ->
             (FStar_Util.incr num_of_toplevelmods;
              (let uu____2728 =
                 let uu____2729 = FStar_ST.op_Bang num_of_toplevelmods  in
                 uu____2729 > (Prims.parse_int "1")  in
               if uu____2728
               then
                 let uu____2775 =
                   let uu____2780 =
                     let uu____2781 = string_of_lid lid true  in
                     FStar_Util.format1
                       "Automatic dependency analysis demands one module per file (module %s not supported)"
                       uu____2781
                      in
                   (FStar_Errors.Fatal_OneModulePerFile, uu____2780)  in
                 let uu____2782 = FStar_Ident.range_of_lid lid  in
                 FStar_Errors.raise_error uu____2775 uu____2782
               else ()))
       
       and collect_tycon uu___109_2784 =
         match uu___109_2784 with
         | FStar_Parser_AST.TyconAbstract (uu____2785,binders,k) ->
             (collect_binders binders; FStar_Util.iter_opt k collect_term)
         | FStar_Parser_AST.TyconAbbrev (uu____2797,binders,k,t) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              collect_term t)
         | FStar_Parser_AST.TyconRecord (uu____2811,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2857  ->
                   match uu____2857 with
                   | (uu____2866,t,uu____2868) -> collect_term t) identterms)
         | FStar_Parser_AST.TyconVariant (uu____2873,binders,k,identterms) ->
             (collect_binders binders;
              FStar_Util.iter_opt k collect_term;
              FStar_List.iter
                (fun uu____2932  ->
                   match uu____2932 with
                   | (uu____2945,t,uu____2947,uu____2948) ->
                       FStar_Util.iter_opt t collect_term) identterms)
       
       and collect_effect_decl uu___110_2957 =
         match uu___110_2957 with
         | FStar_Parser_AST.DefineEffect (uu____2958,binders,t,decls) ->
             (collect_binders binders; collect_term t; collect_decls decls)
         | FStar_Parser_AST.RedefineEffect (uu____2972,binders,t) ->
             (collect_binders binders; collect_term t)
       
       and collect_binders binders = FStar_List.iter collect_binder binders
       
       and collect_binder uu___111_2983 =
         match uu___111_2983 with
         | { FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2984,t);
             FStar_Parser_AST.brange = uu____2986;
             FStar_Parser_AST.blevel = uu____2987;
             FStar_Parser_AST.aqual = uu____2988;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2989,t);
             FStar_Parser_AST.brange = uu____2991;
             FStar_Parser_AST.blevel = uu____2992;
             FStar_Parser_AST.aqual = uu____2993;_} -> collect_term t
         | { FStar_Parser_AST.b = FStar_Parser_AST.NoName t;
             FStar_Parser_AST.brange = uu____2995;
             FStar_Parser_AST.blevel = uu____2996;
             FStar_Parser_AST.aqual = uu____2997;_} -> collect_term t
         | uu____2998 -> ()
       
       and collect_term t = collect_term' t.FStar_Parser_AST.tm
       
       and collect_constant uu___112_3000 =
         match uu___112_3000 with
         | FStar_Const.Const_int
             (uu____3001,FStar_Pervasives_Native.Some (signedness,width)) ->
             let u =
               match signedness with
               | FStar_Const.Unsigned  -> "u"
               | FStar_Const.Signed  -> ""  in
             let w =
               match width with
               | FStar_Const.Int8  -> "8"
               | FStar_Const.Int16  -> "16"
               | FStar_Const.Int32  -> "32"
               | FStar_Const.Int64  -> "64"  in
             let uu____3016 =
               let uu____3017 = FStar_Util.format2 "fstar.%sint%s" u w  in
               PreferInterface uu____3017  in
             add_dep deps uu____3016
         | FStar_Const.Const_char uu____3051 ->
             add_dep deps (PreferInterface "fstar.char")
         | FStar_Const.Const_float uu____3086 ->
             add_dep deps (PreferInterface "fstar.float")
         | uu____3120 -> ()
       
       and collect_term' uu___113_3121 =
         match uu___113_3121 with
         | FStar_Parser_AST.Wild  -> ()
         | FStar_Parser_AST.Const c -> collect_constant c
         | FStar_Parser_AST.Op (s,ts) ->
             ((let uu____3130 =
                 let uu____3131 = FStar_Ident.text_of_id s  in
                 uu____3131 = "@"  in
               if uu____3130
               then
                 let uu____3132 =
                   let uu____3133 =
                     let uu____3134 =
                       FStar_Ident.path_of_text "FStar.List.Tot.Base.append"
                        in
                     FStar_Ident.lid_of_path uu____3134
                       FStar_Range.dummyRange
                      in
                   FStar_Parser_AST.Name uu____3133  in
                 collect_term' uu____3132
               else ());
              FStar_List.iter collect_term ts)
         | FStar_Parser_AST.Tvar uu____3136 -> ()
         | FStar_Parser_AST.Uvar uu____3137 -> ()
         | FStar_Parser_AST.Var lid -> record_lid lid
         | FStar_Parser_AST.Projector (lid,uu____3140) -> record_lid lid
         | FStar_Parser_AST.Discrim lid -> record_lid lid
         | FStar_Parser_AST.Name lid -> record_lid lid
         | FStar_Parser_AST.Construct (lid,termimps) ->
             (if (FStar_List.length termimps) = (Prims.parse_int "1")
              then record_lid lid
              else ();
              FStar_List.iter
                (fun uu____3170  ->
                   match uu____3170 with | (t,uu____3176) -> collect_term t)
                termimps)
         | FStar_Parser_AST.Abs (pats,t) ->
             (collect_patterns pats; collect_term t)
         | FStar_Parser_AST.App (t1,t2,uu____3186) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Let (uu____3188,patterms,t) ->
             (FStar_List.iter
                (fun uu____3238  ->
                   match uu____3238 with
                   | (attrs_opt,(pat,t1)) ->
                       ((let uu____3267 =
                           FStar_Util.map_opt attrs_opt
                             (FStar_List.iter collect_term)
                            in
                         ());
                        collect_pattern pat;
                        collect_term t1)) patterms;
              collect_term t)
         | FStar_Parser_AST.LetOpen (lid,t) ->
             (record_open true lid; collect_term t)
         | FStar_Parser_AST.Bind (uu____3276,t1,t2) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Seq (t1,t2) -> (collect_term t1; collect_term t2)
         | FStar_Parser_AST.If (t1,t2,t3) ->
             (collect_term t1; collect_term t2; collect_term t3)
         | FStar_Parser_AST.Match (t,bs) ->
             (collect_term t; collect_branches bs)
         | FStar_Parser_AST.TryWith (t,bs) ->
             (collect_term t; collect_branches bs)
         | FStar_Parser_AST.Ascribed (t1,t2,FStar_Pervasives_Native.None ) ->
             (collect_term t1; collect_term t2)
         | FStar_Parser_AST.Ascribed (t1,t2,FStar_Pervasives_Native.Some tac)
             -> (collect_term t1; collect_term t2; collect_term tac)
         | FStar_Parser_AST.Record (t,idterms) ->
             (FStar_Util.iter_opt t collect_term;
              FStar_List.iter
                (fun uu____3372  ->
                   match uu____3372 with | (uu____3377,t1) -> collect_term t1)
                idterms)
         | FStar_Parser_AST.Project (t,uu____3380) -> collect_term t
         | FStar_Parser_AST.Product (binders,t) ->
             (collect_binders binders; collect_term t)
         | FStar_Parser_AST.Sum (binders,t) ->
             (collect_binders binders; collect_term t)
         | FStar_Parser_AST.QForall (binders,ts,t) ->
             (collect_binders binders;
              FStar_List.iter (FStar_List.iter collect_term) ts;
              collect_term t)
         | FStar_Parser_AST.QExists (binders,ts,t) ->
             (collect_binders binders;
              FStar_List.iter (FStar_List.iter collect_term) ts;
              collect_term t)
         | FStar_Parser_AST.Refine (binder,t) ->
             (collect_binder binder; collect_term t)
         | FStar_Parser_AST.NamedTyp (uu____3436,t) -> collect_term t
         | FStar_Parser_AST.Paren t -> collect_term t
         | FStar_Parser_AST.Requires (t,uu____3440) -> collect_term t
         | FStar_Parser_AST.Ensures (t,uu____3446) -> collect_term t
         | FStar_Parser_AST.Labeled (t,uu____3452,uu____3453) ->
             collect_term t
         | FStar_Parser_AST.VQuote t -> collect_term t
         | FStar_Parser_AST.Quote uu____3455 -> ()
         | FStar_Parser_AST.Antiquote uu____3460 -> ()
         | FStar_Parser_AST.Attributes cattributes ->
             FStar_List.iter collect_term cattributes
       
       and collect_patterns ps = FStar_List.iter collect_pattern ps
       
       and collect_pattern p = collect_pattern' p.FStar_Parser_AST.pat
       
       and collect_pattern' uu___114_3472 =
         match uu___114_3472 with
         | FStar_Parser_AST.PatWild  -> ()
         | FStar_Parser_AST.PatOp uu____3473 -> ()
         | FStar_Parser_AST.PatConst uu____3474 -> ()
         | FStar_Parser_AST.PatApp (p,ps) ->
             (collect_pattern p; collect_patterns ps)
         | FStar_Parser_AST.PatVar uu____3482 -> ()
         | FStar_Parser_AST.PatName uu____3489 -> ()
         | FStar_Parser_AST.PatTvar uu____3490 -> ()
         | FStar_Parser_AST.PatList ps -> collect_patterns ps
         | FStar_Parser_AST.PatOr ps -> collect_patterns ps
         | FStar_Parser_AST.PatTuple (ps,uu____3504) -> collect_patterns ps
         | FStar_Parser_AST.PatRecord lidpats ->
             FStar_List.iter
               (fun uu____3523  ->
                  match uu____3523 with | (uu____3528,p) -> collect_pattern p)
               lidpats
         | FStar_Parser_AST.PatAscribed (p,(t,FStar_Pervasives_Native.None ))
             -> (collect_pattern p; collect_term t)
         | FStar_Parser_AST.PatAscribed
             (p,(t,FStar_Pervasives_Native.Some tac)) ->
             (collect_pattern p; collect_term t; collect_term tac)
       
       and collect_branches bs = FStar_List.iter collect_branch bs
       
       and collect_branch uu____3573 =
         match uu____3573 with
         | (pat,t1,t2) ->
             (collect_pattern pat;
              FStar_Util.iter_opt t1 collect_term;
              collect_term t2)
        in
       let uu____3591 = FStar_Parser_Driver.parse_file filename  in
       match uu____3591 with
       | (ast,uu____3611) ->
           let mname = lowercase_module_name filename  in
           ((let uu____3626 =
               (is_interface filename) &&
                 (has_implementation original_map mname)
                in
             if uu____3626
             then add_dep mo_roots (UseImplementation mname)
             else ());
            collect_module ast;
            (let uu____3662 = FStar_ST.op_Bang deps  in
             let uu____3714 = FStar_ST.op_Bang mo_roots  in
             (uu____3662, uu____3714))))
  
let (collect_one_cache :
  (dependence Prims.list,dependence Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap FStar_ST.ref)
  =
  let uu____3793 = FStar_Util.smap_create (Prims.parse_int "0")  in
  FStar_Util.mk_ref uu____3793 
let (set_collect_one_cache :
  (dependence Prims.list,dependence Prims.list)
    FStar_Pervasives_Native.tuple2 FStar_Util.smap -> unit)
  = fun cache  -> FStar_ST.op_Colon_Equals collect_one_cache cache 
let (collect :
  Prims.string Prims.list ->
    (Prims.string Prims.list,deps) FStar_Pervasives_Native.tuple2)
  =
  fun all_cmd_line_files  ->
    let all_cmd_line_files1 =
      FStar_All.pipe_right all_cmd_line_files
        (FStar_List.map
           (fun fn  ->
              let uu____3922 = FStar_Options.find_file fn  in
              match uu____3922 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3925 =
                    let uu____3930 =
                      FStar_Util.format1 "File %s could not be found\n" fn
                       in
                    (FStar_Errors.Fatal_ModuleOrFileNotFound, uu____3930)  in
                  FStar_Errors.raise_err uu____3925
              | FStar_Pervasives_Native.Some fn1 -> fn1))
       in
    let dep_graph = deps_empty ()  in
    let file_system_map = build_map all_cmd_line_files1  in
    let rec discover_one file_name =
      let uu____3940 =
        let uu____3941 = deps_try_find dep_graph file_name  in
        uu____3941 = FStar_Pervasives_Native.None  in
      if uu____3940
      then
        let uu____3958 =
          let uu____3967 =
            let uu____3978 = FStar_ST.op_Bang collect_one_cache  in
            FStar_Util.smap_try_find uu____3978 file_name  in
          match uu____3967 with
          | FStar_Pervasives_Native.Some cached -> cached
          | FStar_Pervasives_Native.None  ->
              collect_one file_system_map file_name
           in
        match uu____3958 with
        | (deps,mo_roots) ->
            let deps1 =
              let module_name = lowercase_module_name file_name  in
              let uu____4087 =
                (is_implementation file_name) &&
                  (has_interface file_system_map module_name)
                 in
              if uu____4087
              then FStar_List.append deps [UseInterface module_name]
              else deps  in
            ((let uu____4092 =
                let uu____4097 = FStar_List.unique deps1  in
                (uu____4097, White)  in
              deps_add_dep dep_graph file_name uu____4092);
             (let uu____4098 =
                FStar_List.map
                  (file_of_dep file_system_map all_cmd_line_files1)
                  (FStar_List.append deps1 mo_roots)
                 in
              FStar_List.iter discover_one uu____4098))
      else ()  in
    FStar_List.iter discover_one all_cmd_line_files1;
    (let dep_graph_copy =
       let uu____4104 = dep_graph  in
       match uu____4104 with
       | Deps g ->
           let uu____4112 = FStar_Util.smap_copy g  in Deps uu____4112
        in
     let cycle_detected dep_graph1 cycle filename =
       FStar_Util.print1
         "The cycle contains a subset of the modules in:\n%s \n"
         (FStar_String.concat "\n`used by` " cycle);
       print_graph dep_graph1;
       FStar_Util.print_string "\n";
       (let uu____4146 =
          let uu____4151 =
            FStar_Util.format1 "Recursive dependency on module %s\n" filename
             in
          (FStar_Errors.Fatal_CyclicDependence, uu____4151)  in
        FStar_Errors.raise_err uu____4146)
        in
     let topological_dependences_of all_command_line_files =
       let topologically_sorted = FStar_Util.mk_ref []  in
       let rec aux cycle filename =
         let uu____4186 =
           let uu____4191 = deps_try_find dep_graph filename  in
           FStar_Util.must uu____4191  in
         match uu____4186 with
         | (direct_deps,color) ->
             (match color with
              | Gray  -> cycle_detected dep_graph cycle filename
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph filename (direct_deps, Gray);
                   (let uu____4206 =
                      dependences_of file_system_map dep_graph
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____4206);
                   deps_add_dep dep_graph filename (direct_deps, Black);
                   (let uu____4212 =
                      let uu____4215 = FStar_ST.op_Bang topologically_sorted
                         in
                      filename :: uu____4215  in
                    FStar_ST.op_Colon_Equals topologically_sorted uu____4212)))
          in
       FStar_List.iter (aux []) all_command_line_files;
       FStar_ST.op_Bang topologically_sorted  in
     let full_cycle_detection all_command_line_files =
       let dep_graph1 = dep_graph_copy  in
       let rec aux cycle filename =
         let uu____4392 =
           let uu____4399 = deps_try_find dep_graph1 filename  in
           match uu____4399 with
           | FStar_Pervasives_Native.Some (d,c) -> (d, c)
           | FStar_Pervasives_Native.None  ->
               let uu____4424 =
                 FStar_Util.format1 "Failed to find dependences of %s"
                   filename
                  in
               failwith uu____4424
            in
         match uu____4392 with
         | (direct_deps,color) ->
             let direct_deps1 =
               FStar_All.pipe_right direct_deps
                 (FStar_List.collect
                    (fun x  ->
                       match x with
                       | UseInterface f ->
                           let uu____4447 =
                             implementation_of file_system_map f  in
                           (match uu____4447 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____4453 -> [x; UseImplementation f])
                       | PreferInterface f ->
                           let uu____4457 =
                             implementation_of file_system_map f  in
                           (match uu____4457 with
                            | FStar_Pervasives_Native.None  -> [x]
                            | FStar_Pervasives_Native.Some fn when
                                fn = filename -> [x]
                            | uu____4463 -> [x; UseImplementation f])
                       | uu____4466 -> [x]))
                in
             (match color with
              | Gray  -> cycle_detected dep_graph1 cycle filename
              | Black  -> ()
              | White  ->
                  (deps_add_dep dep_graph1 filename (direct_deps1, Gray);
                   (let uu____4469 =
                      dependences_of file_system_map dep_graph1
                        all_command_line_files filename
                       in
                    FStar_List.iter (fun k  -> aux (k :: cycle) k) uu____4469);
                   deps_add_dep dep_graph1 filename (direct_deps1, Black)))
          in
       FStar_List.iter (aux []) all_command_line_files  in
     full_cycle_detection all_cmd_line_files1;
     FStar_All.pipe_right all_cmd_line_files1
       (FStar_List.iter
          (fun f  ->
             let m = lowercase_module_name f  in
             FStar_Options.add_verify_module m));
     (let uu____4482 = topological_dependences_of all_cmd_line_files1  in
      (uu____4482, (Mk (dep_graph, file_system_map, all_cmd_line_files1)))))
  
let (deps_of : deps -> Prims.string -> Prims.string Prims.list) =
  fun uu____4499  ->
    fun f  ->
      match uu____4499 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          dependences_of file_system_map deps all_cmd_line_files f
  
let (hash_dependences :
  deps ->
    Prims.string ->
      (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
        FStar_Pervasives_Native.option)
  =
  fun uu____4528  ->
    fun fn  ->
      match uu____4528 with
      | Mk (deps,file_system_map,all_cmd_line_files) ->
          let fn1 =
            let uu____4546 = FStar_Options.find_file fn  in
            match uu____4546 with
            | FStar_Pervasives_Native.Some fn1 -> fn1
            | uu____4550 -> fn  in
          let cache_file = cache_file_name fn1  in
          let digest_of_file1 fn2 =
            (let uu____4561 = FStar_Options.debug_any ()  in
             if uu____4561
             then
               FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2
             else ());
            FStar_Util.digest_of_file fn2  in
          let module_name = lowercase_module_name fn1  in
          let source_hash = digest_of_file1 fn1  in
          let interface_hash =
            let uu____4572 =
              (is_implementation fn1) &&
                (has_interface file_system_map module_name)
               in
            if uu____4572
            then
              let uu____4579 =
                let uu____4584 =
                  let uu____4585 =
                    let uu____4586 = interface_of file_system_map module_name
                       in
                    FStar_Option.get uu____4586  in
                  digest_of_file1 uu____4585  in
                ("interface", uu____4584)  in
              [uu____4579]
            else []  in
          let binary_deps =
            let uu____4605 =
              dependences_of file_system_map deps all_cmd_line_files fn1  in
            FStar_All.pipe_right uu____4605
              (FStar_List.filter
                 (fun fn2  ->
                    let uu____4615 =
                      (is_interface fn2) &&
                        (let uu____4617 = lowercase_module_name fn2  in
                         uu____4617 = module_name)
                       in
                    Prims.op_Negation uu____4615))
             in
          let binary_deps1 =
            FStar_List.sortWith
              (fun fn11  ->
                 fun fn2  ->
                   let uu____4627 = lowercase_module_name fn11  in
                   let uu____4628 = lowercase_module_name fn2  in
                   FStar_String.compare uu____4627 uu____4628) binary_deps
             in
          let rec hash_deps out uu___115_4655 =
            match uu___115_4655 with
            | [] ->
                FStar_Pervasives_Native.Some
                  (FStar_List.append (("source", source_hash) ::
                     interface_hash) out)
            | fn2::deps1 ->
                let cache_fn = cache_file_name fn2  in
                if FStar_Util.file_exists cache_fn
                then
                  let uu____4699 =
                    let uu____4706 =
                      let uu____4711 = lowercase_module_name fn2  in
                      let uu____4712 = digest_of_file1 cache_fn  in
                      (uu____4711, uu____4712)  in
                    uu____4706 :: out  in
                  hash_deps uu____4699 deps1
                else
                  ((let uu____4719 = FStar_Options.debug_any ()  in
                    if uu____4719
                    then
                      FStar_Util.print2 "%s: missed digest of file %s\n"
                        cache_file cache_fn
                    else ());
                   FStar_Pervasives_Native.None)
             in
          hash_deps [] binary_deps1
  
let (print_digest :
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list ->
    Prims.string)
  =
  fun dig  ->
    let uu____4748 =
      FStar_All.pipe_right dig
        (FStar_List.map
           (fun uu____4767  ->
              match uu____4767 with
              | (m,d) ->
                  let uu____4774 = FStar_Util.base64_encode d  in
                  FStar_Util.format2 "%s:%s" m uu____4774))
       in
    FStar_All.pipe_right uu____4748 (FStar_String.concat "\n")
  
let (print_make : deps -> unit) =
  fun uu____4781  ->
    match uu____4781 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let keys = deps_keys deps  in
        FStar_All.pipe_right keys
          (FStar_List.iter
             (fun f  ->
                let uu____4801 =
                  let uu____4806 = deps_try_find deps f  in
                  FStar_All.pipe_right uu____4806 FStar_Option.get  in
                match uu____4801 with
                | (f_deps,uu____4828) ->
                    let files =
                      FStar_List.map
                        (file_of_dep file_system_map all_cmd_line_files)
                        f_deps
                       in
                    let files1 =
                      FStar_List.map
                        (fun s  -> FStar_Util.replace_chars s 32 "\\ ") files
                       in
                    FStar_Util.print2 "%s: %s\n\n" f
                      (FStar_String.concat " " files1)))
  
let (print_full : deps -> unit) =
  fun uu____4842  ->
    match uu____4842 with
    | Mk (deps,file_system_map,all_cmd_line_files) ->
        let sort_output_files orig_output_file_map =
          let order = FStar_Util.mk_ref []  in
          let remaining_output_files =
            FStar_Util.smap_copy orig_output_file_map  in
          let visited_other_modules =
            FStar_Util.smap_create (Prims.parse_int "41")  in
          let should_visit lc_module_name =
            (let uu____4883 =
               FStar_Util.smap_try_find remaining_output_files lc_module_name
                in
             FStar_Option.isSome uu____4883) ||
              (let uu____4887 =
                 FStar_Util.smap_try_find visited_other_modules
                   lc_module_name
                  in
               FStar_Option.isNone uu____4887)
             in
          let mark_visiting lc_module_name =
            let ml_file_opt =
              FStar_Util.smap_try_find remaining_output_files lc_module_name
               in
            FStar_Util.smap_remove remaining_output_files lc_module_name;
            FStar_Util.smap_add visited_other_modules lc_module_name true;
            ml_file_opt  in
          let emit_output_file_opt ml_file_opt =
            match ml_file_opt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some ml_file ->
                let uu____4914 =
                  let uu____4917 = FStar_ST.op_Bang order  in ml_file ::
                    uu____4917
                   in
                FStar_ST.op_Colon_Equals order uu____4914
             in
          let rec aux uu___116_5025 =
            match uu___116_5025 with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
                let visit_file file_opt =
                  match file_opt with
                  | FStar_Pervasives_Native.None  -> ()
                  | FStar_Pervasives_Native.Some file_name ->
                      let uu____5043 = deps_try_find deps file_name  in
                      (match uu____5043 with
                       | FStar_Pervasives_Native.None  ->
                           let uu____5054 =
                             FStar_Util.format2
                               "Impossible: module %s: %s not found"
                               lc_module_name file_name
                              in
                           failwith uu____5054
                       | FStar_Pervasives_Native.Some
                           (immediate_deps,uu____5056) ->
                           let immediate_deps1 =
                             FStar_List.map
                               (fun x  ->
                                  FStar_String.lowercase
                                    (module_name_of_dep x)) immediate_deps
                              in
                           aux immediate_deps1)
                   in
                ((let uu____5067 = should_visit lc_module_name  in
                  if uu____5067
                  then
                    let ml_file_opt = mark_visiting lc_module_name  in
                    ((let uu____5072 =
                        implementation_of file_system_map lc_module_name  in
                      visit_file uu____5072);
                     (let uu____5076 =
                        interface_of file_system_map lc_module_name  in
                      visit_file uu____5076);
                     emit_output_file_opt ml_file_opt)
                  else ());
                 aux modules_to_extract)
             in
          let all_extracted_modules =
            FStar_Util.smap_keys orig_output_file_map  in
          aux all_extracted_modules;
          (let uu____5084 = FStar_ST.op_Bang order  in
           FStar_List.rev uu____5084)
           in
        let keys = deps_keys deps  in
        let output_file ext fst_file =
          let ml_base_name =
            let uu____5151 =
              let uu____5152 =
                let uu____5155 = FStar_Util.basename fst_file  in
                check_and_strip_suffix uu____5155  in
              FStar_Option.get uu____5152  in
            FStar_Util.replace_chars uu____5151 46 "_"  in
          FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext)
           in
        let norm_path s = FStar_Util.replace_chars s 92 "/"  in
        let output_ml_file f =
          let uu____5170 = output_file ".ml" f  in norm_path uu____5170  in
        let output_krml_file f =
          let uu____5177 = output_file ".krml" f  in norm_path uu____5177  in
        let output_cmx_file f =
          let uu____5184 = output_file ".cmx" f  in norm_path uu____5184  in
        let cache_file f =
          let uu____5191 = cache_file_name f  in norm_path uu____5191  in
        let transitive_krml = FStar_Util.smap_create (Prims.parse_int "41")
           in
        (FStar_All.pipe_right keys
           (FStar_List.iter
              (fun f  ->
                 let uu____5234 =
                   let uu____5241 = deps_try_find deps f  in
                   FStar_All.pipe_right uu____5241 FStar_Option.get  in
                 match uu____5234 with
                 | (f_deps,uu____5265) ->
                     let norm_f = norm_path f  in
                     let files =
                       FStar_List.map
                         (file_of_dep_aux true file_system_map
                            all_cmd_line_files) f_deps
                        in
                     let files1 = FStar_List.map norm_path files  in
                     let files2 =
                       FStar_List.map
                         (fun s  -> FStar_Util.replace_chars s 32 "\\ ")
                         files1
                        in
                     let files3 = FStar_String.concat "\\\n\t" files2  in
                     ((let uu____5285 = is_interface f  in
                       if uu____5285
                       then
                         let uu____5286 =
                           let uu____5287 =
                             FStar_Options.prepend_cache_dir norm_f  in
                           norm_path uu____5287  in
                         FStar_Util.print3
                           "%s.source: %s \\\n\t%s\n\ttouch $@\n\n"
                           uu____5286 norm_f files3
                       else ());
                      (let uu____5290 = cache_file f  in
                       FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____5290
                         norm_f files3);
                      (let already_there =
                         let uu____5294 =
                           let uu____5305 =
                             let uu____5306 = output_file ".krml" f  in
                             norm_path uu____5306  in
                           FStar_Util.smap_try_find transitive_krml
                             uu____5305
                            in
                         match uu____5294 with
                         | FStar_Pervasives_Native.Some
                             (uu____5317,already_there,uu____5319) ->
                             already_there
                         | FStar_Pervasives_Native.None  -> []  in
                       (let uu____5341 =
                          let uu____5342 = output_file ".krml" f  in
                          norm_path uu____5342  in
                        let uu____5343 =
                          let uu____5352 =
                            let uu____5353 = output_file ".exe" f  in
                            norm_path uu____5353  in
                          let uu____5354 =
                            let uu____5357 =
                              let uu____5360 =
                                let uu____5363 =
                                  deps_of
                                    (Mk
                                       (deps, file_system_map,
                                         all_cmd_line_files)) f
                                   in
                                FStar_List.map
                                  (fun x  ->
                                     let uu____5371 = output_file ".krml" x
                                        in
                                     norm_path uu____5371) uu____5363
                                 in
                              FStar_List.append already_there uu____5360  in
                            FStar_List.unique uu____5357  in
                          (uu____5352, uu____5354, false)  in
                        FStar_Util.smap_add transitive_krml uu____5341
                          uu____5343);
                       (let uu____5382 = is_implementation f  in
                        if uu____5382
                        then
                          ((let uu____5384 = output_ml_file f  in
                            let uu____5385 = cache_file f  in
                            FStar_Util.print2 "%s: %s\n\n" uu____5384
                              uu____5385);
                           (let cmx_files =
                              let fst_files =
                                FStar_All.pipe_right f_deps
                                  (FStar_List.map
                                     (file_of_dep_aux false file_system_map
                                        all_cmd_line_files))
                                 in
                              let extracted_fst_files =
                                FStar_All.pipe_right fst_files
                                  (FStar_List.filter
                                     (fun df  ->
                                        (let uu____5409 =
                                           lowercase_module_name df  in
                                         let uu____5410 =
                                           lowercase_module_name f  in
                                         uu____5409 <> uu____5410) &&
                                          (let uu____5412 =
                                             lowercase_module_name df  in
                                           FStar_Options.should_extract
                                             uu____5412)))
                                 in
                              FStar_All.pipe_right extracted_fst_files
                                (FStar_List.map output_cmx_file)
                               in
                            (let uu____5418 =
                               let uu____5419 = lowercase_module_name f  in
                               FStar_Options.should_extract uu____5419  in
                             if uu____5418
                             then
                               let uu____5420 = output_cmx_file f  in
                               let uu____5421 = output_ml_file f  in
                               FStar_Util.print3 "%s: %s \\\n\t%s\n\n"
                                 uu____5420 uu____5421
                                 (FStar_String.concat "\\\n\t" cmx_files)
                             else ());
                            (let uu____5423 = output_krml_file f  in
                             let uu____5424 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5423
                               uu____5424)))
                        else
                          (let uu____5426 =
                             (let uu____5429 =
                                let uu____5430 = lowercase_module_name f  in
                                has_implementation file_system_map uu____5430
                                 in
                              Prims.op_Negation uu____5429) &&
                               (is_interface f)
                              in
                           if uu____5426
                           then
                             let uu____5431 = output_krml_file f  in
                             let uu____5432 = cache_file f  in
                             FStar_Util.print2 "%s: %s\n\n" uu____5431
                               uu____5432
                           else ()))))));
         (let all_fst_files =
            let uu____5437 =
              FStar_All.pipe_right keys (FStar_List.filter is_implementation)
               in
            FStar_All.pipe_right uu____5437
              (FStar_Util.sort_with FStar_String.compare)
             in
          let all_ml_files =
            let ml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right all_fst_files
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5463 = FStar_Options.should_extract mname  in
                    if uu____5463
                    then
                      let uu____5464 = output_ml_file fst_file  in
                      FStar_Util.smap_add ml_file_map mname uu____5464
                    else ()));
            sort_output_files ml_file_map  in
          let all_krml_files =
            let krml_file_map = FStar_Util.smap_create (Prims.parse_int "41")
               in
            FStar_All.pipe_right keys
              (FStar_List.iter
                 (fun fst_file  ->
                    let mname = lowercase_module_name fst_file  in
                    let uu____5480 = output_krml_file fst_file  in
                    FStar_Util.smap_add krml_file_map mname uu____5480));
            sort_output_files krml_file_map  in
          let rec make_transitive f =
            let uu____5493 =
              let uu____5502 = FStar_Util.smap_try_find transitive_krml f  in
              FStar_Util.must uu____5502  in
            match uu____5493 with
            | (exe,deps1,seen) ->
                if seen
                then (exe, deps1)
                else
                  (FStar_Util.smap_add transitive_krml f (exe, deps1, true);
                   (let deps2 =
                      let uu____5565 =
                        let uu____5568 =
                          FStar_List.map
                            (fun dep1  ->
                               let uu____5580 = make_transitive dep1  in
                               match uu____5580 with
                               | (uu____5589,deps2) -> dep1 :: deps2) deps1
                           in
                        FStar_List.flatten uu____5568  in
                      FStar_List.unique uu____5565  in
                    FStar_Util.smap_add transitive_krml f (exe, deps2, true);
                    (exe, deps2)))
             in
          (let uu____5609 = FStar_Util.smap_keys transitive_krml  in
           FStar_List.iter
             (fun f  ->
                let uu____5628 = make_transitive f  in
                match uu____5628 with
                | (exe,deps1) ->
                    let deps2 =
                      let uu____5642 = FStar_List.unique (f :: deps1)  in
                      FStar_String.concat " " uu____5642  in
                    let wasm =
                      let uu____5646 =
                        FStar_Util.substring exe (Prims.parse_int "0")
                          ((FStar_String.length exe) - (Prims.parse_int "4"))
                         in
                      Prims.strcat uu____5646 ".wasm"  in
                    (FStar_Util.print2 "%s: %s\n\n" exe deps2;
                     FStar_Util.print2 "%s: %s\n\n" wasm deps2)) uu____5609);
          (let uu____5649 =
             let uu____5650 =
               FStar_All.pipe_right all_fst_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5650 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____5649);
          (let uu____5660 =
             let uu____5661 =
               FStar_All.pipe_right all_ml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5661 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____5660);
          (let uu____5670 =
             let uu____5671 =
               FStar_All.pipe_right all_krml_files (FStar_List.map norm_path)
                in
             FStar_All.pipe_right uu____5671 (FStar_String.concat " \\\n\t")
              in
           FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____5670)))
  
let (print : deps -> unit) =
  fun deps  ->
    let uu____5685 = FStar_Options.dep ()  in
    match uu____5685 with
    | FStar_Pervasives_Native.Some "make" -> print_make deps
    | FStar_Pervasives_Native.Some "full" -> print_full deps
    | FStar_Pervasives_Native.Some "graph" ->
        let uu____5688 = deps  in
        (match uu____5688 with
         | Mk (deps1,uu____5690,uu____5691) -> print_graph deps1)
    | FStar_Pervasives_Native.Some uu____5696 ->
        FStar_Errors.raise_err
          (FStar_Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
    | FStar_Pervasives_Native.None  -> ()
  