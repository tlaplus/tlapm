(* Writing and loading of modules.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Property
open Util.Coll

open Tla_parser
open Tla_parser.P

open M_t
open M_parser


(* let debug = Printf.eprintf *)
exception Unknown_module_exception
exception Not_loadable_exception of string wrapped


let clocking cl fn x =
    match cl with
    | Some cl ->
        Timing.start cl;
        let ret = fn x in
        Timing.stop ();
        ret
    | None ->
        fn x



type module_content = Channel of in_channel | String of string | Filesystem

let module_content_prop = Property.make "module_content"

let file_search' fh =
    if Filename.is_implicit fh.core then
        let rec scan = function
            | [] -> None
            | d :: ds ->
                let f = Filename.concat d fh.core in
                if Sys.file_exists f then
                    Some (f @@ fh)
                else scan ds
        in scan ("." :: List.rev !Params.rev_search_path)
    else
        if Sys.file_exists fh.core then
            Some fh
        else None

let file_search'' fh =
    match file_search' fh with
    | None -> (
        match Loader.Global.load fh.core with
        | Some content ->
            let fh = Property.assign fh module_content_prop (String content) in
            Some fh
        | None -> None)
    | Some fh -> Some fh

let file_search fh =
    match Property.query fh module_content_prop with
    | Some (Channel _)
    | Some (String _) -> Some fh
    | Some Filesystem
    | None -> file_search'' fh


let really_parse_file fn =
    match file_search fn with
    | None ->
        Util.eprintf ~at:fn
            "Could not find file %S in the search path."
            fn.core;
        failwith "Module.Parser.parse_file"
    | Some fn ->
        let (flex, _) = match Property.query fn module_content_prop with
            | Some (Channel ch) -> Alexer.lex_channel fn.core ch
            | Some (String str) -> Alexer.lex_string ~fn:fn.core str
            | Some Filesystem
            | None -> Alexer.lex fn.core
        in
        let hparse = use parse in
        match P.run hparse ~init:Tla_parser.init ~source:flex with
        | None ->
            Util.eprintf ~at:fn
                "Could not parse %S successfully."
                fn.core;
            failwith "Module.Parser.parse_file"
        | Some mule ->
            if !Params.verbose then begin
                Util.printf
                    "(* module %S parsed from %S *)"
                    mule.core.name.core
                    fn.core;
            end;
            let rawname =
                Filename.chop_suffix
                    (Filename.basename fn.core)
                    ".tla" in
            if mule.core.name.core <> rawname then begin
                Errors.err  ~at:mule
                    "Warning: module name %S does not match \
                    file name %S."
                    mule.core.name.core
                    (Filename.basename fn.core);
                let newname = {mule.core.name with core=rawname} in
                {mule with core={mule.core with name=newname}}
            end else
                mule


let validate mn inch =
    let v: string = Marshal.from_channel inch in
    if v = Params.rawversion () then
        let h = Digest.input inch in
        if h = Params.self_sum then
            let csum = Digest.input inch in
            let mule: mule = Marshal.from_channel inch in
            (close_in inch;
             Some (csum, mule))
        else
            (close_in inch;
             None)
    else
        (close_in inch;
         None)


let rec really_load_module mn fn fnx =
    match fn, fnx with
    | Some _, Some _ when not !Params.use_xtla ->
        really_load_module mn fn None
    | None, None ->
        (* Util.eprintf ~at:mn
            "Unknown module %S" mn.core;
        Errors.set mn (Printf.sprintf  "Unknown module %S" mn.core);
        failwith "Module.Parser.load_module"
        *)
        raise Unknown_module_exception
    | Some fn, None ->
        really_parse_file fn
    | None, Some fnx ->
        begin match validate mn (open_in_bin fnx.core) with
        | Some (_, m) ->
            if !Params.verbose then
                Util.printf
                    "(* module %S loaded from %S *)"
                    m.core.name.core
                    fnx.core;
            m
        | None ->
            (* Util.eprintf ~at:fnx
                "%S not loadable\nNo corresponding source found either!"
                fnx.core;
            failwith "Module.Parser.load_module"
            *)
            raise (Not_loadable_exception fnx)
        end
    | Some fn, Some fnx ->
        begin match validate mn (open_in_bin fnx.core) with
        | Some (csum, m) when csum = Digest.file fn.core ->
            if !Params.verbose then
                Util.printf
                    "(* module %S loaded from %S *)"
                    m.core.name.core
                    fnx.core;
                m
        | _ ->
            really_parse_file fn
        end


let load_module ?clock ?root:(r="") mn =
    clocking clock begin fun () ->
        let fn = (Filename.concat r (mn.core ^ ".tla")) @@ mn in
        let fnx = (Filename.concat r (mn.core ^ ".xtla")) @@ mn in
        really_load_module mn (file_search fn) (file_search fnx)
    end ()


let parse_file ?clock gfn =
    clocking clock begin fun () ->
        let fn = begin
            if Filename.check_suffix gfn.core ".tla" then
                Filename.chop_suffix gfn.core ".tla"
            else
                gfn.core
        end @@ gfn in
        let mn = (Filename.basename fn.core) @@ fn in
        let fnx = file_search ((fn.core ^ ".xtla") @@ fn) in
        let fn = file_search ((fn.core ^ ".tla") @@ fn) in
            if fn = None && fnx = None then begin
                Util.eprintf ~at:gfn
                    "File %S not found" gfn.core;
                Errors.set
                    gfn (Printf.sprintf "File %s not found" gfn.core);
                failwith "Module.Parser.parse_file"
            end else
                really_load_module mn fn fnx
    end ()


let complete_load ?clock ?root:(r="") mcx =
    clocking clock
    begin fun () ->
        let requested = ref Hs.empty in
        (* suffices to compare to found modules by name.
        `Module.Elab` will add submodules of extended modules to the
        module context, before those are instantiated.
        *)
        let found = ref Hs.empty in
        let mods = ref Deque.empty in
        Sm.iter (fun _ mule -> mods := Deque.snoc !mods mule) mcx;
        let rec spin mcx =
            match Deque.front !mods with
            | None -> mcx
            | Some (mule, rest) ->
                mods := rest;
                let (eds, submodule_names, submodules) =
                    M_dep.external_deps mule in
                found := Hs.union submodule_names !found;
                let mcx = Sm.merge
                    (fun k v1 v2 -> if v1 = None then v2 else v1)
                    mcx submodules in
                (*
                print_string "\n--------\n";
                Hs.iter (fun x -> print_string (x.core ^ "\n")) eds;
                print_string "\n--------\n";
                *)
                let mcx = Hs.fold begin
                    fun ed mcx ->
                        (* let mn = ed in *)
                        (* if module name is also a name of
                        a standrd module, try to load it anyway
                        *)
                        if ((not !Params.prefer_stdlib) && (Sm.mem ed.core M_standard.initctx)) then
                            try
                                let emule = load_module ~root:r ed in
                                mods := Deque.snoc !mods emule;
                                Sm.add ed.core emule mcx
                            with Unknown_module_exception ->
                                (* expected behavior--standard module
                                will be used
                                *)
                                mcx
                            | Not_loadable_exception fnx ->
                                Util.eprintf ~at:fnx
                                    "%S not loadable\n\
                                    No corresponding source found either!"
                                    fnx.core;
                                failwith "Module.Parser.load_module"
                        (* else load it only if it is not already defined
                        (either because a file already loaded, or
                        because a submodule of
                        the current module, or a submodule of
                        a module already loaded)
                        *)
                        else if (Sm.mem ed.core mcx) then mcx
                        else
                            try
                                let emule = load_module ~root:r ed in
                                mods := Deque.snoc !mods emule;
                                Sm.add ed.core emule mcx
                            with Unknown_module_exception ->
                                (* Modules from `INSTANCE` and `EXTENDS`
                                statements could be
                                submodules of a module that the
                                module extends, and is
                                itself another file.
                                *)
                                requested := Hs.add ed !requested;
                                mcx
                                (*
                                Util.eprintf ~at:mn
                                    "Unknown module %S" mn.core;
                                Errors.set
                                    mn
                                    (Printf.sprintf
                                        "Unknown module %S" mn.core);
                                failwith "Module.Parser.load_module"
                                *)
                            | Not_loadable_exception fnx ->
                                Util.eprintf ~at:fnx
                                    "%S not loadable\n\
                                    No corresponding source found either!"
                                    fnx.core;
                                failwith "Module.Parser.load_module"
                    end eds mcx in
                spin mcx in
                let res = spin mcx in
                (*
                print_int (Sm.cardinal res);
                print_int (Hs.cardinal !found);
                print_int (Hs.cardinal !requested);

                print_string "\nResult:\n";
                Sm.iter
                    (fun x y -> print_string (y.core.name.core ^ "\n"))
                    res;

                print_string "\nFound modules:\n";
                Hs.iter
                    (fun x -> print_string (x.core ^ "\n"))
                    !found;

                print_string "\nRequested modules:\n";
                Hs.iter
                    (fun x -> print_string (x.core ^ "\n"))
                    !requested;
                *)
                if not (Hs.subset !requested !found) then begin
                    let not_found = Hs.diff !requested !found in
                    Hs.iter (fun mn ->
                        Util.eprintf ~at:mn
                            "Unknown module %S" mn.core;
                            Errors.set
                                mn
                                (Printf.sprintf
                                    "Unknown module %S" mn.core)
                        ) not_found;
                    failwith "Module.Parser.load_module"
                end;
                res
    end ()


let store_module ?clock mule =
    if !Params.xtla then
        clocking clock begin fun () ->
            let fn = (Util.get_locus mule).Loc.file in
            let fnx = Filename.chop_extension fn ^ ".xtla" in
            let fx = open_out_bin fnx in
            Marshal.to_channel fx Params.rawversion [];
            Digest.output fx Params.self_sum;
            Digest.output fx (Digest.file fn);
            Marshal.to_channel fx mule [];
            close_out fx;
                if !Params.verbose then
                    Util.printf "(* compiled module %S saved to %S *)"
                        mule.core.name.core fnx
            end ()
    else ()


let%test_module _ = (module struct

    let stloc =
        { Loc.file = "<Test>" ;
          Loc.start = Loc.dummy ;
          Loc.stop = Loc.dummy }
    let stm x = Util.locate x stloc
    let create_test_case ls =
    List.fold_left begin
        fun acc (nm,depls,df) ->
        let m = begin
            stm {
                name = noprops nm ;
                extendees = List.map (function x -> noprops x) depls ;
                instancees = [] ;
                defdepth = 0 ;
                important = true ;
                body = [ noprops (Variables [noprops df]) ];
                stage = Parsed ;
            }
        end in
        Sm.add m.core.name.core m acc
    end M_standard.initctx ls

    let%test "t1: load external modules correctly for external modules which has the same name as a standard module - load local module" =
        Loader.Global.setup [];
        let test_case_list = [("a",["TLC"],"B")] in
        let test_case = create_test_case  test_case_list in
            let rfold = List.fold_left Filename.concat ".." ["test"; "resources"; "module"; "m_save"] in
            (List.exists
                (function
                    | {core = Variables ls} -> List.exists (fun x -> x.core = "m_save_t1") ls
                    | _ -> false )
                (Sm.find "TLC" (complete_load ~root:rfold test_case)).core.body)

    let%test "t2: load external modules correctly for external modules which has the same name as a standard module - load standard module" =
        Loader.Global.setup [];
        let test_case_list = [("a",["TLC"],"B")] in
        let test_case = create_test_case  test_case_list in
            (Sm.mem "TLC" (complete_load test_case))

end)
