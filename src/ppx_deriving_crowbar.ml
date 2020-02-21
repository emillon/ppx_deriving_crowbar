open Ppxlib
open Ast_helper

let mkloc txt loc = {Location.txt; loc}

let lid ~loc s = mkloc (Longident.parse s) loc

let free_vars_in_core_type typ =
  let rec free_in typ =
    match typ with
    | { ptyp_desc = Ptyp_any; _ } -> []
    | { ptyp_desc = Ptyp_var name; _ } ->
      [mkloc name typ.ptyp_loc]
    | { ptyp_desc = Ptyp_arrow (_, x, y); _ } -> free_in x @ free_in y
    | { ptyp_desc = (Ptyp_tuple xs | Ptyp_constr (_, xs)); _ } ->
      List.map free_in xs |> List.concat
    | { ptyp_desc = Ptyp_alias (x, name); _ } ->
      [mkloc name typ.ptyp_loc]
      @ free_in x
    | { ptyp_desc = Ptyp_poly (bound, x); _ } ->
      List.filter (fun y -> not (List.mem y bound)) (free_in x)
    | { ptyp_desc = Ptyp_variant (rows, _, _); _ } ->
      List.map (
          function 
                    {prf_desc = Rtag(_, _, ts); _}  
                                     -> List.map free_in ts
                 | 
                    {prf_desc = Rinherit(t); _}  
                                    -> [free_in t]
        ) rows |> List.concat |> List.concat
    | _ -> assert false
  in
  let uniq lst =
    let module StringSet = Set.Make(String) in
    let add name (names, txts) =
      let txt =
        name.txt
      in
      if StringSet.mem txt txts
      then (names, txts)
      else (name :: names, StringSet.add txt txts)
    in fst (List.fold_right add lst ([], StringSet.empty))
  in free_in typ |> uniq

let strong_type_of_type ty =
  let free_vars = free_vars_in_core_type ty in
  Typ.force_poly @@ Typ.poly free_vars ty

let app ~loc f = function
  | [] -> f
  | args -> Ast_helper.Exp.apply ~loc f
    (List.map (fun arg -> (Nolabel, arg)) args)

module Attr = struct
  let generator =
    Attribute.declare
      "crowbar.generator"
      Attribute.Context.core_type
      Ast_pattern.(single_expr_payload __)
      (fun x -> x)

  let generator_cd =
    Attribute.declare
      "crowbar.generator"
      Attribute.Context.constructor_declaration
      Ast_pattern.(single_expr_payload __)
      (fun x -> x)

  let generator_td =
    Attribute.declare
      "crowbar.generator"
      Attribute.Context.type_declaration
      Ast_pattern.(single_expr_payload __)
      (fun x -> x)

  let packed =
    [ Attribute.T generator
    ; Attribute.T generator_cd
    ; Attribute.T generator_td
    ]
end

let deriver = "crowbar"
let raise_errorf = Location.raise_errorf

let mangle = function
  | "t" -> "to_crowbar"
  | s -> s ^ "_to_crowbar"

let mangle_lid = function
  | Longident.Lident s -> Lident (mangle s)
  | Ldot (p, s) -> Ldot (p, mangle s)
  | Lapply _    -> assert false

let mangle_type_decl { ptype_name = { txt = name; _ }; _ } =
  mangle name

let unlazify_attribute_name = "crowbar_recursive_typedef_please_unlazy"
  (* TODO: actually make sure this is unique *)

(* XXX *)
let string_of_core_type  _ = "<STRING_OF_CORE_TYPE>"

let make_crowbar_list ~loc l =
  let cons h t = [%expr Crowbar.(::) ([%e h], [%e t])] in
  let nil = [%expr Crowbar.[]] in
  List.fold_right cons l nil

let n_vars l =
  List.mapi (fun i _ -> Printf.sprintf "a%d" i) l

let last_fun ~loc arg function_body =
  [%expr fun [%p (Ast_helper.Pat.var (mkloc arg loc))] -> [%e function_body]]

let lazify loc e = [%expr lazy [%e e]]

let remove_pervasives ~deriver:_ typ =
  (* XXX *)
      (*Ppx_deriving.remove_pervasives ~deriver typ in*)
  typ

let rec expr_of_typ always_nonempty quoter typ =
  let expr_of_typ = expr_of_typ always_nonempty quoter in
  let loc = typ.ptyp_loc in
  match Attribute.get Attr.generator typ with
  | Some generator ->
    [%expr [%e Ppxlib.Quoter.quote quoter generator] () ]
  | None ->
  let typ = remove_pervasives ~deriver typ in
  let loc = typ.ptyp_loc in
  match typ with
  | { ptyp_desc = Ptyp_constr ({ txt = lid; _ }, args); _ } ->
    begin
      match typ with
    | [%type: unit] -> [%expr Crowbar.const ()]
    | [%type: int] -> [%expr Crowbar.int]
    | [%type: int32]
    | [%type: Int32.t] -> [%expr Crowbar.int32]
    | [%type: int64]
    | [%type: Int64.t] -> [%expr Crowbar.int64]
    | [%type: float] -> [%expr Crowbar.float]
    | [%type: bool] -> [%expr Crowbar.bool]
    | [%type: char] -> [%expr Crowbar.(map [uint8] Char.chr)]
    | [%type: string]
    | [%type: String.t] -> [%expr Crowbar.bytes]
    | [%type: bytes]
    | [%type: Bytes.t] -> [%expr Crowbar.(map [bytes] Bytes.of_string)]
    | [%type: nativeint]
    | [%type: Nativeint.t] -> [%expr Crowbar.(map [int] Nativeint.of_int)]
    (* also TODO: do we DTRT for [@nobuiltin]?  nope. *)
    | [%type: [%t? typ] option] ->
      [%expr Crowbar.(option [%e expr_of_typ typ])]
    | [%type: [%t? typ] ref] ->
      [%expr Crowbar.(map [[%e expr_of_typ typ]] (fun a -> ref a))]
    | [%type: [%t? typ] list] ->
      if always_nonempty then [%expr Crowbar.(list1 [%e expr_of_typ typ])]
      else [%expr Crowbar.(list [%e expr_of_typ typ])]
    | [%type: [%t? typ] array] ->
      if always_nonempty then [%expr Crowbar.(map [list1 [%e expr_of_typ typ]] Array.of_list)]
      else [%expr Crowbar.(map [list [%e expr_of_typ typ]] Array.of_list)]
    | [%type: [%t? typ] lazy_t]
    | [%type: [%t? typ] Lazy.t] ->
      [%expr Crowbar.(map [[%e expr_of_typ typ]] (fun a -> lazy a))]
    | [%type: ([%t? ok_t], [%t? err_t]) result]
    | [%type: ([%t? ok_t], [%t? err_t]) Result.result] ->
      [%expr Crowbar.(map [bool; [%e expr_of_typ ok_t]; [%e expr_of_typ err_t]]
             (fun b x y ->
               if b then (Result.Ok x)
               else (Result.Error y)
             ))
      ]

    | _ ->
    let fwd = app ~loc (Exp.ident (mkloc (mangle_lid lid) loc))
        (List.map expr_of_typ args)
    in
    (* XXX weird *)
    let matches {attr_name = {txt; _}; _} = (0 = String.compare txt unlazify_attribute_name) in
    match List.exists matches typ.ptyp_attributes with
    | true -> [%expr Crowbar.unlazy [%e fwd]]
    | false -> [%expr [%e fwd]]
    end
  | { ptyp_desc = Ptyp_tuple tuple; ptyp_loc = loc; _ } ->
    let gens, vars_to_tuple = generate_tuple ~loc always_nonempty quoter tuple in
    [%expr Crowbar.(map [%e (make_crowbar_list ~loc gens)] [%e vars_to_tuple])]
  | { ptyp_desc = Ptyp_var name; _ } -> Ast_builder.Default.evar ~loc ("poly_"^name)
  | { ptyp_desc = Ptyp_alias (typ, _); _ } -> expr_of_typ typ
  | { ptyp_desc = Ptyp_variant (fields, _, _);ptyp_loc; _} ->
        (* I think we don't care about open vs closed, we just want to wrap thee
           things in the right rows; similarly we don't care about labels *)
        (* just like for non-poly variants, we need to choose from the set of
           available things (which we can't get more clues about than this here
           typedef... hm, unless the labels are clues, actually; TODO think
           about that a bit more, I think they're not but make sure). *)
    let translate = function
      | Rinherit typ -> expr_of_typ typ
      | Rtag (label, _, []) ->
        (* nullary, just use the label name *)
        [%expr Crowbar.const [%e Ast_helper.Exp.variant label.txt None]]
      | Rtag (label, _, [{ptyp_desc = Ptyp_tuple tuple; ptyp_loc=loc; _}]) ->
        (* good ol' tuples *)
        let (gens, last_fun) =
          generate_tuple ~loc always_nonempty quoter
            ~constructor:(Ast_helper.Exp.variant label.txt) tuple in
        [%expr Crowbar.(map [%e (make_crowbar_list ~loc gens)] [%e last_fun])]
      | Rtag (label, _, [typ] (* one non-tuple thing *)) ->
        let var = "a" in
        let body = Ast_helper.Exp.(variant label.txt (Some [%expr a])) in
        let fn = last_fun ~loc var body in
        [%expr Crowbar.(map [[%e expr_of_typ typ]] [%e fn])]
                                                 
      | Rtag _ -> raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                      deriver (string_of_core_type typ)
    in
    let cases = List.map (fun x -> translate x.prf_desc) fields in
    [%expr Crowbar.choose [%e (make_crowbar_list ~loc cases)]]
  | { ptyp_loc; _ } -> raise_errorf ~loc:ptyp_loc "%s cannot be derived for %s"
                      deriver (string_of_core_type typ)
and generate_tuple ~loc always_nonempty quoter ?constructor tuple =
  let vars = n_vars tuple in
  let vars_tuple =
    List.map (Ast_builder.Default.evar ~loc) vars
    |> Ast_builder.Default.pexp_tuple ~loc
  in
  let vars_tuple = match constructor with
  | Some constructor -> constructor (Some vars_tuple)
  | None -> vars_tuple
  in
  let fn_vars_to_tuple = List.fold_right (last_fun ~loc) vars vars_tuple in
  let gens = List.map (expr_of_typ always_nonempty quoter) tuple in
  gens, fn_vars_to_tuple

let fold_right_type_params fn params accum =
  List.fold_right (fun (param, _) accum ->
      match param with
      | { ptyp_desc = Ptyp_any; _ } -> accum
      | { ptyp_desc = Ptyp_var name; _ } ->
        let name = mkloc name param.ptyp_loc in
        fn name accum
      | _ -> assert false)
    params accum
let fold_right_type_decl fn { ptype_params; _ } accum =
  fold_right_type_params fn ptype_params accum

let poly_arrow_of_type_decl fn type_decl typ =
  fold_right_type_decl (fun name typ ->
    let name = name.txt in
    Typ.arrow Nolabel (fn (Typ.var name)) typ) type_decl typ

let poly_fun_of_type_decl type_decl expr =
  fold_right_type_decl (fun {txt=name; loc} expr ->
      Exp.fun_
        Nolabel
        None
        (Ast_builder.Default.pvar ~loc ("poly_"^name)) expr
    )
    type_decl
    expr

let core_type_of_decl type_decl =
  let typ = Ppxlib.core_type_of_type_declaration type_decl in
  let loc = type_decl.ptype_loc in
  poly_arrow_of_type_decl
    (fun var -> [%type: [%t var] Crowbar.gen])
    type_decl
    [%type: [%t typ] Crowbar.gen Lazy.t]

let str_of_type ~always_nonempty ({ptype_loc = loc; _ } as type_decl) =
  let quoter = Ppxlib.Quoter.create () in
  (* TODO: generalize this to "a list of things that have a type and attributes"
     rather than labels; we could use it more generally *)
  let gens_and_fn_of_labels ?name labels =
    let gens = labels |> List.map (fun {pld_type; _} ->
        match Attribute.get Attr.generator pld_type with
        | Some generator -> generator
        | None -> expr_of_typ always_nonempty quoter pld_type) in
    let vars = n_vars labels in
    let field_assignments = labels |> List.mapi (fun n {pld_name; _} ->
      let l = lid ~loc pld_name.txt in
      (l, Ast_helper.Exp.ident @@ lid ~loc @@ List.nth vars n))
    in
    let record = Ast_helper.Exp.record field_assignments None in
    let record = match name with
    | None -> record
    | Some name -> Ast_helper.Exp.construct name (Some record)
    in
    let fn_vars_to_record = List.fold_right (last_fun ~loc) vars record in
    (gens, fn_vars_to_record)
  in
  let generator =
    match Attribute.get Attr.generator_td type_decl with
    | Some generator -> generator
    | None ->
      match type_decl.ptype_kind, type_decl.ptype_manifest with
      | Ptype_open, _ -> raise_errorf "%s cannot be derived for open type" deriver (* TODO: can we do better? *)
      | Ptype_abstract, Some manifest ->
        expr_of_typ always_nonempty quoter manifest
      | Ptype_abstract, None ->
        (* we have a ptype_name foo, so try foo_to_crowbar in the namespace *)
        (Exp.ident (lid ~loc (mangle_type_decl type_decl)))
      | Ptype_record labels, _ -> (* parsetree.mli promises that this will be a
                                     non-empty list *)
        let (gens, fn_vars_to_record) = gens_and_fn_of_labels labels in
        [%expr Crowbar.(map [%e (make_crowbar_list ~loc gens)] [%e fn_vars_to_record])]
      | Ptype_variant constrs, _ ->
        let cases = constrs |>
                    List.map (fun ({pcd_name; pcd_res; pcd_args; pcd_loc; _} as pcd) ->
                        match Attribute.get Attr.generator_cd pcd with
                        | Some generator -> generator
                        | None ->
                          (* under what circumstances can pcd_res be non-None and pcd_args be
                             populated? *)
                          match pcd_res, pcd_args with
                          | None, Pcstr_tuple [] ->
                            let name =
                              Ast_builder.Default.pexp_construct
                                ~loc (lid ~loc pcd_name.txt) None
                            in
                            [%expr Crowbar.(const [%e name])]
                          | None, Pcstr_tuple tuple ->
                            let loc = pcd_loc in
                            let (gens, last_fun) = generate_tuple ~loc always_nonempty quoter
                                ~constructor:(
                                  Ast_helper.Exp.construct @@ lid ~loc pcd_name.txt)
                                tuple in
                            [%expr Crowbar.(map [%e (make_crowbar_list ~loc gens)] [%e last_fun])]
                          | Some core_type, Pcstr_tuple _ | Some core_type, Pcstr_record _ ->
                            (* C: T0  or C: T1 * ... * Tn -> T0 or C: {...} -> T0 *)
                            expr_of_typ always_nonempty quoter core_type
                          | None, Pcstr_record labels ->
                            (* C of {...} or C of {...} as t *)
                            let gens, fn_vars_to_record = gens_and_fn_of_labels
                                ~name:(lid ~loc pcd_name.txt) labels in
                            [%expr Crowbar.(map [%e (make_crowbar_list ~loc gens)] [%e fn_vars_to_record])]
                      ) in
        (* we must be sure that there are generators for all of the possible
           variant types, and then invoke Crowbar.choose on the list of them. *)
        [%expr Crowbar.choose [%e (make_crowbar_list ~loc cases)]]
  in
  let polymorphize = poly_fun_of_type_decl type_decl in
  let out_type =
    strong_type_of_type @@ core_type_of_decl type_decl in
  let generate_var = Ast_builder.Default.pvar ~loc (mangle_type_decl type_decl) in
  [Vb.mk (Pat.constraint_ generate_var out_type)
     (Ppxlib.Quoter.sanitize quoter (polymorphize (lazify loc generator)))
  ]

let tag_recursive_for_unlazifying type_decls =
  let add_tag core_type =
    let loc = core_type.ptyp_loc in
    let attrname = mkloc unlazify_attribute_name loc in
    let payload : Parsetree.payload =
      (PStr [(Ast_helper.Str.mk @@ Pstr_eval ([%expr "Crowbar.unlazy"], []))]) in
    let new_tag : Parsetree.attribute = Ast_helper.Attr.mk attrname payload in
    Ast_helper.Typ.attr core_type new_tag
  in
  let rec tag_on_match (needle : type_declaration) core_type =
    let core_type = match core_type.ptyp_desc with
      | Ptyp_constr (name, args) ->
        (* need to tag the top-level thing too, if it matches *)
        let core_type =
          let full_name l = Longident.flatten_exn l |> String.concat "." in
          if (0 = String.compare (full_name name.txt) needle.ptype_name.txt)
          then add_tag core_type
          else core_type
        in
        {core_type with ptyp_desc =
                        Ptyp_constr (name, List.map (tag_on_match needle) args)}
      | Ptyp_tuple l -> {core_type with ptyp_desc =
                        Ptyp_tuple (List.map (tag_on_match needle) l)}
      | Ptyp_variant (fields, openness, labels) ->
        let dig_desc = function
          | Rinherit _ as a -> a
          | Rtag (a, b, c) -> Rtag (a, b, List.map (tag_on_match needle) c)
        in
        let dig desc = { desc with prf_desc = dig_desc desc.prf_desc } in
        {core_type with ptyp_desc =
                          Ptyp_variant ((List.map dig fields), openness, labels)}

    | _ -> core_type
    in
    if (0 = String.compare (string_of_core_type core_type) needle.ptype_name.txt)
    then add_tag core_type
    else core_type
  in
  let descender needle type_decl =
    match type_decl.ptype_kind, type_decl.ptype_manifest with
    | Ptype_abstract, Some manifest ->
      {type_decl with ptype_manifest = Some (tag_on_match needle manifest) }
    | Ptype_abstract, None -> type_decl
    | Ptype_record labels, _ ->
      let check label = { label with pld_type = (tag_on_match needle label.pld_type)} in
      let labels = List.map check labels in
      {type_decl with ptype_kind = (Ptype_record labels)}
    | Ptype_variant constrs, _ ->
      let constrs = constrs |> List.map @@ fun constr ->
        match constr.pcd_res with
        | Some core_type -> {constr with pcd_res = Some (tag_on_match needle core_type)}
        | None -> match constr.pcd_args with
          | Pcstr_tuple tuple ->
            { constr with pcd_args = Pcstr_tuple (List.map (tag_on_match needle)
                                                    tuple) }
          | Pcstr_record labels ->
            let check label = { label with
                                pld_type = (tag_on_match needle label.pld_type)}
            in
            { constr with pcd_args = Pcstr_record (List.map check labels)}
      in
      {type_decl with ptype_kind = (Ptype_variant constrs)}
    | Ptype_open, _ -> type_decl (* TODO: I don't know what else we could do here *)
  in
  (* each top-level element in the list has to be fully considered with respect
     to both itself and other items *)
  List.fold_left (fun l needle -> List.map (descender needle) l) type_decls type_decls

let unlazify type_decl =
  let name = mangle_type_decl type_decl in
  let loc = type_decl.ptype_loc in
  let fn_name_ident = Exp.ident (lid ~loc name) in
  let args = fold_right_type_decl
      (fun str args ->
         (Asttypes.Nolabel,
          Exp.ident (lid ~loc ("poly_"^(str.txt))))::args)
      type_decl []
  in
  match args with
  | [] ->
    let lazy_name = Ast_helper.Pat.lazy_ (Ast_helper.Pat.var (mkloc name loc)) in
    Str.value Nonrecursive [Vb.mk lazy_name (Ast_builder.Default.evar ~loc name)]
  | args ->
    let apply_fn = Exp.apply fn_name_ident args in
    (* TODO: we assume Lazy has not been shadowed :/ *)
    let lazy_fn =
      [%expr Lazy.force [%e apply_fn]]
    in
    let polymorphize = poly_fun_of_type_decl type_decl in
    Str.value Nonrecursive [Vb.mk (Ast_builder.Default.pvar ~loc name) (polymorphize lazy_fn)]

let from_type_decl ~loc:_ ~path:_ (_rec_flag, type_decls) always_nonempty =
  let type_decls = tag_recursive_for_unlazifying type_decls in
  let bodies = List.concat (List.map (str_of_type ~always_nonempty) type_decls) in
  (Str.value Recursive bodies) :: (List.map unlazify type_decls)

let str_type_decl =
  Deriving.Generator.V2.make
    ~attributes:Attr.packed
    Ppxlib.Deriving.Args.(empty +> flag "nonempty")
    (Expansion_context.Deriver.with_loc_and_path from_type_decl)

let extension ~loc:_ ~path:_ typ =
  expr_of_typ false (Ppxlib.Quoter.create ()) typ
 
let deriver =
  Ppxlib.Deriving.add
    "crowbar"
    ~str_type_decl
    ~extension
