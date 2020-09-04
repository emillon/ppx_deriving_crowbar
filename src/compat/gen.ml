let () =
  let ocaml_version = Scanf.sscanf Sys.ocaml_version "%d.%d" (fun a b -> (a, b)) in
  if ocaml_version < (4, 8) then
    print_endline {|
      let attributes_as_assoc_list l = l

      let make_attribute name payload = (name, payload)

      type row_field_desc =
        | Rtag of Asttypes.label Location.loc * bool * Parsetree.core_type list
        | Rinherit of Parsetree.core_type

      let to_row_field_desc (x:Parsetree.row_field) : row_field_desc =
        match x with
        | Rtag (a, _, b, c) -> Rtag (a, b, c)
        | Rinherit t -> Rinherit t

      let map_row_field_core_type f = function
        | Parsetree.Rinherit t -> Parsetree.Rinherit t
        | Rtag (a, b, c, d) -> Rtag (a, b, c, f d)
    |}
  else
    print_endline {|
      let attributes_as_assoc_list =
        let open Parsetree in
        List.map (fun attr -> (attr.attr_name, attr.attr_payload))

        let make_attribute name payload = Ast_helper.Attr.mk name payload

        type row_field_desc = Parsetree.row_field_desc

        let to_row_field_desc x = x.Parsetree.prf_desc

        let map_row_field_desc_core_type f = function
          | Parsetree.Rinherit t -> Parsetree.Rinherit t
          | Rtag (a, b, c) -> Rtag (a, b, f c)

        let map_row_field_core_type f prf =
          let open Parsetree in
          { prf with prf_desc = map_row_field_desc_core_type f prf.prf_desc }
    |}
