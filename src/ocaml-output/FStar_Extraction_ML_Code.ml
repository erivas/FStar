open Prims
type assoc =
  | ILeft
  | IRight
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_ILeft: assoc -> Prims.bool =
  fun projectee  -> match projectee with | ILeft  -> true | uu____4 -> false
let uu___is_IRight: assoc -> Prims.bool =
  fun projectee  -> match projectee with | IRight  -> true | uu____8 -> false
let uu___is_Left: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____12 -> false
let uu___is_Right: assoc -> Prims.bool =
  fun projectee  -> match projectee with | Right  -> true | uu____16 -> false
let uu___is_NonAssoc: assoc -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____20 -> false
type fixity =
  | Prefix
  | Postfix
  | Infix of assoc[@@deriving show]
let uu___is_Prefix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Prefix  -> true | uu____28 -> false
let uu___is_Postfix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Postfix  -> true | uu____32 -> false
let uu___is_Infix: fixity -> Prims.bool =
  fun projectee  ->
    match projectee with | Infix _0 -> true | uu____37 -> false
let __proj__Infix__item___0: fixity -> assoc =
  fun projectee  -> match projectee with | Infix _0 -> _0
type opprec = (Prims.int,fixity) FStar_Pervasives_Native.tuple2[@@deriving
                                                                 show]
type level = (opprec,assoc) FStar_Pervasives_Native.tuple2[@@deriving show]
let t_prio_fun: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10"), (Infix Right))
let t_prio_tpl: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix NonAssoc))
let t_prio_name: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), Postfix)
let e_bin_prio_lambda: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "5"), Prefix)
let e_bin_prio_if: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "15"), Prefix)
let e_bin_prio_letin: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "19"), Prefix)
let e_bin_prio_or: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "20"), (Infix Left))
let e_bin_prio_and: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "25"), (Infix Left))
let e_bin_prio_eq: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "27"), (Infix NonAssoc))
let e_bin_prio_order: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "29"), (Infix NonAssoc))
let e_bin_prio_op1: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "30"), (Infix Left))
let e_bin_prio_op2: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "40"), (Infix Left))
let e_bin_prio_op3: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "50"), (Infix Left))
let e_bin_prio_op4: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "60"), (Infix Left))
let e_bin_prio_comb: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "70"), (Infix Left))
let e_bin_prio_seq: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "100"), (Infix Left))
let e_app_prio: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((Prims.parse_int "10000"), (Infix Left))
let min_op_prec: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  ((- (Prims.parse_int "1")), (Infix NonAssoc))
let max_op_prec: (Prims.int,fixity) FStar_Pervasives_Native.tuple2 =
  (FStar_Util.max_int, (Infix NonAssoc))
let rec in_ns:
  'a .
    ('a Prims.list,'a Prims.list) FStar_Pervasives_Native.tuple2 ->
      Prims.bool
  =
  fun x  ->
    match x with
    | ([],uu____153) -> true
    | (x1::t1,x2::t2) when x1 = x2 -> in_ns (t1, t2)
    | (uu____176,uu____177) -> false
let path_of_ns:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    Prims.string Prims.list -> Prims.string Prims.list
  =
  fun currentModule  ->
    fun ns  ->
      let ns' = FStar_Extraction_ML_Util.flatten_ns ns in
      if ns' = currentModule
      then []
      else
        (let cg_libs = FStar_Options.codegen_libs () in
         let ns_len = FStar_List.length ns in
         let found =
           FStar_Util.find_map cg_libs
             (fun cg_path  ->
                let cg_len = FStar_List.length cg_path in
                if (FStar_List.length cg_path) < ns_len
                then
                  let uu____235 = FStar_Util.first_N cg_len ns in
                  match uu____235 with
                  | (pfx,sfx) ->
                      (if pfx = cg_path
                       then
                         let uu____268 =
                           let uu____271 =
                             let uu____274 =
                               FStar_Extraction_ML_Util.flatten_ns sfx in
                             [uu____274] in
                           FStar_List.append pfx uu____271 in
                         FStar_Pervasives_Native.Some uu____268
                       else FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None) in
         match found with
         | FStar_Pervasives_Native.None  -> [ns']
         | FStar_Pervasives_Native.Some x -> x)
let mlpath_of_mlpath:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath
  =
  fun currentModule  ->
    fun x  ->
      let uu____298 = FStar_Extraction_ML_Syntax.string_of_mlpath x in
      match uu____298 with
      | "Prims.Some" -> ([], "Some")
      | "Prims.None" -> ([], "None")
      | uu____303 ->
          let uu____304 = x in
          (match uu____304 with
           | (ns,x1) ->
               let uu____311 = path_of_ns currentModule ns in (uu____311, x1))
let ptsym_of_symbol:
  FStar_Extraction_ML_Syntax.mlsymbol -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun s  ->
    let uu____319 =
      let uu____320 =
        let uu____322 = FStar_String.get s (Prims.parse_int "0") in
        FStar_Char.lowercase uu____322 in
      let uu____324 = FStar_String.get s (Prims.parse_int "0") in
      uu____320 <> uu____324 in
    if uu____319 then Prims.strcat "l__" s else s
let ptsym:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      if FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp)
      then ptsym_of_symbol (FStar_Pervasives_Native.snd mlp)
      else
        (let uu____339 = mlpath_of_mlpath currentModule mlp in
         match uu____339 with
         | (p,s) ->
             let uu____346 =
               let uu____349 =
                 let uu____352 = ptsym_of_symbol s in [uu____352] in
               FStar_List.append p uu____349 in
             FStar_String.concat "." uu____346)
let ptctor:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlsymbol
  =
  fun currentModule  ->
    fun mlp  ->
      let uu____359 = mlpath_of_mlpath currentModule mlp in
      match uu____359 with
      | (p,s) ->
          let s1 =
            let uu____367 =
              let uu____368 =
                let uu____370 = FStar_String.get s (Prims.parse_int "0") in
                FStar_Char.uppercase uu____370 in
              let uu____372 = FStar_String.get s (Prims.parse_int "0") in
              uu____368 <> uu____372 in
            if uu____367 then Prims.strcat "U__" s else s in
          FStar_String.concat "." (FStar_List.append p [s1])
let infix_prim_ops:
  (Prims.string,(Prims.int,fixity) FStar_Pervasives_Native.tuple2,Prims.string)
    FStar_Pervasives_Native.tuple3 Prims.list
  =
  [("op_Addition", e_bin_prio_op1, "+");
  ("op_Subtraction", e_bin_prio_op1, "-");
  ("op_Multiply", e_bin_prio_op1, "*");
  ("op_Division", e_bin_prio_op1, "/");
  ("op_Equality", e_bin_prio_eq, "=");
  ("op_Colon_Equals", e_bin_prio_eq, ":=");
  ("op_disEquality", e_bin_prio_eq, "<>");
  ("op_AmpAmp", e_bin_prio_and, "&&");
  ("op_BarBar", e_bin_prio_or, "||");
  ("op_LessThanOrEqual", e_bin_prio_order, "<=");
  ("op_GreaterThanOrEqual", e_bin_prio_order, ">=");
  ("op_LessThan", e_bin_prio_order, "<");
  ("op_GreaterThan", e_bin_prio_order, ">");
  ("op_Modulus", e_bin_prio_order, "mod")]
let prim_uni_ops:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____602  ->
    let op_minus =
      let uu____604 = FStar_Options.codegen_fsharp () in
      if uu____604 then "-" else "~-" in
    [("op_Negation", "not");
    ("op_Minus", op_minus);
    ("op_Bang", "Support.ST.read")]
let prim_types: 'Auu____623 . Prims.unit -> 'Auu____623 Prims.list =
  fun uu____626  -> []
let prim_constructors:
  (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list =
  [("Some", "Some"); ("None", "None"); ("Nil", "[]"); ("Cons", "::")]
let is_prims_ns: FStar_Extraction_ML_Syntax.mlsymbol Prims.list -> Prims.bool
  = fun ns  -> ns = ["Prims"]
let as_bin_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,(Prims.int,fixity)
                                           FStar_Pervasives_Native.tuple2,
      Prims.string) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option
  =
  fun uu____676  ->
    match uu____676 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____721  ->
               match uu____721 with | (y,uu____733,uu____734) -> x = y)
            infix_prim_ops
        else FStar_Pervasives_Native.None
let is_bin_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____757 = as_bin_op p in uu____757 <> FStar_Pervasives_Native.None
let as_uni_op:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____800  ->
    match uu____800 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          let uu____819 = prim_uni_ops () in
          FStar_List.tryFind
            (fun uu____833  -> match uu____833 with | (y,uu____839) -> x = y)
            uu____819
        else FStar_Pervasives_Native.None
let is_uni_op: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  ->
    let uu____848 = as_uni_op p in uu____848 <> FStar_Pervasives_Native.None
let is_standard_type: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool =
  fun p  -> false
let as_standard_constructor:
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Extraction_ML_Syntax.mlsymbol,Prims.string)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu____876  ->
    match uu____876 with
    | (ns,x) ->
        if is_prims_ns ns
        then
          FStar_List.tryFind
            (fun uu____902  -> match uu____902 with | (y,uu____908) -> x = y)
            prim_constructors
        else FStar_Pervasives_Native.None
let is_standard_constructor: FStar_Extraction_ML_Syntax.mlpath -> Prims.bool
  =
  fun p  ->
    let uu____917 = as_standard_constructor p in
    uu____917 <> FStar_Pervasives_Native.None
let maybe_paren:
  ((Prims.int,fixity) FStar_Pervasives_Native.tuple2,assoc)
    FStar_Pervasives_Native.tuple2 ->
    (Prims.int,fixity) FStar_Pervasives_Native.tuple2 ->
      FStar_Format.doc -> FStar_Format.doc
  =
  fun uu____952  ->
    fun inner  ->
      fun doc1  ->
        match uu____952 with
        | (outer,side) ->
            let noparens _inner _outer side1 =
              let uu____1003 = _inner in
              match uu____1003 with
              | (pi,fi) ->
                  let uu____1010 = _outer in
                  (match uu____1010 with
                   | (po,fo) ->
                       (pi > po) ||
                         ((match (fi, side1) with
                           | (Postfix ,Left ) -> true
                           | (Prefix ,Right ) -> true
                           | (Infix (Left ),Left ) ->
                               (pi = po) && (fo = (Infix Left))
                           | (Infix (Right ),Right ) ->
                               (pi = po) && (fo = (Infix Right))
                           | (Infix (Left ),ILeft ) ->
                               (pi = po) && (fo = (Infix Left))
                           | (Infix (Right ),IRight ) ->
                               (pi = po) && (fo = (Infix Right))
                           | (uu____1017,NonAssoc ) -> (pi = po) && (fi = fo)
                           | (uu____1018,uu____1019) -> false))) in
            if noparens inner outer side
            then doc1
            else FStar_Format.parens doc1
let escape_byte_hex: FStar_BaseTypes.byte -> Prims.string =
  fun x  -> Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)
let escape_char_hex: FStar_BaseTypes.char -> Prims.string =
  fun x  -> escape_byte_hex (FStar_Util.byte_of_char x)
let escape_or:
  (FStar_Char.char -> Prims.string) -> FStar_Char.char -> Prims.string =
  fun fallback  ->
    fun uu___180_1037  ->
      match uu___180_1037 with
      | c when c = 92 -> "\\\\"
      | c when c = 32 -> " "
      | c when c = 8 -> "\\b"
      | c when c = 9 -> "\\t"
      | c when c = 13 -> "\\r"
      | c when c = 10 -> "\\n"
      | c when c = 39 -> "\\'"
      | c when c = 34 -> "\\\""
      | c when FStar_Util.is_letter_or_digit c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_punctuation c -> FStar_Util.string_of_char c
      | c when FStar_Util.is_symbol c -> FStar_Util.string_of_char c
      | c -> fallback c
let string_of_mlconstant:
  FStar_Extraction_ML_Syntax.mlconstant -> Prims.string =
  fun sctt  ->
    match sctt with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> "()"
    | FStar_Extraction_ML_Syntax.MLC_Bool (true ) -> "true"
    | FStar_Extraction_ML_Syntax.MLC_Bool (false ) -> "false"
    | FStar_Extraction_ML_Syntax.MLC_Char c ->
        let nc = FStar_Char.int_of_char c in
        let uu____1087 = FStar_Util.string_of_int nc in
        Prims.strcat uu____1087
          (if
             ((nc >= (Prims.parse_int "32")) &&
                (nc <= (Prims.parse_int "127")))
               && (nc <> (Prims.parse_int "34"))
           then
             Prims.strcat " (*"
               (Prims.strcat (FStar_Util.string_of_char c) "*)")
           else "")
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int32 ))
        -> Prims.strcat s "l"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some
         (FStar_Const.Signed ,FStar_Const.Int64 ))
        -> Prims.strcat s "L"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1134,FStar_Const.Int8 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some (uu____1146,FStar_Const.Int16 )) -> s
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")")
    | FStar_Extraction_ML_Syntax.MLC_Float d -> FStar_Util.string_of_float d
    | FStar_Extraction_ML_Syntax.MLC_Bytes bytes ->
        let uu____1172 =
          let uu____1173 =
            FStar_Compiler_Bytes.f_encode escape_byte_hex bytes in
          Prims.strcat uu____1173 "\"" in
        Prims.strcat "\"" uu____1172
    | FStar_Extraction_ML_Syntax.MLC_String chars ->
        let uu____1175 =
          let uu____1176 =
            FStar_String.collect (escape_or FStar_Util.string_of_char) chars in
          Prims.strcat uu____1176 "\"" in
        Prims.strcat "\"" uu____1175
    | uu____1177 ->
        failwith "TODO: extract integer constants properly into OCaml"
let rec doc_of_mltype':
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        match ty with
        | FStar_Extraction_ML_Syntax.MLTY_Var x ->
            let escape_tyvar s =
              if FStar_Util.starts_with s "'_"
              then FStar_Util.replace_char s 95 117
              else s in
            FStar_Format.text (escape_tyvar x)
        | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
            let doc1 =
              FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left))
                tys in
            let doc2 =
              let uu____1212 =
                let uu____1213 =
                  FStar_Format.combine (FStar_Format.text " * ") doc1 in
                FStar_Format.hbox uu____1213 in
              FStar_Format.parens uu____1212 in
            doc2
        | FStar_Extraction_ML_Syntax.MLTY_Named (args,name) ->
            let args1 =
              match args with
              | [] -> FStar_Format.empty
              | arg::[] ->
                  doc_of_mltype currentModule (t_prio_name, Left) arg
              | uu____1226 ->
                  let args1 =
                    FStar_List.map
                      (doc_of_mltype currentModule (min_op_prec, NonAssoc))
                      args in
                  let uu____1236 =
                    let uu____1237 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.hbox uu____1237 in
                  FStar_Format.parens uu____1236 in
            let name1 = ptsym currentModule name in
            let uu____1239 =
              FStar_Format.reduce1 [args1; FStar_Format.text name1] in
            FStar_Format.hbox uu____1239
        | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____1241,t2) ->
            let d1 = doc_of_mltype currentModule (t_prio_fun, Left) t1 in
            let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
            let uu____1253 =
              let uu____1254 =
                FStar_Format.reduce1 [d1; FStar_Format.text " -> "; d2] in
              FStar_Format.hbox uu____1254 in
            maybe_paren outer t_prio_fun uu____1253
        | FStar_Extraction_ML_Syntax.MLTY_Top  ->
            let uu____1255 = FStar_Options.codegen_fsharp () in
            if uu____1255
            then FStar_Format.text "obj"
            else FStar_Format.text "Obj.t"
and doc_of_mltype:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlty -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun ty  ->
        let uu____1260 = FStar_Extraction_ML_Util.resugar_mlty ty in
        doc_of_mltype' currentModule outer uu____1260
let rec doc_of_expr:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    level -> FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun outer  ->
      fun e  ->
        match e.FStar_Extraction_ML_Syntax.expr with
        | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t,t') ->
            let doc1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let uu____1314 = FStar_Options.codegen_fsharp () in
            if uu____1314
            then
              let uu____1315 =
                FStar_Format.reduce
                  [FStar_Format.text "Prims.unsafe_coerce "; doc1] in
              FStar_Format.parens uu____1315
            else
              (let uu____1317 =
                 FStar_Format.reduce
                   [FStar_Format.text "Obj.magic "; FStar_Format.parens doc1] in
               FStar_Format.parens uu____1317)
        | FStar_Extraction_ML_Syntax.MLE_Seq es ->
            let docs =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
            let docs1 =
              FStar_List.map
                (fun d  ->
                   FStar_Format.reduce
                     [d; FStar_Format.text ";"; FStar_Format.hardline]) docs in
            let uu____1333 = FStar_Format.reduce docs1 in
            FStar_Format.parens uu____1333
        | FStar_Extraction_ML_Syntax.MLE_Const c ->
            let uu____1335 = string_of_mlconstant c in
            FStar_Format.text uu____1335
        | FStar_Extraction_ML_Syntax.MLE_Var x -> FStar_Format.text x
        | FStar_Extraction_ML_Syntax.MLE_Name path ->
            let uu____1338 = ptsym currentModule path in
            FStar_Format.text uu____1338
        | FStar_Extraction_ML_Syntax.MLE_Record (path,fields) ->
            let for1 uu____1364 =
              match uu____1364 with
              | (name,e1) ->
                  let doc1 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1376 =
                    let uu____1379 =
                      let uu____1380 = ptsym currentModule (path, name) in
                      FStar_Format.text uu____1380 in
                    [uu____1379; FStar_Format.text "="; doc1] in
                  FStar_Format.reduce1 uu____1376 in
            let uu____1383 =
              let uu____1384 = FStar_List.map for1 fields in
              FStar_Format.combine (FStar_Format.text "; ") uu____1384 in
            FStar_Format.cbrackets uu____1383
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,[]) ->
            let name =
              let uu____1395 = is_standard_constructor ctor in
              if uu____1395
              then
                let uu____1396 =
                  let uu____1401 = as_standard_constructor ctor in
                  FStar_Option.get uu____1401 in
                FStar_Pervasives_Native.snd uu____1396
              else ptctor currentModule ctor in
            FStar_Format.text name
        | FStar_Extraction_ML_Syntax.MLE_CTor (ctor,args) ->
            let name =
              let uu____1420 = is_standard_constructor ctor in
              if uu____1420
              then
                let uu____1421 =
                  let uu____1426 = as_standard_constructor ctor in
                  FStar_Option.get uu____1426 in
                FStar_Pervasives_Native.snd uu____1421
              else ptctor currentModule ctor in
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let doc1 =
              match (name, args1) with
              | ("::",x::xs::[]) ->
                  FStar_Format.reduce
                    [FStar_Format.parens x; FStar_Format.text "::"; xs]
              | (uu____1452,uu____1453) ->
                  let uu____1458 =
                    let uu____1461 =
                      let uu____1464 =
                        let uu____1465 =
                          FStar_Format.combine (FStar_Format.text ", ") args1 in
                        FStar_Format.parens uu____1465 in
                      [uu____1464] in
                    (FStar_Format.text name) :: uu____1461 in
                  FStar_Format.reduce1 uu____1458 in
            maybe_paren outer e_app_prio doc1
        | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
            let docs =
              FStar_List.map
                (fun x  ->
                   let uu____1475 =
                     doc_of_expr currentModule (min_op_prec, NonAssoc) x in
                   FStar_Format.parens uu____1475) es in
            let docs1 =
              let uu____1481 =
                FStar_Format.combine (FStar_Format.text ", ") docs in
              FStar_Format.parens uu____1481 in
            docs1
        | FStar_Extraction_ML_Syntax.MLE_Let ((rec_,uu____1483,lets),body) ->
            let pre =
              if
                e.FStar_Extraction_ML_Syntax.loc <>
                  FStar_Extraction_ML_Syntax.dummy_loc
              then
                let uu____1499 =
                  let uu____1502 =
                    let uu____1505 =
                      doc_of_loc e.FStar_Extraction_ML_Syntax.loc in
                    [uu____1505] in
                  FStar_Format.hardline :: uu____1502 in
                FStar_Format.reduce uu____1499
              else FStar_Format.empty in
            let doc1 = doc_of_lets currentModule (rec_, false, lets) in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let uu____1515 =
              let uu____1516 =
                let uu____1519 =
                  let uu____1522 =
                    let uu____1525 =
                      FStar_Format.reduce1 [FStar_Format.text "in"; body1] in
                    [uu____1525] in
                  doc1 :: uu____1522 in
                pre :: uu____1519 in
              FStar_Format.combine FStar_Format.hardline uu____1516 in
            FStar_Format.parens uu____1515
        | FStar_Extraction_ML_Syntax.MLE_App (e1,args) ->
            (match ((e1.FStar_Extraction_ML_Syntax.expr), args) with
             | (FStar_Extraction_ML_Syntax.MLE_Name
                p,{
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_Fun
                      (uu____1535::[],scrutinee);
                    FStar_Extraction_ML_Syntax.mlty = uu____1537;
                    FStar_Extraction_ML_Syntax.loc = uu____1538;_}::{
                                                                    FStar_Extraction_ML_Syntax.expr
                                                                    =
                                                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                                                    ((arg,uu____1540)::[],possible_match);
                                                                    FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____1542;
                                                                    FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____1543;_}::[])
                 when
                 let uu____1578 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____1578 = "FStar.All.try_with" ->
                 let branches =
                   match possible_match with
                   | {
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Match
                         ({
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Var arg';
                            FStar_Extraction_ML_Syntax.mlty = uu____1601;
                            FStar_Extraction_ML_Syntax.loc = uu____1602;_},branches);
                       FStar_Extraction_ML_Syntax.mlty = uu____1604;
                       FStar_Extraction_ML_Syntax.loc = uu____1605;_} when
                       arg = arg' -> branches
                   | e2 ->
                       [(FStar_Extraction_ML_Syntax.MLP_Wild,
                          FStar_Pervasives_Native.None, e2)] in
                 doc_of_expr currentModule outer
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       (FStar_Extraction_ML_Syntax.MLE_Try
                          (scrutinee, branches));
                     FStar_Extraction_ML_Syntax.mlty =
                       (possible_match.FStar_Extraction_ML_Syntax.mlty);
                     FStar_Extraction_ML_Syntax.loc =
                       (possible_match.FStar_Extraction_ML_Syntax.loc)
                   }
             | (FStar_Extraction_ML_Syntax.MLE_Name p,e11::e2::[]) when
                 is_bin_op p -> doc_of_binop currentModule p e11 e2
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu____1661;
                   FStar_Extraction_ML_Syntax.loc = uu____1662;_},unitVal::[]),e11::e2::[])
                 when
                 (is_bin_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_binop currentModule p e11 e2
             | (FStar_Extraction_ML_Syntax.MLE_Name p,e11::[]) when
                 is_uni_op p -> doc_of_uniop currentModule p e11
             | (FStar_Extraction_ML_Syntax.MLE_App
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.MLE_Name p;
                   FStar_Extraction_ML_Syntax.mlty = uu____1675;
                   FStar_Extraction_ML_Syntax.loc = uu____1676;_},unitVal::[]),e11::[])
                 when
                 (is_uni_op p) &&
                   (unitVal = FStar_Extraction_ML_Syntax.ml_unit)
                 -> doc_of_uniop currentModule p e11
             | uu____1683 ->
                 let e2 = doc_of_expr currentModule (e_app_prio, ILeft) e1 in
                 let args1 =
                   FStar_List.map
                     (doc_of_expr currentModule (e_app_prio, IRight)) args in
                 let uu____1702 = FStar_Format.reduce1 (e2 :: args1) in
                 FStar_Format.parens uu____1702)
        | FStar_Extraction_ML_Syntax.MLE_Proj (e1,f) ->
            let e2 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              let uu____1711 = FStar_Options.codegen_fsharp () in
              if uu____1711
              then
                FStar_Format.reduce
                  [e2;
                  FStar_Format.text ".";
                  FStar_Format.text (FStar_Pervasives_Native.snd f)]
              else
                (let uu____1715 =
                   let uu____1718 =
                     let uu____1721 =
                       let uu____1724 =
                         let uu____1725 = ptsym currentModule f in
                         FStar_Format.text uu____1725 in
                       [uu____1724] in
                     (FStar_Format.text ".") :: uu____1721 in
                   e2 :: uu____1718 in
                 FStar_Format.reduce uu____1715) in
            doc1
        | FStar_Extraction_ML_Syntax.MLE_Fun (ids,body) ->
            let bvar_annot x xt =
              let uu____1751 = FStar_Options.codegen_fsharp () in
              if uu____1751
              then
                let uu____1752 =
                  let uu____1755 =
                    let uu____1758 =
                      let uu____1761 =
                        match xt with
                        | FStar_Pervasives_Native.Some xxt ->
                            let uu____1763 =
                              let uu____1766 =
                                let uu____1769 =
                                  doc_of_mltype currentModule outer xxt in
                                [uu____1769] in
                              (FStar_Format.text " : ") :: uu____1766 in
                            FStar_Format.reduce1 uu____1763
                        | uu____1770 -> FStar_Format.text "" in
                      [uu____1761; FStar_Format.text ")"] in
                    (FStar_Format.text x) :: uu____1758 in
                  (FStar_Format.text "(") :: uu____1755 in
                FStar_Format.reduce1 uu____1752
              else FStar_Format.text x in
            let ids1 =
              FStar_List.map
                (fun uu____1784  ->
                   match uu____1784 with
                   | (x,xt) -> bvar_annot x (FStar_Pervasives_Native.Some xt))
                ids in
            let body1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) body in
            let doc1 =
              let uu____1797 =
                let uu____1800 =
                  let uu____1803 = FStar_Format.reduce1 ids1 in
                  [uu____1803; FStar_Format.text "->"; body1] in
                (FStar_Format.text "fun") :: uu____1800 in
              FStar_Format.reduce1 uu____1797 in
            FStar_Format.parens doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.None ) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1814 =
                let uu____1817 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1818 =
                  let uu____1821 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  [uu____1821; FStar_Format.text "end"] in
                uu____1817 :: uu____1818 in
              FStar_Format.combine FStar_Format.hardline uu____1814 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_If
            (cond,e1,FStar_Pervasives_Native.Some e2) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let doc1 =
              let uu____1837 =
                let uu____1840 =
                  FStar_Format.reduce1
                    [FStar_Format.text "if";
                    cond1;
                    FStar_Format.text "then";
                    FStar_Format.text "begin"] in
                let uu____1841 =
                  let uu____1844 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                  let uu____1849 =
                    let uu____1852 =
                      FStar_Format.reduce1
                        [FStar_Format.text "end";
                        FStar_Format.text "else";
                        FStar_Format.text "begin"] in
                    let uu____1853 =
                      let uu____1856 =
                        doc_of_expr currentModule (min_op_prec, NonAssoc) e2 in
                      [uu____1856; FStar_Format.text "end"] in
                    uu____1852 :: uu____1853 in
                  uu____1844 :: uu____1849 in
                uu____1840 :: uu____1841 in
              FStar_Format.combine FStar_Format.hardline uu____1837 in
            maybe_paren outer e_bin_prio_if doc1
        | FStar_Extraction_ML_Syntax.MLE_Match (cond,pats) ->
            let cond1 =
              doc_of_expr currentModule (min_op_prec, NonAssoc) cond in
            let pats1 = FStar_List.map (doc_of_branch currentModule) pats in
            let doc1 =
              let uu____1894 =
                FStar_Format.reduce1
                  [FStar_Format.text "match";
                  FStar_Format.parens cond1;
                  FStar_Format.text "with"] in
              uu____1894 :: pats1 in
            let doc2 = FStar_Format.combine FStar_Format.hardline doc1 in
            FStar_Format.parens doc2
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,[]) ->
            let uu____1899 =
              let uu____1902 =
                let uu____1905 =
                  let uu____1906 = ptctor currentModule exn in
                  FStar_Format.text uu____1906 in
                [uu____1905] in
              (FStar_Format.text "raise") :: uu____1902 in
            FStar_Format.reduce1 uu____1899
        | FStar_Extraction_ML_Syntax.MLE_Raise (exn,args) ->
            let args1 =
              FStar_List.map
                (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
            let uu____1920 =
              let uu____1923 =
                let uu____1926 =
                  let uu____1927 = ptctor currentModule exn in
                  FStar_Format.text uu____1927 in
                let uu____1928 =
                  let uu____1931 =
                    let uu____1932 =
                      FStar_Format.combine (FStar_Format.text ", ") args1 in
                    FStar_Format.parens uu____1932 in
                  [uu____1931] in
                uu____1926 :: uu____1928 in
              (FStar_Format.text "raise") :: uu____1923 in
            FStar_Format.reduce1 uu____1920
        | FStar_Extraction_ML_Syntax.MLE_Try (e1,pats) ->
            let uu____1955 =
              let uu____1958 =
                let uu____1961 =
                  doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
                let uu____1966 =
                  let uu____1969 =
                    let uu____1972 =
                      let uu____1973 =
                        FStar_List.map (doc_of_branch currentModule) pats in
                      FStar_Format.combine FStar_Format.hardline uu____1973 in
                    [uu____1972] in
                  (FStar_Format.text "with") :: uu____1969 in
                uu____1961 :: uu____1966 in
              (FStar_Format.text "try") :: uu____1958 in
            FStar_Format.combine FStar_Format.hardline uu____1955
        | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
            doc_of_expr currentModule outer head1
and doc_of_binop:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        fun e2  ->
          let uu____1986 =
            let uu____1997 = as_bin_op p in FStar_Option.get uu____1997 in
          match uu____1986 with
          | (uu____2020,prio,txt) ->
              let e11 = doc_of_expr currentModule (prio, Left) e1 in
              let e21 = doc_of_expr currentModule (prio, Right) e2 in
              let doc1 =
                FStar_Format.reduce1 [e11; FStar_Format.text txt; e21] in
              FStar_Format.parens doc1
and doc_of_uniop:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Format.doc
  =
  fun currentModule  ->
    fun p  ->
      fun e1  ->
        let uu____2045 =
          let uu____2050 = as_uni_op p in FStar_Option.get uu____2050 in
        match uu____2045 with
        | (uu____2061,txt) ->
            let e11 = doc_of_expr currentModule (min_op_prec, NonAssoc) e1 in
            let doc1 =
              FStar_Format.reduce1
                [FStar_Format.text txt; FStar_Format.parens e11] in
            FStar_Format.parens doc1
and doc_of_pattern:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlpattern -> FStar_Format.doc
  =
  fun currentModule  ->
    fun pattern  ->
      match pattern with
      | FStar_Extraction_ML_Syntax.MLP_Wild  -> FStar_Format.text "_"
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____2072 = string_of_mlconstant c in
          FStar_Format.text uu____2072
      | FStar_Extraction_ML_Syntax.MLP_Var x -> FStar_Format.text x
      | FStar_Extraction_ML_Syntax.MLP_Record (path,fields) ->
          let for1 uu____2099 =
            match uu____2099 with
            | (name,p) ->
                let uu____2106 =
                  let uu____2109 =
                    let uu____2110 = ptsym currentModule (path, name) in
                    FStar_Format.text uu____2110 in
                  let uu____2113 =
                    let uu____2116 =
                      let uu____2119 = doc_of_pattern currentModule p in
                      [uu____2119] in
                    (FStar_Format.text "=") :: uu____2116 in
                  uu____2109 :: uu____2113 in
                FStar_Format.reduce1 uu____2106 in
          let uu____2120 =
            let uu____2121 = FStar_List.map for1 fields in
            FStar_Format.combine (FStar_Format.text "; ") uu____2121 in
          FStar_Format.cbrackets uu____2120
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,[]) ->
          let name =
            let uu____2132 = is_standard_constructor ctor in
            if uu____2132
            then
              let uu____2133 =
                let uu____2138 = as_standard_constructor ctor in
                FStar_Option.get uu____2138 in
              FStar_Pervasives_Native.snd uu____2133
            else ptctor currentModule ctor in
          FStar_Format.text name
      | FStar_Extraction_ML_Syntax.MLP_CTor (ctor,pats) ->
          let name =
            let uu____2157 = is_standard_constructor ctor in
            if uu____2157
            then
              let uu____2158 =
                let uu____2163 = as_standard_constructor ctor in
                FStar_Option.get uu____2163 in
              FStar_Pervasives_Native.snd uu____2158
            else ptctor currentModule ctor in
          let doc1 =
            match (name, pats) with
            | ("::",x::xs::[]) ->
                let uu____2182 =
                  let uu____2185 =
                    let uu____2186 = doc_of_pattern currentModule x in
                    FStar_Format.parens uu____2186 in
                  let uu____2187 =
                    let uu____2190 =
                      let uu____2193 = doc_of_pattern currentModule xs in
                      [uu____2193] in
                    (FStar_Format.text "::") :: uu____2190 in
                  uu____2185 :: uu____2187 in
                FStar_Format.reduce uu____2182
            | (uu____2194,(FStar_Extraction_ML_Syntax.MLP_Tuple
               uu____2195)::[]) ->
                let uu____2200 =
                  let uu____2203 =
                    let uu____2206 =
                      let uu____2207 = FStar_List.hd pats in
                      doc_of_pattern currentModule uu____2207 in
                    [uu____2206] in
                  (FStar_Format.text name) :: uu____2203 in
                FStar_Format.reduce1 uu____2200
            | uu____2208 ->
                let uu____2215 =
                  let uu____2218 =
                    let uu____2221 =
                      let uu____2222 =
                        let uu____2223 =
                          FStar_List.map (doc_of_pattern currentModule) pats in
                        FStar_Format.combine (FStar_Format.text ", ")
                          uu____2223 in
                      FStar_Format.parens uu____2222 in
                    [uu____2221] in
                  (FStar_Format.text name) :: uu____2218 in
                FStar_Format.reduce1 uu____2215 in
          maybe_paren (min_op_prec, NonAssoc) e_app_prio doc1
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let uu____2236 = FStar_Format.combine (FStar_Format.text ", ") ps1 in
          FStar_Format.parens uu____2236
      | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
          let ps1 = FStar_List.map (doc_of_pattern currentModule) ps in
          let ps2 = FStar_List.map FStar_Format.parens ps1 in
          FStar_Format.combine (FStar_Format.text " | ") ps2
and doc_of_branch:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlbranch -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2247  ->
      match uu____2247 with
      | (p,cond,e) ->
          let case =
            match cond with
            | FStar_Pervasives_Native.None  ->
                let uu____2256 =
                  let uu____2259 =
                    let uu____2262 = doc_of_pattern currentModule p in
                    [uu____2262] in
                  (FStar_Format.text "|") :: uu____2259 in
                FStar_Format.reduce1 uu____2256
            | FStar_Pervasives_Native.Some c ->
                let c1 = doc_of_expr currentModule (min_op_prec, NonAssoc) c in
                let uu____2269 =
                  let uu____2272 =
                    let uu____2275 = doc_of_pattern currentModule p in
                    [uu____2275; FStar_Format.text "when"; c1] in
                  (FStar_Format.text "|") :: uu____2272 in
                FStar_Format.reduce1 uu____2269 in
          let uu____2276 =
            let uu____2279 =
              FStar_Format.reduce1
                [case; FStar_Format.text "->"; FStar_Format.text "begin"] in
            let uu____2280 =
              let uu____2283 =
                doc_of_expr currentModule (min_op_prec, NonAssoc) e in
              [uu____2283; FStar_Format.text "end"] in
            uu____2279 :: uu____2280 in
          FStar_Format.combine FStar_Format.hardline uu____2276
and doc_of_lets:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    (FStar_Extraction_ML_Syntax.mlletflavor,Prims.bool,FStar_Extraction_ML_Syntax.mllb
                                                         Prims.list)
      FStar_Pervasives_Native.tuple3 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun uu____2289  ->
      match uu____2289 with
      | (rec_,top_level,lets) ->
          let for1 uu____2308 =
            match uu____2308 with
            | { FStar_Extraction_ML_Syntax.mllb_name = name;
                FStar_Extraction_ML_Syntax.mllb_tysc = tys;
                FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2311;
                FStar_Extraction_ML_Syntax.mllb_def = e;
                FStar_Extraction_ML_Syntax.print_typ = pt;_} ->
                let e1 = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                let ids = [] in
                let ty_annot =
                  if Prims.op_Negation pt
                  then FStar_Format.text ""
                  else
                    (let uu____2326 =
                       (FStar_Options.codegen_fsharp ()) &&
                         ((rec_ = FStar_Extraction_ML_Syntax.Rec) ||
                            top_level) in
                     if uu____2326
                     then
                       match tys with
                       | FStar_Pervasives_Native.Some
                           (uu____2327::uu____2328,uu____2329) ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.None  ->
                           FStar_Format.text ""
                       | FStar_Pervasives_Native.Some ([],ty) ->
                           let ty1 =
                             doc_of_mltype currentModule
                               (min_op_prec, NonAssoc) ty in
                           FStar_Format.reduce1 [FStar_Format.text ":"; ty1]
                     else
                       if top_level
                       then
                         (match tys with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Format.text ""
                          | FStar_Pervasives_Native.Some ([],ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              FStar_Format.reduce1
                                [FStar_Format.text ":"; ty1]
                          | FStar_Pervasives_Native.Some (vs,ty) ->
                              let ty1 =
                                doc_of_mltype currentModule
                                  (min_op_prec, NonAssoc) ty in
                              let vars =
                                let uu____2381 =
                                  FStar_All.pipe_right vs
                                    (FStar_List.map
                                       (fun x  ->
                                          doc_of_mltype currentModule
                                            (min_op_prec, NonAssoc)
                                            (FStar_Extraction_ML_Syntax.MLTY_Var
                                               x))) in
                                FStar_All.pipe_right uu____2381
                                  FStar_Format.reduce1 in
                              FStar_Format.reduce1
                                [FStar_Format.text ":";
                                vars;
                                FStar_Format.text ".";
                                ty1])
                       else FStar_Format.text "") in
                let uu____2395 =
                  let uu____2398 =
                    let uu____2401 = FStar_Format.reduce1 ids in
                    [uu____2401; ty_annot; FStar_Format.text "="; e1] in
                  (FStar_Format.text name) :: uu____2398 in
                FStar_Format.reduce1 uu____2395 in
          let letdoc =
            if rec_ = FStar_Extraction_ML_Syntax.Rec
            then
              FStar_Format.reduce1
                [FStar_Format.text "let"; FStar_Format.text "rec"]
            else FStar_Format.text "let" in
          let lets1 = FStar_List.map for1 lets in
          let lets2 =
            FStar_List.mapi
              (fun i  ->
                 fun doc1  ->
                   FStar_Format.reduce1
                     [if i = (Prims.parse_int "0")
                      then letdoc
                      else FStar_Format.text "and";
                     doc1]) lets1 in
          FStar_Format.combine FStar_Format.hardline lets2
and doc_of_loc: FStar_Extraction_ML_Syntax.mlloc -> FStar_Format.doc =
  fun uu____2415  ->
    match uu____2415 with
    | (lineno,file) ->
        let uu____2418 =
          (FStar_Options.no_location_info ()) ||
            (FStar_Options.codegen_fsharp ()) in
        if uu____2418
        then FStar_Format.empty
        else
          (let file1 = FStar_Util.basename file in
           FStar_Format.reduce1
             [FStar_Format.text "#";
             FStar_Format.num lineno;
             FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))])
let doc_of_mltydecl:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mltydecl -> FStar_Format.doc
  =
  fun currentModule  ->
    fun decls  ->
      let for1 uu____2448 =
        match uu____2448 with
        | (uu____2467,x,mangle_opt,tparams,uu____2471,body) ->
            let x1 =
              match mangle_opt with
              | FStar_Pervasives_Native.None  -> x
              | FStar_Pervasives_Native.Some y -> y in
            let tparams1 =
              match tparams with
              | [] -> FStar_Format.empty
              | x2::[] -> FStar_Format.text x2
              | uu____2489 ->
                  let doc1 =
                    FStar_List.map (fun x2  -> FStar_Format.text x2) tparams in
                  let uu____2497 =
                    FStar_Format.combine (FStar_Format.text ", ") doc1 in
                  FStar_Format.parens uu____2497 in
            let forbody body1 =
              match body1 with
              | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
                  doc_of_mltype currentModule (min_op_prec, NonAssoc) ty
              | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                  let forfield uu____2521 =
                    match uu____2521 with
                    | (name,ty) ->
                        let name1 = FStar_Format.text name in
                        let ty1 =
                          doc_of_mltype currentModule (min_op_prec, NonAssoc)
                            ty in
                        FStar_Format.reduce1
                          [name1; FStar_Format.text ":"; ty1] in
                  let uu____2534 =
                    let uu____2535 = FStar_List.map forfield fields in
                    FStar_Format.combine (FStar_Format.text "; ") uu____2535 in
                  FStar_Format.cbrackets uu____2534
              | FStar_Extraction_ML_Syntax.MLTD_DType ctors ->
                  let forctor uu____2568 =
                    match uu____2568 with
                    | (name,tys) ->
                        let uu____2593 = FStar_List.split tys in
                        (match uu____2593 with
                         | (_names,tys1) ->
                             (match tys1 with
                              | [] -> FStar_Format.text name
                              | uu____2612 ->
                                  let tys2 =
                                    FStar_List.map
                                      (doc_of_mltype currentModule
                                         (t_prio_tpl, Left)) tys1 in
                                  let tys3 =
                                    FStar_Format.combine
                                      (FStar_Format.text " * ") tys2 in
                                  FStar_Format.reduce1
                                    [FStar_Format.text name;
                                    FStar_Format.text "of";
                                    tys3])) in
                  let ctors1 = FStar_List.map forctor ctors in
                  let ctors2 =
                    FStar_List.map
                      (fun d  ->
                         FStar_Format.reduce1 [FStar_Format.text "|"; d])
                      ctors1 in
                  FStar_Format.combine FStar_Format.hardline ctors2 in
            let doc1 =
              let uu____2642 =
                let uu____2645 =
                  let uu____2648 =
                    let uu____2649 = ptsym currentModule ([], x1) in
                    FStar_Format.text uu____2649 in
                  [uu____2648] in
                tparams1 :: uu____2645 in
              FStar_Format.reduce1 uu____2642 in
            (match body with
             | FStar_Pervasives_Native.None  -> doc1
             | FStar_Pervasives_Native.Some body1 ->
                 let body2 = forbody body1 in
                 let uu____2654 =
                   let uu____2657 =
                     FStar_Format.reduce1 [doc1; FStar_Format.text "="] in
                   [uu____2657; body2] in
                 FStar_Format.combine FStar_Format.hardline uu____2654) in
      let doc1 = FStar_List.map for1 decls in
      let doc2 =
        if (FStar_List.length doc1) > (Prims.parse_int "0")
        then
          let uu____2680 =
            let uu____2683 =
              let uu____2686 =
                FStar_Format.combine (FStar_Format.text " \n and ") doc1 in
              [uu____2686] in
            (FStar_Format.text "type") :: uu____2683 in
          FStar_Format.reduce1 uu____2680
        else FStar_Format.text "" in
      doc2
let rec doc_of_sig1:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      match s with
      | FStar_Extraction_ML_Syntax.MLS_Mod (x,subsig) ->
          let uu____2704 =
            let uu____2707 =
              FStar_Format.reduce1
                [FStar_Format.text "module";
                FStar_Format.text x;
                FStar_Format.text "="] in
            let uu____2708 =
              let uu____2711 = doc_of_sig currentModule subsig in
              let uu____2712 =
                let uu____2715 =
                  FStar_Format.reduce1 [FStar_Format.text "end"] in
                [uu____2715] in
              uu____2711 :: uu____2712 in
            uu____2707 :: uu____2708 in
          FStar_Format.combine FStar_Format.hardline uu____2704
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLS_Exn (x,args) ->
          let args1 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
          let args2 =
            let uu____2733 =
              FStar_Format.combine (FStar_Format.text " * ") args1 in
            FStar_Format.parens uu____2733 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args2]
      | FStar_Extraction_ML_Syntax.MLS_Val (x,(uu____2735,ty)) ->
          let ty1 = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
          FStar_Format.reduce1
            [FStar_Format.text "val";
            FStar_Format.text x;
            FStar_Format.text ": ";
            ty1]
      | FStar_Extraction_ML_Syntax.MLS_Ty decls ->
          doc_of_mltydecl currentModule decls
and doc_of_sig:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlsig -> FStar_Format.doc
  =
  fun currentModule  ->
    fun s  ->
      let docs = FStar_List.map (doc_of_sig1 currentModule) s in
      let docs1 =
        FStar_List.map
          (fun x  ->
             FStar_Format.reduce
               [x; FStar_Format.hardline; FStar_Format.hardline]) docs in
      FStar_Format.reduce docs1
let doc_of_mod1:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule1 -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      match m with
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,[]) ->
          FStar_Format.reduce1
            [FStar_Format.text "exception"; FStar_Format.text x]
      | FStar_Extraction_ML_Syntax.MLM_Exn (x,args) ->
          let args1 = FStar_List.map FStar_Pervasives_Native.snd args in
          let args2 =
            FStar_List.map
              (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args1 in
          let args3 =
            let uu____2803 =
              FStar_Format.combine (FStar_Format.text " * ") args2 in
            FStar_Format.parens uu____2803 in
          FStar_Format.reduce1
            [FStar_Format.text "exception";
            FStar_Format.text x;
            FStar_Format.text "of";
            args3]
      | FStar_Extraction_ML_Syntax.MLM_Ty decls ->
          doc_of_mltydecl currentModule decls
      | FStar_Extraction_ML_Syntax.MLM_Let (rec_,uu____2806,lets) ->
          doc_of_lets currentModule (rec_, true, lets)
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu____2815 =
            let uu____2818 =
              let uu____2821 =
                let uu____2824 =
                  let uu____2827 =
                    doc_of_expr currentModule (min_op_prec, NonAssoc) e in
                  [uu____2827] in
                (FStar_Format.text "=") :: uu____2824 in
              (FStar_Format.text "_") :: uu____2821 in
            (FStar_Format.text "let") :: uu____2818 in
          FStar_Format.reduce1 uu____2815
      | FStar_Extraction_ML_Syntax.MLM_Loc loc -> doc_of_loc loc
let doc_of_mod:
  FStar_Extraction_ML_Syntax.mlsymbol ->
    FStar_Extraction_ML_Syntax.mlmodule -> FStar_Format.doc
  =
  fun currentModule  ->
    fun m  ->
      let docs =
        FStar_List.map
          (fun x  ->
             let doc1 = doc_of_mod1 currentModule x in
             [doc1;
             (match x with
              | FStar_Extraction_ML_Syntax.MLM_Loc uu____2851 ->
                  FStar_Format.empty
              | uu____2852 -> FStar_Format.hardline);
             FStar_Format.hardline]) m in
      FStar_Format.reduce (FStar_List.flatten docs)
let rec doc_of_mllib_r:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2861  ->
    match uu____2861 with
    | FStar_Extraction_ML_Syntax.MLLib mllib ->
        let rec for1_sig uu____2927 =
          match uu____2927 with
          | (x,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let x1 = FStar_Extraction_ML_Util.flatten_mlpath x in
              let head1 =
                FStar_Format.reduce1
                  [FStar_Format.text "module";
                  FStar_Format.text x1;
                  FStar_Format.text ":";
                  FStar_Format.text "sig"] in
              let tail1 = FStar_Format.reduce1 [FStar_Format.text "end"] in
              let doc1 =
                FStar_Option.map
                  (fun uu____3000  ->
                     match uu____3000 with
                     | (s,uu____3006) -> doc_of_sig x1 s) sigmod in
              let sub2 = FStar_List.map for1_sig sub1 in
              let sub3 =
                FStar_List.map
                  (fun x2  ->
                     FStar_Format.reduce
                       [x2; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let uu____3033 =
                let uu____3036 =
                  let uu____3039 =
                    let uu____3042 = FStar_Format.reduce sub3 in
                    [uu____3042;
                    FStar_Format.cat tail1 FStar_Format.hardline] in
                  (match doc1 with
                   | FStar_Pervasives_Native.None  -> FStar_Format.empty
                   | FStar_Pervasives_Native.Some s ->
                       FStar_Format.cat s FStar_Format.hardline)
                    :: uu____3039 in
                (FStar_Format.cat head1 FStar_Format.hardline) :: uu____3036 in
              FStar_Format.reduce uu____3033
        and for1_mod istop uu____3045 =
          match uu____3045 with
          | (mod_name1,sigmod,FStar_Extraction_ML_Syntax.MLLib sub1) ->
              let target_mod_name =
                FStar_Extraction_ML_Util.flatten_mlpath mod_name1 in
              let maybe_open_pervasives =
                match mod_name1 with
                | ("FStar"::[],"Pervasives") -> []
                | uu____3113 ->
                    let pervasives1 =
                      FStar_Extraction_ML_Util.flatten_mlpath
                        (["FStar"], "Pervasives") in
                    [FStar_Format.hardline;
                    FStar_Format.text (Prims.strcat "open " pervasives1)] in
              let head1 =
                let uu____3124 =
                  let uu____3127 = FStar_Options.codegen_fsharp () in
                  if uu____3127
                  then
                    [FStar_Format.text "module";
                    FStar_Format.text target_mod_name]
                  else
                    if Prims.op_Negation istop
                    then
                      [FStar_Format.text "module";
                      FStar_Format.text target_mod_name;
                      FStar_Format.text "=";
                      FStar_Format.text "struct"]
                    else [] in
                FStar_Format.reduce1 uu____3124 in
              let tail1 =
                if Prims.op_Negation istop
                then FStar_Format.reduce1 [FStar_Format.text "end"]
                else FStar_Format.reduce1 [] in
              let doc1 =
                FStar_Option.map
                  (fun uu____3146  ->
                     match uu____3146 with
                     | (uu____3151,m) -> doc_of_mod target_mod_name m) sigmod in
              let sub2 = FStar_List.map (for1_mod false) sub1 in
              let sub3 =
                FStar_List.map
                  (fun x  ->
                     FStar_Format.reduce
                       [x; FStar_Format.hardline; FStar_Format.hardline])
                  sub2 in
              let prefix1 =
                let uu____3182 = FStar_Options.codegen_fsharp () in
                if uu____3182
                then
                  [FStar_Format.cat (FStar_Format.text "#light \"off\"")
                     FStar_Format.hardline]
                else [] in
              let uu____3186 =
                let uu____3189 =
                  let uu____3192 =
                    let uu____3195 =
                      let uu____3198 =
                        let uu____3201 =
                          let uu____3204 = FStar_Format.reduce sub3 in
                          [uu____3204;
                          FStar_Format.cat tail1 FStar_Format.hardline] in
                        (match doc1 with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Format.empty
                         | FStar_Pervasives_Native.Some s ->
                             FStar_Format.cat s FStar_Format.hardline)
                          :: uu____3201 in
                      FStar_Format.hardline :: uu____3198 in
                    FStar_List.append maybe_open_pervasives uu____3195 in
                  FStar_List.append
                    [head1;
                    FStar_Format.hardline;
                    FStar_Format.text "open Prims"] uu____3192 in
                FStar_List.append prefix1 uu____3189 in
              FStar_All.pipe_left FStar_Format.reduce uu____3186 in
        let docs =
          FStar_List.map
            (fun uu____3243  ->
               match uu____3243 with
               | (x,s,m) ->
                   let uu____3293 = FStar_Extraction_ML_Util.flatten_mlpath x in
                   let uu____3294 = for1_mod true (x, s, m) in
                   (uu____3293, uu____3294)) mllib in
        docs
let doc_of_mllib:
  FStar_Extraction_ML_Syntax.mllib ->
    (Prims.string,FStar_Format.doc) FStar_Pervasives_Native.tuple2 Prims.list
  = fun mllib  -> doc_of_mllib_r mllib
let string_of_mlexpr:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlexpr -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3323 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_expr uu____3323 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1
let string_of_mlty:
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.string
  =
  fun cmod  ->
    fun e  ->
      let doc1 =
        let uu____3335 = FStar_Extraction_ML_Util.flatten_mlpath cmod in
        doc_of_mltype uu____3335 (min_op_prec, NonAssoc) e in
      FStar_Format.pretty (Prims.parse_int "0") doc1