open Var0
open Prog
open Word
module T = Type
module C = Expr

let rec pos_of_bi bi =
  let open B.Notations in
  if bi <=^ B.one then BinNums.Coq_xH
  else
    let p = pos_of_bi (B.rshift bi 1) in
    if (B.erem bi (B.of_int 2)) =^ B.one
    then BinNums.Coq_xI p
    else BinNums.Coq_xO p

let rec bi_of_pos pos =
  let open B.Notations in
  match pos with
  | BinNums.Coq_xH   -> B.one
  | BinNums.Coq_xO p -> B.lshift (bi_of_pos p) 1
  | BinNums.Coq_xI p -> B.lshift (bi_of_pos p) 1 +^ B.one

let z_of_bi bi =
  let open B.Notations in
  if bi =^ B.zero then BinNums.Z0
  else if bi <^ B.zero then BinNums.Zneg (pos_of_bi (B.abs bi))
  else BinNums.Zpos (pos_of_bi bi)

let bi_of_z z =
  match z with
  | BinNums.Zneg p -> B.neg (bi_of_pos p)
  | BinNums.Z0     -> B.zero
  | BinNums.Zpos p -> bi_of_pos p

let z_of_int i = z_of_bi (B.of_int i)

let bi_of_nat n =
  bi_of_z (BinInt.Z.of_nat n)

let pos_of_int i = pos_of_bi (B.of_int i)
let int_of_pos p = B.to_int (bi_of_pos p)

let int64_of_bi bi = I64.repr (z_of_bi bi)
let bi_of_int64 z  = bi_of_z (I64.signed z)

(* ------------------------------------------------------------------------ *)

let string0_of_string s =
  let s0 = ref [] in
  for i = String.length s - 1 downto 0 do
    s0 := s.[i] :: !s0
  done;
  (Obj.magic !s0)

let string_of_string0 s0 =
  let s0 = Obj.magic s0 in
  let s0 = Array.of_list s0 in
  let sz = Array.length s0 in
  String.init sz (fun i -> s0.(i))

(* ------------------------------------------------------------------------ *)

let cty_of_ty = function
  | Bty Bool      -> T.Coq_sbool
  | Bty Int       -> T.Coq_sint
  | Bty (U W64)   -> T.Coq_sword
  | Arr (W64, sz) -> T.Coq_sarr (pos_of_int sz)
  | _ -> assert false

let ty_of_cty = function
  | T.Coq_sbool  ->  Bty Bool
  | T.Coq_sint   ->  Bty Int
  | T.Coq_sword  ->  Bty (U W64)
  | T.Coq_sarr p ->  Arr (W64, (int_of_pos p))

(* ------------------------------------------------------------------------ *)

type 'info coq_tbl = {
     dft_info      : 'info;
     mutable count : int;
     var           : (Var.var, var) Hashtbl.t;
     cvar          : Var.var Hv.t;
     vari          : (int, L.t) Hashtbl.t;
     iinfo         : (int, L.t * 'info) Hashtbl.t;
     funname       : (funname, BinNums.positive) Hashtbl.t;
     cfunname      : (BinNums.positive, funname) Hashtbl.t;
     finfo         : (int, L.t * call_conv) Hashtbl.t;
  }

let new_count tbl =
  let n = tbl.count in
  tbl.count <- n + 1;
  n

let empty_tbl info = {
    dft_info = info;
    count    = 1;
    var      = Hashtbl.create 101;
    cvar     = Hv.create 101;
    vari     = Hashtbl.create 1000;
    iinfo    = Hashtbl.create 1000;
    funname  = Hashtbl.create 101;
    cfunname = Hashtbl.create 101;
    finfo    = Hashtbl.create 101;
  }

(* ------------------------------------------------------------------------ *)

let gen_cvar_of_var with_uid tbl v =
  try Hv.find tbl.cvar v
  with Not_found ->
    let s =
      if with_uid then
        v.v_name ^ "." ^ (string_of_int (int_of_uid v.v_id))
      else v.v_name in
    let cv = {
      Var.vtype = cty_of_ty v.v_ty;
      Var.vname = string0_of_string s
    } in
    Hv.add tbl.cvar v cv;
    assert (not (Hashtbl.mem tbl.var cv));
    Hashtbl.add tbl.var cv v;
    cv

let cvar_of_var tbl v = gen_cvar_of_var true tbl v
let cvar_of_reg tbl v = gen_cvar_of_var false tbl v

let var_of_cvar tbl cv =
  try Hashtbl.find tbl.var cv
  with Not_found -> assert false

let fresh_cvar tbl n ty =
  let v = V.mk n Reg ty L._dummy in
  cvar_of_var tbl v

(* ------------------------------------------------------------------------ *)

let get_loc tbl p =
  try Hashtbl.find tbl.vari (int_of_pos p)
  with Not_found -> L._dummy

let set_loc tbl loc =
  let n = new_count tbl in
  Hashtbl.add tbl.vari n loc;
  pos_of_int n

let cvari_of_vari tbl v =
  let p = set_loc tbl (L.loc v) in
  let cv = cvar_of_var tbl (L.unloc v) in
  { C.v_var = cv; C.v_info = p }

let vari_of_cvari tbl v =
  let loc =  get_loc tbl v.C.v_info in
  L.mk_loc loc (var_of_cvar tbl v.C.v_var)

(* ------------------------------------------------------------------------ *)

let cwsize_of_wsize = function
  | W8  -> Word.U8
  | W16 -> Word.U16
  | W32 -> Word.U32
  | W64 -> Word.U64
  | W128 -> assert false 
  | W256 -> assert false 

let wsize_of_cwsize = function
  | Word.U8  -> W8  
  | Word.U16 -> W16 
  | Word.U32 -> W32 
  | Word.U64 -> W64 

let ccmp_of_cmp = function
  | Cmp_int   -> C.Cmp_int
  | Cmp_uw ws -> C.Cmp_uw (cwsize_of_wsize ws) 
  | Cmp_sw ws -> C.Cmp_sw (cwsize_of_wsize ws)

let cmp_of_ccmp = function
  | C.Cmp_int    -> Cmp_int
  | C.Cmp_uw  ws -> Cmp_uw (wsize_of_cwsize ws)
  | C.Cmp_sw  ws -> Cmp_sw (wsize_of_cwsize ws)

let coty_of_oty = function
  | Op_int   -> C.Op_int
  | Op_w ws  -> C.Op_w (cwsize_of_wsize ws)

let oty_of_coty = function
  | C.Op_int  -> Op_int
  | C.Op_w ws -> Op_w (wsize_of_cwsize ws)

let cop_of_op = function
  | Oand    -> C.Oand
  | Oor     -> C.Oor

  | Oadd ty -> C.Oadd (coty_of_oty ty)
  | Omul ty -> C.Omul (coty_of_oty ty)
  | Osub ty -> C.Osub (coty_of_oty ty)

  | Oland ty -> C.Oland (cwsize_of_wsize ty)
  | Olor  ty -> C.Olor  (cwsize_of_wsize ty)
  | Olxor ty -> C.Olxor (cwsize_of_wsize ty)
  | Olsr  ty -> C.Olsr  (cwsize_of_wsize ty)
  | Olsl  ty -> C.Olsl  (cwsize_of_wsize ty)
  | Oasr  ty -> C.Oasr  (cwsize_of_wsize ty)

  | Oeq  ty -> C.Oeq  (ccmp_of_cmp ty)
  | Oneq ty -> C.Oneq (ccmp_of_cmp ty)
  | Olt  ty -> C.Olt  (ccmp_of_cmp ty)
  | Ole  ty -> C.Ole  (ccmp_of_cmp ty)
  | Ogt  ty -> C.Ogt  (ccmp_of_cmp ty)
  | Oge  ty -> C.Oge  (ccmp_of_cmp ty)

let op_of_cop = function
  | C.Oand    -> Oand
  | C.Oor     -> Oor
  | C.Oadd ty -> Oadd (oty_of_coty ty)
  | C.Omul ty -> Omul (oty_of_coty ty)
  | C.Osub ty -> Osub (oty_of_coty ty)

  | C.Oland ty  -> Oland (wsize_of_cwsize ty)
  | C.Olor  ty  -> Olor  (wsize_of_cwsize ty)
  | C.Olxor ty  -> Olxor (wsize_of_cwsize ty)
  | C.Olsr  ty  -> Olsr  (wsize_of_cwsize ty)
  | C.Olsl  ty  -> Olsl  (wsize_of_cwsize ty)
  | C.Oasr  ty  -> Oasr  (wsize_of_cwsize ty)

  | C.Oeq  ty -> Oeq  (cmp_of_ccmp ty)
  | C.Oneq ty -> Oneq (cmp_of_ccmp ty)
  | C.Olt  ty -> Olt  (cmp_of_ccmp ty)
  | C.Ole  ty -> Ole  (cmp_of_ccmp ty)
  | C.Ogt  ty -> Ogt  (cmp_of_ccmp ty)
  | C.Oge  ty -> Oge  (cmp_of_ccmp ty)

let op1_of_cop1 = function
  | C.Olnot ty -> Olnot (wsize_of_cwsize ty)
  | C.Onot     -> Onot
  | C.Oneg  ty -> Oneg (wsize_of_cwsize ty)

let cop1_of_op1 = function
  | Olnot ty -> C.Olnot (cwsize_of_wsize ty)
  | Onot     -> C.Onot
  | Oneg  ty -> C.Oneg (cwsize_of_wsize ty)

(* ------------------------------------------------------------------------ *)

let rec cexpr_of_expr tbl = function
  | Pconst z          -> C.Pconst (z_of_bi z)
  | Pbool  b          -> C.Pbool  b
  | Pcast (ty, e)     -> C.Pcast (cwsize_of_wsize ty, cexpr_of_expr tbl e)
  | Pvar x            -> C.Pvar (cvari_of_vari tbl x)
  | Pget (x,e)        -> C.Pget (cvari_of_vari tbl x, cexpr_of_expr tbl e)
  | Pload (ty, x, e)  -> C.Pload(cwsize_of_wsize ty, cvari_of_vari tbl x, cexpr_of_expr tbl e)
  | Papp1 (o, e)      -> C.Papp1(cop1_of_op1 o, cexpr_of_expr tbl e)
  | Papp2 (o, e1, e2) -> C.Papp2(cop_of_op o, cexpr_of_expr tbl e1, cexpr_of_expr tbl e2)
  | Pif   (e, e1, e2)  -> C.Pif(cexpr_of_expr tbl e,
                                cexpr_of_expr tbl e1,
                                cexpr_of_expr tbl e2)

let rec expr_of_cexpr tbl = function
  | C.Pconst z          -> Pconst (bi_of_z z)
  | C.Pbool  b          -> Pbool  b
  | C.Pcast (ty, e)     -> Pcast (wsize_of_cwsize ty, expr_of_cexpr tbl e)
  | C.Pvar x            -> Pvar (vari_of_cvari tbl x)
  | C.Pget  (x,e)       -> Pget (vari_of_cvari tbl x, expr_of_cexpr tbl e)
  | C.Pload (ty, x, e)  -> Pload(wsize_of_cwsize ty, vari_of_cvari tbl x, expr_of_cexpr tbl e)
  | C.Papp1 (o, e)      -> Papp1(op1_of_cop1 o, expr_of_cexpr tbl e)
  | C.Papp2 (o, e1, e2) -> Papp2(op_of_cop o, expr_of_cexpr tbl e1, expr_of_cexpr tbl e2)
  | C.Pif   (e, e1, e2) -> Pif(expr_of_cexpr tbl e,
                               expr_of_cexpr tbl e1,
                               expr_of_cexpr tbl e2)


(* ------------------------------------------------------------------------ *)

let copn_of_opn (o, ws) = 
  match o with 
  | Omulu        -> C.Omulu       (cwsize_of_wsize ws)  
  | Omuls        -> C.Omuls       (cwsize_of_wsize ws)  
  | Oaddcarry    -> C.Oaddcarry   (cwsize_of_wsize ws)
  | Osubcarry    -> C.Osubcarry   (cwsize_of_wsize ws)
  | Ox86_MOV     -> C.Ox86_MOV    (cwsize_of_wsize ws)
  | Ox86_CMOVcc  -> C.Ox86_CMOVcc (cwsize_of_wsize ws)
  | Ox86_ADD     -> C.Ox86_ADD    (cwsize_of_wsize ws)
  | Ox86_SUB     -> C.Ox86_SUB    (cwsize_of_wsize ws)
  | Ox86_MUL     -> C.Ox86_MUL    (cwsize_of_wsize ws)
  | Ox86_IMUL    -> C.Ox86_IMUL   (cwsize_of_wsize ws)
  | Ox86_IMUL64	 -> C.Ox86_IMUL64 (cwsize_of_wsize ws)
  | Ox86_DIV     -> C.Ox86_DIV    (cwsize_of_wsize ws)
  | Ox86_IDIV    -> C.Ox86_IDIV   (cwsize_of_wsize ws)
  | Ox86_ADC     -> C.Ox86_ADC    (cwsize_of_wsize ws)
  | Ox86_SBB     -> C.Ox86_SBB    (cwsize_of_wsize ws)
  | Ox86_NEG	 -> C.Ox86_NEG    (cwsize_of_wsize ws)
  | Ox86_INC     -> C.Ox86_INC    (cwsize_of_wsize ws)
  | Ox86_DEC     -> C.Ox86_DEC    (cwsize_of_wsize ws)
  | Ox86_SETcc   -> C.Ox86_SETcc  (cwsize_of_wsize ws)
  | Ox86_LEA     -> C.Ox86_LEA    (cwsize_of_wsize ws)
  | Ox86_TEST    -> C.Ox86_TEST   (cwsize_of_wsize ws)
  | Ox86_CMP     -> C.Ox86_CMP    (cwsize_of_wsize ws)
  | Ox86_AND     -> C.Ox86_AND    (cwsize_of_wsize ws)
  | Ox86_OR      -> C.Ox86_OR     (cwsize_of_wsize ws)
  | Ox86_XOR     -> C.Ox86_XOR    (cwsize_of_wsize ws)
  | Ox86_NOT     -> C.Ox86_NOT    (cwsize_of_wsize ws)
  | Ox86_SHL     -> C.Ox86_SHL    (cwsize_of_wsize ws)
  | Ox86_SHR     -> C.Ox86_SHR    (cwsize_of_wsize ws)
  | Ox86_SAR     -> C.Ox86_SAR    (cwsize_of_wsize ws)
  | Ox86_RCL     -> C.Ox86_RCL    (cwsize_of_wsize ws)
  | Ox86_RCR     -> C.Ox86_RCR    (cwsize_of_wsize ws)
  | Ox86_ROL     -> C.Ox86_ROL    (cwsize_of_wsize ws)
  | Ox86_ROR     -> C.Ox86_ROR    (cwsize_of_wsize ws)
  | Ox86_RORX    -> C.Ox86_RORX   (cwsize_of_wsize ws)

let opn_of_copn = function
  | C.Omuls       ws -> Omuls      , (wsize_of_cwsize ws)
  | C.Omulu       ws -> Omulu      , (wsize_of_cwsize ws)
  | C.Oaddcarry   ws -> Oaddcarry  , (wsize_of_cwsize ws)
  | C.Osubcarry   ws -> Osubcarry  , (wsize_of_cwsize ws)
  | C.Ox86_MOV    ws -> Ox86_MOV   , (wsize_of_cwsize ws)
  | C.Ox86_CMOVcc ws -> Ox86_CMOVcc, (wsize_of_cwsize ws)
  | C.Ox86_ADD    ws -> Ox86_ADD   , (wsize_of_cwsize ws)
  | C.Ox86_SUB    ws -> Ox86_SUB   , (wsize_of_cwsize ws)
  | C.Ox86_MUL    ws -> Ox86_MUL   , (wsize_of_cwsize ws)
  | C.Ox86_IMUL   ws -> Ox86_IMUL  , (wsize_of_cwsize ws)
  | C.Ox86_IMUL64 ws -> Ox86_IMUL64, (wsize_of_cwsize ws)
  | C.Ox86_DIV    ws -> Ox86_DIV   , (wsize_of_cwsize ws)
  | C.Ox86_IDIV   ws -> Ox86_IDIV  , (wsize_of_cwsize ws)
  | C.Ox86_ADC    ws -> Ox86_ADC   , (wsize_of_cwsize ws)
  | C.Ox86_SBB    ws -> Ox86_SBB   , (wsize_of_cwsize ws)
  | C.Ox86_NEG	  ws -> Ox86_NEG   , (wsize_of_cwsize ws)
  | C.Ox86_INC    ws -> Ox86_INC   , (wsize_of_cwsize ws)
  | C.Ox86_DEC    ws -> Ox86_DEC   , (wsize_of_cwsize ws)
  | C.Ox86_SETcc  ws -> Ox86_SETcc , (wsize_of_cwsize ws)
  | C.Ox86_LEA    ws -> Ox86_LEA   , (wsize_of_cwsize ws)
  | C.Ox86_TEST   ws -> Ox86_TEST  , (wsize_of_cwsize ws)
  | C.Ox86_CMP    ws -> Ox86_CMP   , (wsize_of_cwsize ws)
  | C.Ox86_AND    ws -> Ox86_AND   , (wsize_of_cwsize ws)
  | C.Ox86_OR     ws -> Ox86_OR    , (wsize_of_cwsize ws)
  | C.Ox86_XOR    ws -> Ox86_XOR   , (wsize_of_cwsize ws)
  | C.Ox86_NOT    ws -> Ox86_NOT   , (wsize_of_cwsize ws)
  | C.Ox86_SHL    ws -> Ox86_SHL   , (wsize_of_cwsize ws)
  | C.Ox86_SHR    ws -> Ox86_SHR   , (wsize_of_cwsize ws)
  | C.Ox86_SAR    ws -> Ox86_SAR   , (wsize_of_cwsize ws)
  | C.Ox86_RCL    ws -> Ox86_RCL   , (wsize_of_cwsize ws)
  | C.Ox86_RCR    ws -> Ox86_RCR   , (wsize_of_cwsize ws)
  | C.Ox86_ROL    ws -> Ox86_ROL   , (wsize_of_cwsize ws)
  | C.Ox86_ROR    ws -> Ox86_ROR   , (wsize_of_cwsize ws)
  | C.Ox86_RORX   ws -> Ox86_RORX  , (wsize_of_cwsize ws)

(* ------------------------------------------------------------------------ *)

let clval_of_lval tbl = function
  | Lnone(loc, ty) -> C.Lnone (set_loc tbl loc, cty_of_ty ty)
  | Lvar x         -> C.Lvar  (cvari_of_vari tbl x)
  | Lmem (ty,x,e)  -> C.Lmem  (cwsize_of_wsize ty, cvari_of_vari tbl x, cexpr_of_expr tbl e)
  | Laset(x,e)     -> C.Laset (cvari_of_vari tbl x, cexpr_of_expr tbl e)

let lval_of_clval tbl = function
  | C.Lnone(p,ty)-> Lnone (get_loc tbl p, ty_of_cty ty)
  | C.Lvar x     -> Lvar (vari_of_cvari tbl x)
  | C.Lmem(ty, x,e) -> Lmem (wsize_of_cwsize ty, vari_of_cvari tbl x, expr_of_cexpr tbl e)
  | C.Laset(x,e) -> Laset (vari_of_cvari tbl x, expr_of_cexpr tbl e)

(* ------------------------------------------------------------------------ *)

let clval_of_lvals tbl xs = List.map (clval_of_lval tbl) xs
let lval_of_clvals tbl xs = List.map (lval_of_clval tbl) xs

let cexpr_of_exprs tbl es = List.map (cexpr_of_expr tbl) es
let expr_of_cexprs tbl es = List.map (expr_of_cexpr tbl) es

(* ------------------------------------------------------------------------ *)

let cat_of_at = function
  | AT_keep       -> C.AT_keep
  | AT_rename_arg -> C.AT_rename_arg
  | AT_rename_res -> C.AT_rename_res
  | AT_unroll     -> C.AT_inline
  | AT_phinode -> assert false

let at_of_cat = function
  | C.AT_keep       -> AT_keep
  | C.AT_rename_arg -> AT_rename_arg
  | C.AT_rename_res -> AT_rename_res
  | C.AT_inline     -> AT_unroll

(* ------------------------------------------------------------------------ *)

let crdir_of_rdir = function
  | UpTo   -> C.UpTo
  | DownTo -> C.DownTo

let rdir_of_crdir = function
  | C.UpTo   -> UpTo
  | C.DownTo -> DownTo

(* ------------------------------------------------------------------------ *)

let cii_of_ii = function
  | DoInline -> C.InlineFun
  | NoInline -> C.DoNotInline

let ii_of_cii = function
  | C.InlineFun   -> DoInline
  | C.DoNotInline -> NoInline

(* ------------------------------------------------------------------------ *)

let cfun_of_fun tbl fn =
  try Hashtbl.find tbl.funname fn
  with Not_found ->
    let p = pos_of_int (new_count tbl) in
    Hashtbl.add tbl.funname fn p;
    Hashtbl.add tbl.cfunname p fn;
    p

let fun_of_cfun tbl p =
  try Hashtbl.find tbl.cfunname p
  with Not_found -> assert false

(* ------------------------------------------------------------------------ *)

let set_iinfo tbl loc ii =
  let n = new_count tbl in
  Hashtbl.add tbl.iinfo n (loc, ii);
  pos_of_int n

let get_iinfo tbl n =
  try Hashtbl.find tbl.iinfo (int_of_pos n)
  with Not_found ->
    Format.eprintf "WARNING: CAN NOT FIND IINFO %i@." (int_of_pos n);
    L._dummy, tbl.dft_info

let rec cinstr_of_instr tbl i c =
  let n = set_iinfo tbl i.i_loc i.i_info in
  cinstr_r_of_instr_r tbl n i.i_desc c

and cinstr_r_of_instr_r tbl p i tl =
  match i with
  | Cblock c -> cstmt_of_stmt tbl c tl
  | Cassgn(x,t,e) ->
    let ir  =
      C.Cassgn(clval_of_lval tbl x, cat_of_at t, cexpr_of_expr tbl e) in
    C.MkI(p, ir) :: tl
  | Copn(x,o,e) ->
    let ir =
      C.Copn(clval_of_lvals tbl x, copn_of_opn o, cexpr_of_exprs tbl e) in
    C.MkI(p, ir) :: tl

  | Cif(e,c1,c2) ->
    let c1 = cstmt_of_stmt tbl c1 [] in
    let c2 = cstmt_of_stmt tbl c2 [] in
    let ir = C.Cif(cexpr_of_expr tbl e, c1, c2) in
    C.MkI(p, ir) :: tl

  | Cfor(x, (d,e1,e2), c) ->
    let d = ((crdir_of_rdir d, cexpr_of_expr tbl e1), cexpr_of_expr tbl e2) in
    let x = cvari_of_vari tbl x in
    let c = cstmt_of_stmt tbl c [] in
    let ir = C.Cfor(x,d,c) in
    C.MkI(p, ir) :: tl
  | Cwhile(c, e, c') ->
    let ir = C.Cwhile(cstmt_of_stmt tbl c [], cexpr_of_expr tbl e,
                      cstmt_of_stmt tbl c' []) in
    C.MkI(p,ir) :: tl
  | Ccall(ii, x, f, e) ->
    let ii = cii_of_ii ii in
    let ir =
      C.Ccall(ii, clval_of_lvals tbl x, cfun_of_fun tbl f, cexpr_of_exprs tbl e)
    in
    C.MkI(p,ir) :: tl

and cstmt_of_stmt tbl c tl =
  List.fold_right (cinstr_of_instr tbl) c tl

let rec instr_of_cinstr tbl i =
  match i with
  | C.MkI(p, ir) ->
    let (i_loc, i_info) = get_iinfo tbl p in
    let i_desc = instr_r_of_cinstr_r tbl ir in
    { i_desc; i_loc; i_info }

and instr_r_of_cinstr_r tbl = function
  | C.Cassgn(x,t,e) ->
    Cassgn(lval_of_clval tbl x, at_of_cat t, expr_of_cexpr tbl e)

  | C.Copn(x,o,e) ->
    Copn(lval_of_clvals tbl x, opn_of_copn o, expr_of_cexprs tbl e)

  | C.Cif(e,c1,c2) ->
    let c1 = stmt_of_cstmt tbl c1 in
    let c2 = stmt_of_cstmt tbl c2 in
    Cif(expr_of_cexpr tbl e, c1, c2)

  | Cfor(x, ((d,e1),e2), c) ->
    let d = (rdir_of_crdir d, expr_of_cexpr tbl e1, expr_of_cexpr tbl e2) in
    let x = vari_of_cvari tbl x in
    let c = stmt_of_cstmt tbl c in
    Cfor(x,d,c)

  | Cwhile(c, e, c') ->
    Cwhile(stmt_of_cstmt tbl c, expr_of_cexpr tbl e, stmt_of_cstmt tbl c')

  | Ccall(ii, x, f, e) ->
    let ii = ii_of_cii ii in
    Ccall(ii, lval_of_clvals tbl x, fun_of_cfun tbl f, expr_of_cexprs tbl e)

and stmt_of_cstmt tbl c =
  List.map (instr_of_cinstr tbl) c


(* ------------------------------------------------------------------------ *)

let set_finfo tbl loc cc =
  let n = new_count tbl in
  Hashtbl.add tbl.finfo n (loc, cc);
  pos_of_int n

let get_finfo tbl n =
  try Hashtbl.find tbl.finfo (int_of_pos n)
  with Not_found -> assert false

let cfdef_of_fdef tbl fd =
  let fn = cfun_of_fun tbl fd.f_name in
  let f_iinfo = set_finfo tbl fd.f_loc fd.f_cc in
  let f_params =
    List.map (fun x -> cvari_of_vari tbl (L.mk_loc L._dummy x)) fd.f_args in
  let f_body = cstmt_of_stmt tbl fd.f_body [] in
  let f_res = List.map (cvari_of_vari tbl) fd.f_ret in
  fn, { C.f_iinfo = f_iinfo;
        C.f_params = f_params;
        C.f_body   = f_body;
        C.f_res    = f_res }


let fdef_of_cfdef tbl (fn, fd) =
  let f_loc, f_cc = get_finfo tbl fd.C.f_iinfo in
  { f_loc;
    f_cc;
    f_name = fun_of_cfun tbl fn;
    f_args = List.map (fun v -> L.unloc (vari_of_cvari tbl v)) fd.C.f_params;
    f_body = stmt_of_cstmt tbl fd.C.f_body;
    f_ret  = List.map (vari_of_cvari tbl) fd.C.f_res;
  }

let cprog_of_prog info p =
  let tbl = empty_tbl info in
  (* First add registers *)
  List.iter
    (fun x -> ignore (cvar_of_reg tbl x))
    Regalloc.X64.all_registers;
  Format.eprintf "Register string@.";
  List.iter (fun x ->
      let cv = cvar_of_var tbl x in
      Format.eprintf "%s " (string_of_string0 cv.Var.vname))
    Regalloc.X64.all_registers;
  Format.eprintf "@.";

  tbl, List.map (cfdef_of_fdef tbl) p

let prog_of_cprog tbl p =
  List.map (fdef_of_cfdef tbl) p
