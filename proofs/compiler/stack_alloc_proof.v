(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import psem compiler_util constant_prop_proof.
Require Export stack_alloc stack_sem.
Require Import Psatz.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
Local Open Scope Z_scope.

(* --------------------------------------------------------------------------- *)

Lemma size_of_pos t s : size_of t = ok s -> (1 <= s).
Proof.
  case: t => //= [p [] <-| sz [] <-]; first by lia.
  have hsz := wsize_size_pos sz; nia.
Qed.

Definition ptr_ok (w: pointer) (z:Z) :=
  wunsigned w + z <= wbase Uptr /\
  forall ofs s,
    is_align (w + wrepr _ ofs) s = is_align (wrepr _ ofs) s.

Definition ptr_size (stk_size glob_size :Z) ms :=
  if ms == MSstack then stk_size else glob_size.

Definition valid_map (gm:gmap) (sm:smap) (stk_size glob_size:Z) :=
  forall x mpx, find_gvar gm sm x = Some mpx -> 
     exists sx, size_of (vtype x.(gv)) = ok sx /\
     [/\ 0 <= mpx.(mp_ofs), mpx.(mp_ofs) + sx <= ptr_size stk_size glob_size mpx.(mp_s),
         aligned_for (vtype x.(gv)) mpx.(mp_ofs) &
         forall y mpy sy, 
           find_gvar gm sm y = Some mpy -> 
           size_of (vtype y.(gv)) = ok sy ->
           mpx.(mp_s) = mpy.(mp_s) ->
           if mpx.(mp_ofs) == mpy.(mp_ofs) then sx = sy
           else mpx.(mp_ofs) + sx <= mpy.(mp_ofs) \/ mpy.(mp_ofs) + sy <= mpx.(mp_ofs)].

Hint Resolve is_align_no_overflow Memory.valid_align.

(* TODO: MOVE *)

Lemma is_word_typeP ty ws : 
  is_word_type ty = Some ws -> ty = sword ws.
Proof. by case: ty => //= w [->]. Qed.

Lemma cast_ptrP gd s e i : sem_pexpr gd s e = ok (Vint i) ->
  sem_pexpr gd s (cast_ptr e) = ok (Vword (wrepr U64 i)).
Proof. by move=> h;rewrite /cast_ptr /cast_w /= h. Qed.

Lemma cast_wordP gd s e i : sem_pexpr gd s e = ok (Vint i) ->
  exists sz (w:word sz), sem_pexpr gd s (cast_word e) = ok (Vword w) /\
                         truncate_word U64 w = ok (wrepr U64 i).
Proof.
  move=> he.
  have : exists sz (w:word sz), 
              sem_pexpr gd s (cast_ptr e) = ok (Vword w) /\
                      truncate_word U64 w = ok (wrepr U64 i). 
  + exists U64, (wrepr U64 i); split; first by apply cast_ptrP.
    by rewrite truncate_word_u.
  case: e he => // -[] // [] //=.
  move=> e he _; move: he; rewrite /sem_sop1 /=; t_xrbindP => v -> w.
  case v => //= [sw w'| []//] /truncate_wordP [hsw ->] <-.
  by exists sw, w'; split => //; rewrite /truncate_word hsw wrepr_unsigned.
Qed.

Lemma mk_ofsP sz gd s2 ofs e i :
  sem_pexpr gd s2 e = ok (Vint i) ->
  sem_pexpr gd s2 (mk_ofs sz e ofs) = ok (Vword (wrepr U64 (i * wsize_size sz + ofs)%Z)).
Proof.
  rewrite /mk_ofs; case is_constP => /= [? [->] //| {e} e he] /=.
  rewrite /sem_sop2 /=.
  have [sz' [w [-> /= -> /=]]]:= cast_wordP he.
  by rewrite !zero_extend_u wrepr_add wrepr_mul GRing.mulrC. 
Qed.

Lemma subtypeEl ty ty': subtype ty ty' → 
  match ty with
  | sbool => ty' = sbool
  | sint => ty' = sint
  | sarr n => ∃ n' : positive, ty' = sarr n' ∧ n <= n'
  | sword sz => ∃ sz' : wsize, ty' = sword sz' ∧ (sz ≤ sz')%CMP
  end.
Proof.
  (case: ty => /= [/eqP <-|/eqP <-| p | sz ] //;
   case: ty') => // [p' /ZleP ? | sz' ?]; eauto.
Qed.
  
Lemma validr_valid_pointer (m1:mem) p ws : is_ok (validr m1 p ws) = valid_pointer m1 p ws.
Proof.
  case: (Memory.readV m1 p ws); rewrite Memory.readP /CoreMem.read.
  + by move=> [w]; case: validr.
  by case: validr => //= _ [];eauto.
Qed.

(* End MOVE *)

Section PROOF.
  Variable P: prog.
  Notation gd := (p_globs P).
  Variable SP: sprog.

  Variable stk_size : Z.
  Variable rsp : pointer.
  Variable glob_size : Z.
  Variable rip : pointer. 
  Variable data : seq u8.

  Hypothesis rsp_add : ptr_ok rsp stk_size.
  Hypothesis rip_add : ptr_ok rip glob_size.

  Variable gm:gmap.

Section EXPR.

  Variable sm:smap.
 
  Definition wptr mp := if mp == MSstack then rsp else rip.

  Lemma wptr_add x : ptr_ok (wptr x) (ptr_size stk_size glob_size x).
  Proof. by rewrite /wptr /ptr_size; case: ifP. Qed.

  Definition valid_ptr_word (vm1:vmap) (m2:mem) ms (p: Z) sz x :=
    valid_pointer m2 (wptr ms + wrepr _ p) sz /\
    forall v, get_gvar gd vm1 x = ok v ->
    exists2 w,
      read_mem m2 (wptr ms + wrepr _ p) sz = ok w &
      v = Vword w.

  Definition valid_ptr_arr (vm1:vmap) (m2:mem) ms (p: Z) s x :=
    forall off, (0 <= off < Zpos s)%Z ->
      valid_pointer m2 (wptr ms + (wrepr _ (off + p))) U8 /\
      forall s' (a:WArray.array s'),
        get_gvar gd vm1 x = ok (Varr a) ->
        forall v, WArray.get U8 a off = ok v ->
          read_mem m2 (wptr ms + (wrepr _ (off + p))) U8 = ok v.

  Definition valid_stk (vm1:vmap) (vm2:vmap) (m2:mem) :=
    forall x,
      match find_gvar gm sm x with
      | Some mp =>
        (if mp.(mp_id) is Some id then
           Sv.mem {| vname := id; vtype := sword Uptr |} sm.(maddrvar) /\
           get_var vm2 {| vname := id; vtype := sword Uptr |} = ok (Vword (wptr mp.(mp_s) + wrepr _ mp.(mp_ofs)))%R
         else True) /\
        match vtype x.(gv) with
        | sword sz => valid_ptr_word vm1 m2 mp.(mp_s) mp.(mp_ofs) sz x
        | sarr s => valid_ptr_arr vm1 m2 mp.(mp_s) mp.(mp_ofs) s x
        | _ => True
        end
      | _ => True
      end.

  Definition eq_vm (vm1 vm2:vmap) := 
    forall (x:var), 
       ~~ is_in_stk sm x -> ~~ is_vrsp gm x -> ~~ is_vrip gm x -> ~~ Sv.mem x sm.(maddrvar) ->
       eval_uincl vm1.[x] vm2.[x].

  Lemma eq_vm_write vm1 vm2 x v v':
    eq_vm vm1 vm2 ->
    eval_uincl v v' -> 
    eq_vm vm1.[x <- v] vm2.[x <- v'].
  Proof.
    move=> Heqvm Hu w ????.
    case : (x =P w) => [<- | /eqP ?];first by rewrite !Fv.setP_eq.
    by rewrite !Fv.setP_neq //; apply Heqvm.
  Qed.

  Definition disjoint_ptr m :=
    forall w sz,
      valid_pointer m w sz ->
      ~((wunsigned rsp <? wunsigned w + wsize_size sz) && (wunsigned w <? wunsigned rsp + stk_size)) /\
      ~((wunsigned rip <? wunsigned w + wsize_size sz) && (wunsigned w <? wunsigned rip + glob_size)).

  Record valid (s1 s2: estate) : Prop := Valid {
    valid_disj : disjoint_ptr (emem s1);
    valid_eq   :
      forall w sz, valid_pointer (emem s1) w sz -> read_mem (emem s1) w sz = read_mem (emem s2) w sz;
    valid_def  :
      forall w sz, valid_pointer (emem s2) w sz = 
         valid_pointer (emem s1) w sz || (between rsp stk_size w sz && is_align w sz) || 
            (between rip glob_size w sz && is_align w sz);
    valid_vm   : eq_vm (evm s1) (evm s2);
    valid_rip  : get_var (evm s2) (vrip gm) = ok (Vword rip);
    valid_rsp  : get_var (evm s2) (vrsp gm) = ok (Vword rsp);
    valid_top  : top_stack (emem s2) = rsp;
    valid_frame: frame_size (emem s2) rsp = Some stk_size;
    valid_s    : valid_stk (evm s1) (evm s2) (emem s2);
    valid_m    : valid_map gm sm stk_size glob_size;
(*    valid_a    : forall x, Sv.mem x sm.(maddrvar) -> vtype x = sword Uptr; *)
    valid_glob : forall i, 
         0 <= i < glob_size ->
         read_mem (emem s2) (rip + wrepr U64 i) U8 = ok (nth (wrepr U8 0) data (Z.to_nat i))
  }.

  Lemma check_varP vm1 vm2 x v:
    check_var gm sm x -> eq_vm vm1 vm2 -> 
    get_var vm1 x = ok v ->
    exists v', get_var vm2 x = ok v' /\ value_uincl v v'.
  Proof.
    move=> /andP[] /andP[] /andP[] Hin_stk Hnot_rsp Hnot_rip Hnot_addr Heq Hget.
    have := Heq _ Hin_stk Hnot_rsp Hnot_rip Hnot_addr.
    move: Hget;rewrite /get_var; apply: on_vuP => [t | ] -> //=.
    by move=> <-;case vm2.[x] => //= s Hs;exists (pto_val s).
  Qed.

  Lemma check_varsP vm1 vm2 xs vs:
    all (check_var gm sm) xs -> eq_vm vm1 vm2 ->
    mapM (fun x : var_i => get_var vm1 x) xs = ok vs ->
    exists vs', 
      mapM (fun x : var_i => get_var vm2 x) xs = ok vs' /\
      List.Forall2 value_uincl vs vs'.
  Proof.
    elim: xs vs=> [|a l IH] //= vs.
    + move=> _ Heq [<-];by exists [::].
    move=> /andP [Ha Hl] Heq.
    apply: rbindP => va /(check_varP Ha Heq) [v' [-> Hu]].
    apply: rbindP => tl  /(IH _ Hl Heq) [tl' [-> Hus]] [<-] /=.
    by exists (v' :: tl');split=>//;constructor.
  Qed.

  Lemma get_arr_read_mem vm mem mp (n n':positive) (t : WArray.array n) x ws i w:
    n <= n' -> find_gvar gm sm x = Some mp ->
    valid_ptr_arr vm mem mp.(mp_s) mp.(mp_ofs) n' x ->
    is_align (wrepr U64 mp.(mp_ofs)) ws -> 
    get_gvar gd vm x = ok (Varr t) ->
    WArray.get ws t i = ok w ->
    read_mem mem (wptr mp.(mp_s) + wrepr U64 (i * wsize_size ws + mp.(mp_ofs))) ws = ok w.
  Proof.
    move=> hnn' hm hvalid halign hvget hget.
    rewrite Memory.readP /CoreMem.read.
    have hbound := WArray.get_bound hget.
    have hv : valid_pointer mem (wptr mp.(mp_s) + wrepr U64 (i * wsize_size ws + mp.(mp_ofs))) ws.
    + apply Memory.is_align_valid_pointer.
      + by case : (wptr_add mp.(mp_s)) => ? ->; rewrite Z.mul_comm wrepr_add is_align_array.
      move=> k hk; have [] := hvalid  (i * wsize_size ws + k).
      + by nia.
      by rewrite -Z.add_assoc (Z.add_comm k) Z.add_assoc wrepr_add GRing.addrA.
    have := validr_valid_pointer mem (wptr mp.(mp_s) + wrepr U64 (i * wsize_size ws + mp.(mp_ofs)))%R ws.
    rewrite hv; case: validr => //= _ _.
    move: (hget);rewrite /WArray.get /CoreMem.read; t_xrbindP => ? _ <-.
    do 2 f_equal; rewrite /CoreMem.uread.
    apply eq_map_ziota => k hk /=.
    have [v]:= WArray.get_get8 hget hk.
    have []/= := hvalid (i * wsize_size ws + k);first nia.
    move=> hva /(_ _ _ hvget) h /dup [] /h h1 /WArray.get_uget ->.
    move: h1; rewrite Memory.readP /CoreMem.read.
    t_xrbindP=> ??; rewrite CoreMem.uread8_get => <-; f_equal.
    by rewrite Memory.addP !wrepr_add; ssrring.ssring.
  Qed.

  Lemma check_vfreshP x tt : 
    check_vfresh gm sm x = ok tt -> [/\ is_lvar x, ~~is_vrsp gm (gv x), ~~is_vrip gm (gv x) & ~~Sv.mem (gv x) sm.(maddrvar)].
  Proof.
    rewrite /check_vfresh; case: ifPn => //.
    case: ifPn => //=; case: ifPn => //=; case: ifPn => //=.
    by rewrite /is_glob /is_lvar; case: gk.
  Qed.

  Section CHECK_E_ESP.
    Context s s' (Hv: valid s s').

    Let X e : Prop :=
      ∀ e' v,
        alloc_e gm sm e = ok e' →
        sem_pexpr gd s e = ok v →
        ∃ v', sem_pexpr [::] s' e' = ok v' ∧ value_uincl v v'.

    Let Y es : Prop :=
      ∀ es' vs,
        mapM (alloc_e gm sm) es = ok es' →
        sem_pexprs gd s es = ok vs →
        ∃ vs', sem_pexprs [::] s' es' = ok vs' ∧ List.Forall2 value_uincl vs vs'.

    Lemma check_vfresh_get x v tt : eq_vm (evm s) (evm s') ->
      check_vfresh gm sm x = ok tt → 
      find_gvar gm sm x = None ->
      get_gvar gd (evm s) x = ok v → 
      ∃ v' : value, get_gvar [::] (evm s') x = ok v' ∧ value_uincl v v'.
    Proof.
      rewrite /find_gvar /get_gvar => hvm /check_vfreshP [-> nrsp nrip naddr].
      case heq: Mvar.get => [ [] | ] //= _; apply: check_varP => //.
      by rewrite /check_var nrsp nrip /is_in_stk heq.
    Qed.

    Lemma get_vptr ms : get_var (evm s') (vptr gm ms) = ok (Vword (wptr ms)).
    Proof.
      have hrsp := valid_rsp Hv; have hrip := valid_rip Hv.
      by rewrite /vptr /wptr ;case: ms => /=.
    Qed.

    Lemma check_e_esP : (∀ e, X e) * (∀ es, Y es).
    Proof.
      have Hvm: eq_vm (evm s) (evm s') by move: Hv => -[].
      apply: pexprs_ind_pair; subst X Y; split => /=.
      
      - by move=> ?? [<-] [<-];exists [::].

      - move=> e he es hes ??; t_xrbindP => e' /he{he}he es' /hes{hes}hes <-.
        move=> ? /he [v' /= [->]] /= vu ? /hes [vs1' [->]] uvs <- /=.
        by exists (v'::vs1');split => //;constructor.
 
      + by move=> z1 e2 v [<-] [<-]; exists z1.
      + by move=> b1 e2 v [<-] [<-]; exists b1.
      + by move=> n1 e2 v [<-] [<-]; eexists; split; first reflexivity.
    
      + move=> x1 e2 v.
        case heq : find_gvar => [ mp | ]; last first.
        + by t_xrbindP => ? h1 <-; apply: check_vfresh_get h1 heq.
        case heq1 : mp_id => //.
        case hw : is_word_type => [ws | //].
        have hty := is_word_typeP hw => {hw} -[<-] /=.
        rewrite get_vptr /= !zero_extend_u.
        by have := valid_s Hv x1; rewrite heq heq1 hty => -[] _ [h1 h2] /h2 [w] -> -> /=; exists (Vword w).
  
      + move=> sz x1 e1 IH e2 v; t_xrbindP => e1' /IH hrec.
        case heq: find_gvar => [mp | ];last first.
        + t_xrbindP => ? h1 <- /=; apply: on_arr_gvarP => n t Ht Harr.
          have [v' [-> /=]]:= check_vfresh_get Hvm h1 heq Harr.
          case: v' => //= n' a hincl.
          t_xrbindP => i ve /hrec [ve' [-> hve]] /(value_uincl_int hve) [??];subst ve ve'=> /= w hw <-.
          by have -> /= := WArray.uincl_get hincl hw; exists (Vword w).
        case:ifP=> //= halign [<-].
        apply: on_arr_gvarP => n t hsubt hget.
        t_xrbindP => i ve /hrec [ve' [hve' sve']] /(value_uincl_int sve') [??].
        move=> w hti ?; subst v ve ve' => /=.
        have [n' [/= heqt hnn']]:= subtypeEl hsubt.
        have := valid_s Hv x1; rewrite heq heqt; case: mp_id => [id | ] [hgeti hva].
        + case: hgeti => [hin hgeti];rewrite hgeti /= (mk_ofsP sz 0 hve') /= !zero_extend_u.
          have := get_arr_read_mem hnn' heq hva halign hget hti.
          have -> : (wptr (mp_s mp) + wrepr U64 (mp_ofs mp) + wrepr U64 (i * wsize_size sz + 0))%R = 
                    (wptr (mp_s mp) + wrepr U64 (i * wsize_size sz + mp_ofs mp))%R.
          + by rewrite !wrepr_add wrepr0; ssrring.ssring.
          by move=> -> /=; exists (Vword w).
        rewrite get_vptr /= (mk_ofsP sz mp.(mp_ofs) hve') /= !zero_extend_u.
        by rewrite (get_arr_read_mem hnn' heq hva halign hget hti);exists (Vword w).

      + move=> sz1 v1 e1 IH e2 v.
        case:ifP => // hc; t_xrbindP => e1' /IH hrec <- wv1 vv1 /= hget hto' we1 ve1.
        move=> /hrec [ve1' [->] hu] /= hto wr hr ?;subst v. 
        have [vv1' [-> hu'] /=]:= check_varP hc Hvm hget.
        rewrite (value_uincl_word hu hto) (value_uincl_word hu' hto') /=. 
        have hv:= read_mem_valid_pointer hr.
        by have <- := valid_eq Hv hv; rewrite hr /=;eexists;(split;first by reflexivity) => /=.
   
      + move=> o1 e1 IH e2 v.
        t_xrbindP => e1' /IH hrec <- ve1 /hrec [ve1' /= [-> hu] /=] /(vuincl_sem_sop1 hu) ->.
        by eexists;split;first by reflexivity.

      + move=> o1 e1 H1 e1' H1' e2 v.
        t_xrbindP => e1_ /H1 hrec e1'_ /H1' hrec' <- ve1 /hrec.
        move=> [ve1' /= [-> hu] /=] ve2 /hrec' [ve2' /= [-> hu'] /=] .
        move=> /(vuincl_sem_sop2 hu hu') ->. 
        by eexists;split;first by reflexivity.

      + move => e1 es1 H1 e2 v.
        t_xrbindP => es1' /H1{H1}H1 <- vs /H1{H1} /= [vs' []].
        rewrite /sem_pexprs => -> /= h1 h2. 
        by have [v' ??]:= (vuincl_sem_opN h2 h1);exists v'.

      move=> t e He e1 H1 e1' H1' e2 v.   
      t_xrbindP => e_ /He he e1_ /H1 hrec e1'_ /H1' hrec' <-.
      move=> b vb /he [vb' /= [-> ub]] /(value_uincl_bool ub) [??];subst vb vb'.
      move=> vte1 ve1 /hrec [ve1' /= [-> hu] /=] ht1 vte2 ve2 /hrec' [ve2' /= [-> hu'] /=] ht2 <-.
      have [? -> ?]:= truncate_value_uincl hu ht1.
      have [? -> ? /=]:= truncate_value_uincl hu' ht2.
      eexists;split;first by reflexivity.
      by case: (b).
    Qed.

  End CHECK_E_ESP.

  Definition alloc_eP e e' s s' v he hv :=
    (@check_e_esP s s' hv).1 e e' v he.

  Definition alloc_esP es es' s s' vs hs hv :=
    (@check_e_esP s s' hv).2 es es' vs hs.

End EXPR.

(* TODO: move *)
  Lemma get_gvar_neq x vi vm (v: exec (psem_t (vtype vi))): 
    (is_lvar x → vi != gv x) ->
    get_gvar gd vm.[vi <- v] x = get_gvar gd vm x.
  Proof.
    by rewrite /get_gvar;case: ifP => ? // /(_ erefl) hx; rewrite /get_var Fv.setP_neq.
  Qed.

  Lemma get_var_neq vm x v y :
    x <> y ->
    get_var vm.[x <- v] y = get_var vm y.
  Proof. move=> /eqP hne;rewrite /get_var /on_vu Fv.setP_neq //. Qed.

  Lemma valid_stk_write_notinstk sm s1 s2 vi v v':
    ~~ (is_in_stk sm vi) -> ~~ Sv.mem vi sm.(maddrvar) ->
    valid_stk sm (evm s1) (evm s2) (emem s2) ->
    valid_stk sm (evm s1).[vi <- v] (evm s2).[vi <- v'] (emem s2).
  Proof.
    move=> Hnotinstk Hnmem Hstk x.
    move: Hstk=> /(_ x).
    case Hget: find_gvar => [mp|] // [hid hv]; split.
    + case: mp_id hid => // id [h1 h2]; split => //.
      by rewrite get_var_neq // => heq; move: Hnmem;rewrite heq h1.
    have Hx: is_lvar x -> vi != x.(gv).
    + move=> hl;apply/negP=> /eqP Habs.
      by move: Hnotinstk Hget; rewrite /is_in_stk Habs /find_gvar hl; case: Mvar.get.
    case Htype: (vtype (gv x)) hv=> // [p|].
    + by move=> H off /H {H} [H H']; split; last rewrite get_gvar_neq.
    by move=> [H H'];split=> //= v0; rewrite get_gvar_neq //; apply: H'.
  Qed.

  Lemma valid_set_uincl sm s1 s2 vi v v': 
    vi != vrsp gm -> vi != vrip gm -> ~~ is_in_stk sm vi -> ~~ Sv.mem vi sm.(maddrvar) ->
    valid sm s1 s2 -> eval_uincl v v' -> 
    valid sm {| emem := emem s1; evm := (evm s1).[vi <- v] |}
             {| emem := emem s2; evm := (evm s2).[vi <- v'] |}.
  Proof.
    move=> neq1 neq2 nin naddr [????????] Hu;split=> //=.
    + by apply: eq_vm_write.
    + by rewrite /get_var Fv.setP_neq ?Hx //.
    + by rewrite /get_var Fv.setP_neq ?Hx //.
    by apply: valid_stk_write_notinstk.
  Qed. 

  Lemma check_varW sm (vi : var_i) (s1 s2: estate) v v':
    check_var gm sm vi -> valid sm s1 s2 -> value_uincl v v' -> 
    forall s1', write_var vi v s1 = ok s1' ->
    exists s2', write_var vi v' s2 = ok s2' /\ valid sm s1' s2'.
  Proof.
    move=> /andP [] /andP [] /andP [] Hnotinstk Hnvrsp Hnvrip Hnaddr Hval Hu s1'. 
    rewrite /write_var; apply: rbindP=> z /=; apply: set_varP;rewrite /set_var.
    + move=> t /(pof_val_uincl Hu) [t' [-> Htt']] <- [<-] /=.
      eexists;split;first reflexivity.
      by apply valid_set_uincl.
    case: vi Hnotinstk Hnvrsp Hnvrip Hnaddr => -[tvi nvi] vii /= Hnotinstk Hnvrsp Hnvrip Hnaddr.
    move=> /is_sboolP ?; subst tvi => /= /to_bool_undef ?; subst v => <- [<-].
    by have [-> | [b1 ->]] /=:= pof_val_undef Hu erefl;
     (eexists;split;first reflexivity); apply valid_set_uincl.
  Qed.

  Lemma check_varsW sm (vi : seq var_i) (s1 s2: estate) v v':
    all (check_var gm sm) vi -> valid sm s1 s2 -> 
    List.Forall2 value_uincl v v' -> 
    forall s1', write_vars vi v s1 = ok s1' ->
    exists s2', write_vars vi v' s2 = ok s2' /\ valid sm s1' s2'.
  Proof.
    elim: vi v v' s1 s2 => [|a l IH] //= [|va vl] [|va' vl'] s1 s2 //=.
    + by move=> _ Hv _ s1' []<-; exists s2.
    + by move => _ _ /List_Forall2_inv_l /seq_eq_injL.
    + by move => _ _ /List_Forall2_inv_r /seq_eq_injL.
    move=> /andP [Ha Hl] Hv /List_Forall2_inv_l [va''] [vl''] [] /seq_eq_injL [??]; subst va'' vl'' => - [] hva hvl s1'.
    apply: rbindP=> x Hwa.
    move: (check_varW Ha Hv hva Hwa)=> [s2' [Hs2' Hv2']] Hwl.
    move: (IH _ _ _ _ Hl Hv2' hvl _ Hwl)=> [s3' [Hs3' Hv3']].
    by exists s3'; split=> //; rewrite Hs2' /= Hs3'.
  Qed.

  Lemma Mvar_filterP (A:Type) (f: var -> A -> bool) (m:Mvar.t A) x a: 
    Mvar.get (Mvar_filter f m) x = Some a <->
    Mvar.get m x = Some a /\ f x a.
  Proof.
    rewrite /Mvar_filter; rewrite Mvar.foldP.
    set F := (λ (a0 : Mvar.t A) (kv : Mvar.K.t * A), if f kv.1 kv.2 then Mvar.set a0 kv.1 kv.2 else a0).
    have h : forall els m1,
              uniq [seq x.1 | x <- els] ->
              (forall e, List.In e els -> Mvar.get m1 e.1 = None) -> 
              Mvar.get (foldl F m1 els) x = Some a <->
              (Mvar.get m1 x = Some a \/ (List.In (x,a) els /\ f x a)).
    + elim => [ | [y ay] els ih] m1 /=; first by intuition.
      move=> /andP [] hy hu he; rewrite ih //; last first. 
      + move=> e h; rewrite /F /=; case: ifP => ?; last by auto.
        rewrite Mvar.setP_neq; first by auto.
        apply /eqP => ?;subst y.
        move /xseq.InP: hy => hy; apply hy.
        by apply: (List.in_map fst). 
      rewrite {1}/F; case: ifPn => /= [ | /negP] ?. 
      + rewrite Mvar.setP; case: eqP => ?.
        + subst; split.
          + by move=> [] [?]; first subst ay; auto.
          move=> []; first by rewrite (he (x,ay)); auto.
          by move=> [] [[??] | ]; subst; intuition.
        split; first by intuition. 
        move=> []; first by auto.
        by move=> [] [[??] |]; subst; intuition. 
      split; first by intuition. 
      move=> [];first by auto.
      move=> [[[??] | ]]; subst; intuition.
    rewrite h.
    + rewrite Mvar.get0 Mvar.elementsIn /=.
      split; last by auto.
      by move=> []; auto.
    + by apply Mvar.elementsU.
    by move=> e;rewrite Mvar.get0.
  Qed.

  Lemma eq_vm_write_rm sm vm1 vm2 x v v':
    (forall x, Sv.mem x sm.(maddrvar) -> vtype x = sword Uptr) ->
    eq_vm sm vm1 vm2 ->
    eval_uincl v v' ->
    eq_vm (map_remove sm x) vm1.[x <- v] vm2.[x <- v'].
  Proof.
    move=> hty Heqvm Hu w h1 h2 h3 h4.
    case : (x =P w) => [<- | /eqP hne];first by rewrite !Fv.setP_eq.
    move: h1 h4; rewrite /map_remove.
    case heq: is_word_type => [ws | ]; last first.
    + by move=> h1 h4; rewrite !Fv.setP_neq //; apply Heqvm.
    case: ifP; last first.
    + by move=> _ h1 h4; rewrite !Fv.setP_neq //; apply Heqvm.
    move=> /andP [] /eqP ? hin /= h1 /Sv_memP h4.
    rewrite !Fv.setP_neq //; apply Heqvm => //;
      last by apply /Sv_memP; move /eqP: hne; SvD.fsetdec.
    move: h1; rewrite /is_in_stk /=.
    case heq1: (Mvar.get (Mvar_filter _ _) _) => //.
    case heq2: Mvar.get => [mp' | ] //.
    have :=  Mvar_filterP (keep_addrvar (vname x)) (mstk sm) w mp'.
    rewrite heq1 heq2 /keep_addrvar.

admit.
rewrite /keep_addrvar.
      have := Mvar_filterP 
 
    apply /Sv_memP; move /Sv_memP : h4; move /eqP : hne; SvD.fsetdec.
Lemma Mvar_filterP : 
  Qed.

  Lemma valid_set_uincl_addr sm s1 s2 vi v v': 
    vi != vrsp gm -> vi != vrip gm -> ~~ is_in_stk sm vi -> 
    valid sm s1 s2 -> eval_uincl v v' ->
    valid (map_remove sm vi) {| emem := emem s1; evm := (evm s1).[vi <- v] |}
             {| emem := emem s2; evm := (evm s2).[vi <- v'] |}.
  Proof.
    move=> neq1 neq2 nin [????????] Hu;split=> //=.
Print eq_vm.
Print map_remove.
    + by apply: eq_vm_write.
    + by rewrite /get_var Fv.setP_neq ?Hx //.
    + by rewrite /get_var Fv.setP_neq ?Hx //.
    by apply: valid_stk_write_notinstk.
  Qed. 
(*~~ is_in_stk sm x ->
~~ is_vrsp gm x ->
 ~~ is_vrip gm x ->
eval_uincl v v' -> 

 valid (map_remove sm x) {| emem := emem s1; evm := (evm s1).[x <- v] |}
    {| emem := emem s2; evm := (evm s2).[x <- v'] |}
*)
  Lemma wunsigned_rsp_add ofs :
    0 <= ofs -> ofs < stk_size ->
    wunsigned (rsp + wrepr Uptr ofs) = wunsigned rsp + ofs.
  Proof.
    move => p1 p2; apply: wunsigned_add.
    case: rsp_add => h _; have := wunsigned_range rsp; lia.
  Qed.

  Lemma wunsigned_rip_add ofs :
    0 <= ofs -> ofs < glob_size ->
    wunsigned (rip + wrepr Uptr ofs) = wunsigned rip + ofs.
  Proof.
    move => p1 p2; apply: wunsigned_add.
    case: rip_add => h _; have := wunsigned_range rip; lia.
  Qed.

  Lemma wunsigned_wptr_add ofs x :
    0 <= ofs -> ofs < ptr_size stk_size glob_size x ->
    wunsigned (wptr x + wrepr Uptr ofs) = wunsigned (wptr x) + ofs.
  Proof.
    rewrite /wptr /ptr_size; case: is_lvar; auto using wunsigned_rsp_add, wunsigned_rip_add. 
  Qed.

  Lemma lt_of_add_le x y sz :
    x + wsize_size sz <= y -> x < y.
  Proof. have := wsize_size_pos sz; lia. Qed.

  Lemma get_find_gvar x ofs : 
    Mvar.get m.(mstk) x = Some ofs ->
    find_gvar m (mk_lvar ({|v_var := x; v_info := xH|})) = Some ofs.
  Proof. by rewrite /find_gvar /= => ->. Qed.

  Lemma find_between x ofs :
    find_gvar m x = Some ofs ->
    match vtype x.(gv) with
    | sword ws => between (wptr x) (ptr_size stk_size glob_size x) (wptr x + wrepr Uptr ofs) ws &&
                  is_align (wptr x + wrepr Uptr ofs) ws
                  
    | sarr n   => forall i, 0 <= i < n -> 
                  between (wptr x) (ptr_size stk_size glob_size x) (wptr x + wrepr Uptr (i + ofs)) U8 &&
                  is_align (wptr x + wrepr Uptr (i + ofs)) U8
    | _        => True
    end. 
  Proof.
    move=> hfind.
    have [sx]:= validm hfind.
    have [hstk halign] := wptr_add x.
    case: vtype => //= [p | ws] [] [<-] [] h1 h2 h3 h4 => [i hi| ];
    [have ? : wsize_size U8 = 1 by done| have ? := wsize_size_pos ws].
    + apply/andP;split.
      + by apply /andP;rewrite wunsigned_wptr_add;first (split;apply /ZleP); lia.
      by rewrite halign;apply is_align8.
    apply/andP;split.
    + by apply /andP;rewrite wunsigned_wptr_add;first (split;apply /ZleP); lia.
    by rewrite halign.
  Qed.

  Lemma valid_get_w sz vn ofs :
    Mvar.get m.(mstk) {| vtype := sword sz; vname := vn |} = Some ofs ->
    between rsp stk_size (rsp + wrepr Uptr ofs) sz && is_align (rsp + wrepr Uptr ofs) sz.
  Proof. by move=> /get_find_gvar -/find_between. Qed.

  Hypothesis disj_rsp_rip :
    0 < stk_size -> 0 < glob_size ->
    ((wunsigned rsp + stk_size <=? wunsigned rip) || (wunsigned rip + glob_size <=? wunsigned rsp)).

  Lemma between_rsp_rip_disj p1 p2 sz1 sz2 :
    between rsp stk_size p1 sz1 && is_align p1 sz1 ->
    between rip glob_size p2 sz2 && is_align p2 sz2 -> 
    disjoint_range p1 sz1 p2 sz2.
  Proof.
    rewrite /between /disjoint_range /disjoint_zrange => 
      /andP[]/andP[] /ZleP? /ZleP? ha1 /andP[]/andP[] /ZleP? /ZleP? ha2; split; eauto.
    have h1:  0 < stk_size.
    + have := wsize_size_pos sz1; lia.
    have h2: 0 < glob_size.
    + have := wsize_size_pos sz2; lia.
    move: (disj_rsp_rip h1 h2) => /orP [/ZleP ?| /ZleP ?]; lia.
  Qed.

  Lemma valid_stk_arr_var_stk s1 s2 sz xwn ofsw y ofsy n w m':
    let xw := {| vname := xwn; vtype := sword sz |} in
    Mvar.get m.(mstk) xw = Some ofsw ->
    find_gvar m y = Some ofsy ->  
    vtype y.(gv) = sarr n -> 
    write_mem (emem s2) (rsp + wrepr _ ofsw) sz w = ok m' ->
    valid_ptr_arr (evm s1) (emem s2) ofsy n y ->
    valid_ptr_arr (evm s1).[xw <- ok (pword_of_word w)] m' ofsy n y.
  Proof.
    move=> xw Hgetw hfind hty Hm' H off Hoff.
    have Hvmem : valid_pointer (emem s2) (rsp + wrepr _ ofsw) sz by apply /Memory.writeV;eauto.
    move: H=> /(_ off Hoff) [Hoff1 Hoff2]; split.
    - by rewrite (Memory.write_valid _ _ Hm').
    have hxwa : xw != y.(gv) by rewrite vtype_diff // hty.
    rewrite get_gvar_neq // => t a Ht v0 Hv0.
    rewrite -(Hoff2 _ _ Ht _ Hv0).
    apply: (Memory.writeP_neq Hm').
    case his : (is_lvar y);last first.
    + have := find_between hfind.
      rewrite hty /ptr_size /wptr his => /(_ _ Hoff).
      by apply: between_rsp_rip_disj (valid_get_w Hgetw).
    have /andP [h1 h2]:= valid_get_w Hgetw. 
    case: (validm hfind) => sa [].
    rewrite /ptr_size /wptr his hty /= => -[]hsa [ha ha' haal] _; subst sa.
    case: (validm (get_find_gvar Hgetw)) => sw /= [] [<-] [hw hw' ? /(_ y _ n hxwa _ hfind)].
    rewrite (eqP his) hty => /(_ erefl erefl) hdisj.
    split.
    + by apply is_align_no_overflow.
    + by apply is_align_no_overflow; apply is_align8.
    have : wunsigned (rsp + wrepr _ ofsw) = wunsigned rsp + ofsw.
    + by apply: (wunsigned_wptr_add hw (lt_of_add_le hw')).
    rewrite wsize8.
    have : wunsigned (rsp + wrepr _ (off + ofsy)) = wunsigned rsp + off + ofsy.
    - rewrite wunsigned_rsp_add;lia.
    have hsz := wsize_size_pos sz.
    nia.
  Qed.

  Lemma valid_stk_word_var_stk s1 s2 sz xn sz' y ofsx ofsy m' w:
    let x := {| vtype := sword sz; vname := xn |} in
    Mvar.get m.(mstk) x = Some ofsx ->
    find_gvar m y = Some ofsy ->  
    vtype y.(gv) = sword sz' -> 
    write_mem (emem s2) (rsp + wrepr _ ofsx) sz w = ok m' ->
    valid_ptr_word (evm s1) (emem s2) ofsy sz' y ->
    valid_ptr_word (evm s1).[x <- ok (pword_of_word w)] m' ofsy sz' y.
  Proof.
    move=> xw Hget hfind hty Hm' [H H'].
    have Hvmem : valid_pointer (emem s2) (rsp + wrepr _ ofsx) sz by apply /Memory.writeV;eauto.
    split; first by rewrite (Memory.write_valid _ _ Hm').
    move=> v.
    case his: (is_lvar y);first last.
    + rewrite get_gvar_neq ?his // => /H' [w' h1 h2];exists w' => //.
      rewrite -h1; apply: (Memory.writeP_neq Hm').
      have := find_between hfind.
      rewrite hty /ptr_size /wptr his. 
      by apply: between_rsp_rip_disj (valid_get_w Hget).
    case: (xw =P y.(gv)) => [ | /eqP] heq.
    + move: hfind hty; rewrite /find_gvar /get_gvar /wptr his /get_var -heq /= /on_vu 
        Fv.setP_eq Hget => -[?] [?] [?] /=;subst; exists w => //.
      exact: (Memory.writeP_eq Hm').
    rewrite get_gvar_neq // => /H' [w' h1 h2];exists w' => //. 
    rewrite (Memory.writeP_neq Hm') => //. 
    split; eauto.
    case: (validm (get_find_gvar Hget)) => sx [] [<-] {sx} [hw hw' hxal] /(_ _ _ _ heq _ hfind). 
    rewrite /= (eqP his) hty => /(_ _ erefl erefl) hdisj.
    case: (validm hfind) => sa [];rewrite hty /ptr_size /wptr his => -[<-] {sa} [ha ha' haal] _.
    have : wunsigned (rsp + wrepr _ ofsx) = wunsigned rsp + ofsx.
    - by apply: (wunsigned_rsp_add hw (lt_of_add_le hw')).
    have haha : wunsigned (rsp + wrepr _ ofsy) = wunsigned rsp + ofsy.
    - by apply: (wunsigned_rsp_add ha (lt_of_add_le ha')).
    lia.
  Qed.

  Lemma valid_stk_var_stk s1 s2 sz (w: word sz) m' xn ofs ii:
    let vi := {| v_var := {| vtype := sword sz; vname := xn |}; v_info := ii |} in
    Mvar.get m.(mstk) vi = Some ofs ->
    write_mem (emem s2) (rsp + wrepr _ ofs) sz w = ok m' ->
    valid_stk (evm s1) (emem s2) ->
    valid_stk (evm s1).[{| vtype := sword sz; vname := xn |} <- ok (pword_of_word w)] m'.
  Proof.
    move=> vi Hget Hm' H x; move: H=> /(_ x).
    have Hvmem : valid_pointer (emem s2) (rsp + wrepr _ ofs) sz by apply /Memory.writeV;eauto.
    case hfind : find_gvar => [ofs'|//].
    case hty: vtype => //.
    + exact: (valid_stk_arr_var_stk Hget hfind). 
    exact: (valid_stk_word_var_stk Hget hfind).
  Qed.

  Lemma valid_var_stk s1 xn sz w s2 m' ofs ii:
    valid s1 s2 ->
    write_mem (emem s2) (rsp + wrepr _ ofs) sz w = ok m' ->
    let vi := {| v_var := {| vtype := sword sz; vname := xn |}; v_info := ii |} in
    Mvar.get m.(mstk) vi = Some ofs ->
    valid {|
      emem := emem s1;
      evm := (evm s1).[{| vtype := sword sz; vname := xn |} <- ok (pword_of_word w)] |}
      {| emem := m'; evm := evm s2 |}.
  Proof.
    move=> [] H1 H2 H3 H4 H5 hrip Hrsp Hssz H6 hg Hm' vi Hget.
    have Hmem : valid_pointer (emem s2) (rsp + wrepr _ ofs) sz.
    + by apply/Memory.writeV; eauto.
    split=> //=.
    + move=> w' sz' Hvalid.
      have := validm (get_find_gvar Hget).
      rewrite /ptr_size /= => -[sx [hsx [ho1 ho2 hal hdisj]]].
      have [hov hal'] := rsp_add.
      rewrite (H2 _ _ Hvalid); symmetry; apply: (Memory.writeP_neq Hm').
      split; eauto.
      case: hsx => ?; subst sx.
      have : wunsigned (rsp + wrepr _ ofs) = wunsigned rsp + ofs.
      - by apply: (wunsigned_rsp_add ho1 (lt_of_add_le ho2)).
      have []:= H1 _ _ Hvalid.
      case/negP/nandP => /ZltP /Z.nlt_ge h h'; lia.
    + by move=> w' sz'; rewrite -H3 -(Memory.write_valid _ _ Hm').
    + move=> x Hx1 Hx2.
      rewrite Fv.setP_neq; first exact: H4.
      apply/negP=> /eqP ?; subst x.
      by rewrite /is_in_stk Hget in Hx1.
    + by have [<- _ _] := Memory.write_mem_stable Hm'.
    + by have [_ _ <-] := Memory.write_mem_stable Hm'.
    + exact: (valid_stk_var_stk Hget Hm').
    move=> i [hi1 hi2].
    rewrite (Memory.writeP_neq Hm') ?hg //.
    apply between_rsp_rip_disj.
    + rewrite (Memory.valid_align Hmem) andbT.
      have [/=]:= validm (get_find_gvar Hget).
      rewrite /ptr_size /= => x [ [? [h1 h2 h3] ?]];subst x.
      have ho : ofs < stk_size by have := wsize_size_pos sz;lia.
      apply /andP; rewrite wunsigned_rsp_add //;split;apply /ZleP;lia.
    rewrite is_align8 andbT;apply /andP; rewrite wunsigned_rip_add // wsize8;split;apply /ZleP; lia.
  Qed.

  Lemma valid_map_arr_addr n x off ofsx :
    vtype x = sarr n -> 
    Mvar.get m.(mstk) x = Some ofsx ->
    0 <= off < Z.pos n ->
    wunsigned (rsp + wrepr U64 (off + ofsx)) =
    wunsigned rsp + off + ofsx.
  Proof.
    case: x => ty xn /= h; subst ty.
    move=> hget hoff;have := validm (get_find_gvar hget).
    rewrite /ptr_size /= => -[sx /= [[?] [??? _]]]; subst sx.
    rewrite wunsigned_add;first by ring.
    case: rsp_add => ? _; have ? := wunsigned_range rsp; nia.
  Qed. 

  Lemma valid_map_word_addr sz x ofsx: 
    vtype x = sword sz ->
    Mvar.get m.(mstk) x = Some ofsx ->
    wunsigned (rsp + wrepr U64 ofsx) = wunsigned rsp + ofsx.
  Proof.
    case: x => ty xn /= h; subst ty.
    move=> hget; have  := validm (get_find_gvar hget).
    rewrite /ptr_size /= => -[sx /= [[?] [??? _]]];subst sx.
    apply wunsigned_add; case: rsp_add => ? _; have ? := wsize_size_pos sz.
    have ? := wunsigned_range rsp;nia.
  Qed.

  Lemma valid_get_arr sz n i vn ofs :
    Mvar.get m.(mstk) {| vtype := sarr n; vname := vn |} = Some ofs ->
    0 <= i * wsize_size sz ∧ (i + 1) * wsize_size sz <= n ->
    is_align (rsp + wrepr _ (i * wsize_size sz + ofs)) sz ->
    between rsp stk_size (rsp + wrepr U64 (i * wsize_size sz + ofs)) sz &&
     is_align (rsp + wrepr U64 (i * wsize_size sz + ofs)) sz.
  Proof. 
    move=> /get_find_gvar hfind hi ->.
    have [sx]:= validm hfind.
    rewrite /ptr_size /= => -[] [?] [ho1 ho2 _ _]; subst sx.
    have [hstk halign] := rsp_add.
    have ? := wsize_size_pos sz; apply/andP;split => //.
    by apply /andP;rewrite wunsigned_rsp_add;first (split;apply /ZleP); lia.
  Qed.

  Lemma valid_stk_arr_arr_stk s1 s2 n n' sz xn x' ofsx ofsx' m' v0 i (a: WArray.array n) t:
    let x := {| vtype := sarr n; vname := xn |} in
    Mvar.get m.(mstk) x = Some ofsx ->
    find_gvar m x' = Some ofsx' ->
    vtype x'.(gv) = sarr n' ->
    get_var (evm s1) x = ok (Varr a) ->
    valid_pointer (emem s2) (rsp + wrepr _ (i * wsize_size sz + ofsx)) sz ->
    write_mem (emem s2) (rsp + wrepr _ (i * wsize_size sz + ofsx)) sz v0 = ok m' ->
    WArray.set a i v0 = ok t ->
    valid_ptr_arr (evm s1) (emem s2) ofsx' n' x' ->
    valid_ptr_arr (evm s1).[x <- ok t] m' ofsx' n' x'.
  Proof.
    move=> x Hget Hget' hty Ha Hvmem Hm' Ht.
    move=> H off Hoff.
    move: H=> /(_ off Hoff) [H /= H']; split.
    - by rewrite (Memory.write_valid _ _ Hm').
    move=> s' a0; case his: (is_lvar x');first last.
    + rewrite get_gvar_neq ?his // => /H' h v1 /h <-.
      apply: (Memory.writeP_neq Hm').
      have := find_between Hget'.
      rewrite hty /ptr_size /wptr his => /(_ _ Hoff).
      have := valid_get_arr Hget (WArray.set_bound Ht) (Memory.valid_align Hvmem). 
      by apply: between_rsp_rip_disj.
    case: (x =P x'.(gv)) => [ | /eqP] heq.
    + move: hty; rewrite /get_gvar his -heq /get_var /= Fv.setP_eq /= => -[?] h.
      have /Varr_inj [e ]:= ok_inj h; subst n' s'=> /= ?; subst a0 => {h}.
      move: Hget' H'; rewrite /find_gvar /get_gvar /wptr his -heq Hget => -[?] H' v1 Hv1; subst ofsx'.
      have -> := Memory.write_read8 (rsp + wrepr U64 (off + ofsx)) Hm'.
      have /= := WArray.set_get8 off Ht; rewrite Hv1.
      rewrite (valid_map_arr_addr _ Hget Hoff) //.
      have /(valid_map_arr_addr _ Hget) -> // : 0 <= i * wsize_size sz < Z.pos n.
      + by have ? := WArray.set_bound Ht; have ? := wsize_size_pos sz; nia.
      have -> : wunsigned rsp + off + ofsx - (wunsigned rsp + i * wsize_size sz + ofsx) =
                off - i * wsize_size sz by ring.
      by case: ifPn => // ? h; apply: (H' _ a).
    rewrite get_gvar_neq //.
    move => /H'{H'}H' v /H'{H'}.
    move: (Hget') H; rewrite /find_gvar /wptr his.
    case Hget1':  Mvar.get => [ofs1 | //] [?] H;subst ofs1. 
    rewrite (Memory.writeP_neq Hm') //.
    split; eauto.
    rewrite (valid_map_arr_addr _ Hget1' Hoff) //.
    have /(valid_map_arr_addr _ Hget) -> // : 0 <= i * wsize_size sz < Z.pos n.
    + by have ? := WArray.set_bound Ht; have ? := wsize_size_pos sz; nia.
    rewrite wsize8. 
    have [sx [/= [?] [??? H1]]]:= validm (get_find_gvar Hget);subst sx.
    have := H1 _ _ _ heq _ Hget'; rewrite hty (eqP his) => /(_ n' erefl erefl).
    have ? := wsize_size_pos sz; have ? := WArray.set_bound Ht; nia.
  Qed.

  Lemma valid_stk_word_arr_stk n xan sz xw sz' ofsa ofsw (a: WArray.array n) m' s1 s2 t v0 i:
    let xa := {| vtype := sarr n; vname := xan |} in
    Mvar.get m.(mstk) xa = Some ofsa ->
    find_gvar m xw = Some ofsw ->
    vtype xw.(gv) = sword sz' ->
    get_var (evm s1) xa = ok (Varr a) ->
    valid_pointer (emem s2) (rsp + wrepr _ (i * wsize_size sz + ofsa)) sz ->
    write_mem (emem s2) (rsp + wrepr _ (i * wsize_size sz + ofsa)) sz v0 = ok m' ->
    WArray.set a i v0 = ok t ->
    valid_ptr_word (evm s1) (emem s2) ofsw sz' xw ->
    valid_ptr_word (evm s1).[xa <- ok t] m' ofsw sz' xw.
  Proof.
    move=> xa Hgeta Hgetw hty Ha Hvmem Hm' Ht [H H'].
    split.
    + by rewrite (Memory.write_valid _ _ Hm').
    move=> /= v1.
    have hxwa : xa != xw.(gv) by rewrite vtype_diff // hty.
    rewrite get_gvar_neq // => Hv1.
    have [w' h1 h2]:= H' _ Hv1;subst v1; exists w' => //; rewrite -h1.
    apply: (Memory.writeP_neq Hm').
    case his : (is_lvar xw);last first.
    + have := find_between Hgetw.
      rewrite hty /ptr_size /wptr his. 
      have := valid_get_arr Hgeta (WArray.set_bound Ht) (Memory.valid_align Hvmem). 
      by apply: between_rsp_rip_disj. 
    split; eauto.
    rewrite /wptr his.
    have Hi:= WArray.set_bound Ht; have ? := wsize_size_pos sz.
    have /(valid_map_arr_addr _ Hgeta) -> // : 0 <= i * wsize_size sz < Z.pos n.
    + by have ? := WArray.set_bound Ht; have ? := wsize_size_pos sz; nia.
    have := validm (get_find_gvar Hgeta).
    rewrite /= /ptr_size /= => -[sx [/= [?] [??? H1]]]; subst sx.
    have := H1 _ _ _ hxwa _ Hgetw; rewrite hty (eqP his) => /(_ _ erefl erefl).
    have := validm Hgetw.
    rewrite /= /ptr_size his hty /= => -[sx [/= [?] [????]]]; subst sx.
    have ? := wsize_size_pos sz'; rewrite wunsigned_rsp_add //; nia.
  Qed.

  Lemma valid_stk_arr_stk s1 s2 sz vn n m' v0 i ofs (a: WArray.array n) t:
    let vi := {| vtype := sarr n; vname := vn |} in
    Mvar.get m.(mstk) vi = Some ofs ->
    get_var (evm s1) vi = ok (Varr a) ->
    valid_pointer (emem s2) (rsp + wrepr _ (i * wsize_size sz + ofs)) sz ->
    write_mem (emem s2) (rsp + wrepr _ (i * wsize_size sz + ofs)) sz v0 = ok m' ->
    WArray.set a i v0 = ok t ->
    valid_stk (evm s1) (emem s2) ->
    valid_stk (evm s1).[vi <- ok t] m'.
  Proof.
    move=> vi Hget Ha Hvmem Hm' Ht H x; have := H x.
    case Heq: find_gvar => [ ptr | // ].
    case hty: vtype => // [n' | ws]. 
    + exact: (valid_stk_arr_arr_stk Hget Heq hty Ha Hvmem Hm' Ht).
    exact: (valid_stk_word_arr_stk Hget Heq hty Ha Hvmem Hm' Ht).
  Qed.

  Lemma valid_arr_stk sz n vn v0 i ofs s1 s2 m' (a: WArray.array n) t:
    let vi := {| vtype := sarr n; vname := vn |} in
    Mvar.get m.(mstk) vi = Some ofs ->
    get_var (evm s1) vi = ok (Varr a) ->
    write_mem (emem s2) (rsp + wrepr _ (i * wsize_size sz + ofs)) sz v0 = ok m' ->
    WArray.set a i v0 = ok t ->
    valid s1 s2 ->
    valid {| emem := emem s1; evm := (evm s1).[vi <- ok t] |}
          {| emem := m'; evm := evm s2 |}.
  Proof.
    move => vi Hget Ha Hm' Ht.
    have Hvmem : valid_pointer (emem s2) (rsp + wrepr _ (i * wsize_size sz + ofs)) sz.
    + by apply/Memory.writeV; eauto.
    case => H1 H2 H3 H4 H5 hrip Hrsp Hssz H6 hg; split => //=.
    + move=> w sz' Hvmem'. 
      rewrite (H2 _ _ Hvmem') //.
      symmetry; apply: (Memory.writeP_neq Hm').
      split; eauto.
      have Hi:= WArray.set_bound Ht; have ? := wsize_size_pos sz.
      have /(_ _ _ erefl) -> := valid_map_arr_addr _ Hget; last by lia.
      have := validm (get_find_gvar Hget).
      rewrite /ptr_size /= => -[sx [/= [?] [??? ?]]].
      have [ /negP /nandP [ /ZltP| /ZltP ] ]:= H1 _ _ Hvmem'; nia. 
    + move=> w' sz'.
      by rewrite (Memory.write_valid _ _ Hm') H3.
    + move=> x Hx1 Hx2.
      rewrite Fv.setP_neq.
      apply: H4=> //.
      apply/negP=> /eqP Habs.
      by rewrite -Habs /is_in_stk Hget in Hx1.
    + by have [<- _ _] := Memory.write_mem_stable Hm'.
    + by have [_ _ <-] := Memory.write_mem_stable Hm'.
    + exact: (valid_stk_arr_stk Hget Ha Hvmem Hm' Ht).
    move=> i0 [hi1 hi2].
    rewrite (Memory.writeP_neq Hm') ?hg //.
    apply between_rsp_rip_disj.
    + rewrite (Memory.valid_align Hvmem) andbT.
      have [/=]:= validm (get_find_gvar Hget).
      rewrite /ptr_size /= => x [ [? [h1 h2 h3] ?]];subst x.
      have ? :=  wsize_size_pos sz.
      have [l1 l2]:= WArray.set_bound Ht.
      apply /andP; rewrite wunsigned_rsp_add; [ | lia | lia].
      by split;apply /ZleP; lia.
    rewrite is_align8 andbT;apply /andP; rewrite wunsigned_rip_add // wsize8;split;apply /ZleP; lia.
  Qed.

  Lemma get_var_arr n (a: WArray.array n) vm vi:
    get_var vm vi = ok (Varr a) ->
    exists vn, vi = {| vtype := sarr n; vname := vn |}.
  Proof.
    move: vi=> [vt vn] //=.
    apply: on_vuP=> //= x Hx; rewrite /to_val.
    move: vt x Hx=> [] // n' /= x Hx /Varr_inj [?];subst n' => /=.
    by exists vn.
  Qed.

  Lemma valid_stk_mem s1 s2 sz ptr off val m' m'2:
    write_mem (emem s1) (ptr + off) sz val = ok m' ->
    disjoint_zrange rsp stk_size (ptr + off) (wsize_size sz) ->
    disjoint_zrange rip glob_size (ptr + off) (wsize_size sz) ->
    write_mem (emem s2) (ptr + off) sz val = ok m'2 ->
    valid_stk (evm s1) (emem s2) ->
    valid_stk (evm s1) m'2.
  Proof.
    move=> Hm' Hbound Hgbound Hm'2 Hv x.
    have Hvalid : valid_pointer (emem s1) (ptr + off) sz.
    - by apply/Memory.writeV; eauto.
    move: Hv=> /(_ x).
    case Hget: find_gvar => [offx|//].
    case hty : vtype => // [p | ws] H.
    + move=> off' Hoff'.
      move: H=> /(_ off' Hoff') [H H']; split.
      + by rewrite (Memory.write_valid _ _ Hm'2).
      move => t a Ht v0 Hv0.
      rewrite -(H' _ a Ht v0 Hv0).
      apply: (Memory.writeP_neq Hm'2).
      split; eauto.
      have hsz := wsize_size_pos sz.
      have := validm Hget.
      rewrite hty /= => -[sx [] [?] [? h1 _ ?]]; subst sx.
      rewrite wunsigned_wptr_add; [ | nia | nia ].
      move: h1; rewrite /wptr /ptr_size; case:ifP.
      + by case: Hbound => _ _ []; rewrite wsize8; nia.
      by case: Hgbound => _ _ []; rewrite wsize8; nia.     
    case: H => [H'' H']; split.
    + by rewrite (Memory.write_valid _ _ Hm'2).
    move=> v0 Hv0; have [w h1 h2]:= H' v0 Hv0; subst v0;exists w => //.
    rewrite -h1; apply: (Memory.writeP_neq Hm'2).
    split; eauto.
    have hsz := wsize_size_pos sz; have hsz' := wsize_size_pos ws.
    have := validm Hget.
    rewrite hty /= => -[sx [] [?] [? h3 _ ?]]; subst sx.
    rewrite wunsigned_wptr_add; [ | nia | nia ].
    move: h3; rewrite /wptr /ptr_size; case:ifP.
    + by case: Hbound => _ _ []; nia.
    by case: Hgbound => _ _ []; nia. 
  Qed.

  Lemma valid_mem s1 s2 m' m'2 ptr off sz val:
    write_mem (emem s1) (ptr + off) sz val = ok m' ->
    write_mem (emem s2) (ptr + off) sz val = ok m'2 ->
    valid s1 s2 ->
    valid {| emem := m'; evm := evm s1 |} {| emem := m'2; evm := evm s2 |}.
  Proof.
    move=> Hm' Hm'2 [H1 H2 H3 H4 Hrip Hrsp H5 Hssz H6 hg].
    split=> //=.
    + move=> sz' w Hw.
      rewrite (Memory.write_valid _ _ Hm') in Hw.
      exact: H1.
    + move=> w sz'.
      rewrite (Memory.write_valid _ _ Hm') => Hw.
      exact: Memory.read_write_any_mem Hw (H2 _ _ Hw) Hm' Hm'2.
    + by move=> w sz'; rewrite (Memory.write_valid w sz' Hm') (Memory.write_valid w sz' Hm'2).
    + by have [<- _ _] := Memory.write_mem_stable Hm'2.
    + by have [_ _ <-] := Memory.write_mem_stable Hm'2.
    have Hvalid1: valid_pointer (emem s1) (ptr + off) sz.
    + apply/Memory.writeV; exists m'; exact: Hm'.
    apply: (valid_stk_mem Hm') Hm'2 H6.
    + split; eauto.
      + by case: rsp_add => /ZleP.
      by have [/negP/nandP []]:= H1 _ _ Hvalid1 => /ZltP; lia.
    split; eauto.
    + by case: rip_add => /ZleP.
    + by have [_ /negP/nandP []]:= H1 _ _ Hvalid1 => /ZltP; lia. 
    move=> i [hi1 hi2].
    rewrite (Memory.writeP_neq Hm'2) ? hg //.
    have ha := (write_mem_valid_pointer Hm').
    split.
    + by apply is_align_no_overflow; apply: (Memory.valid_align ha).
    + by apply is_align_no_overflow; apply is_align8.
    have []:= H1 _ _ ha.
    move=> /negP /andP;rewrite /is_true !Z.ltb_lt => ? /negP /andP;rewrite /is_true !Z.ltb_lt.
    rewrite wunsigned_rip_add // wsize8;lia.
  Qed.

  Lemma check_memW sz (vi : var_i) (s1 s2: estate) v v' e e':
    check_var m vi -> alloc_e m e = ok e' -> valid s1 s2 -> 
    value_uincl v v' ->
    forall s1', write_lval gd (Lmem sz vi e) v s1 = ok s1'->
    exists s2', write_lval [::] (Lmem sz vi e') v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move => Hvar He Hv Hu s1'.
    case: (Hv) => H1 H2 H3 H4 Hrip Hpstk H5 Hssz H6 hg.
    rewrite /write_lval; t_xrbindP => ptr wi hwi hwiptr ofs we he heofs w hvw.
    move => m' Hm' <- {s1'}.
    have [wi' [-> hwi']] := check_varP Hvar H4 hwi.
    rewrite /= (value_uincl_word hwi' hwiptr) /=.
    have [we' [-> hwe' /=]] := alloc_eP He Hv he.
    rewrite /= (value_uincl_word hwe' heofs) /= (value_uincl_word Hu hvw) /=.
    have : exists m2', write_mem (emem s2) (ptr + ofs) sz w = ok m2'.
    + apply: Memory.writeV; rewrite H3; apply /orP; left; apply /orP; left; apply/Memory.writeV; eauto.
    case => m2' Hm2'; rewrite Hm2' /=; eexists; split; first by reflexivity.
    exact: (valid_mem Hm').
  Qed.

  Lemma check_arrW (vi: var_i) ws (s1 s2: estate) v v' e e':
    check_var m vi -> alloc_e m e = ok e' -> valid s1 s2 -> value_uincl v v' ->
    forall s1', write_lval gd (Laset ws vi e) v s1 = ok s1'->
    exists s2', write_lval [::] (Laset ws vi e') v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    case: vi => vi ivi.
    move=> Hvar He Hv Hu s1'.
    have Hv' := Hv.
    move: Hv'=> [] H1 H2 H3 H4 Hrip Hpstk H5 Hssz H6 hg.
    apply: rbindP=> [[]] // n a Ha.
    t_xrbindP => i vali Hvali Hi v0 Hv0 t Ht vm.
    rewrite /set_var;apply: set_varP => //=;last first.
    + by move=> /is_sboolP h1 h2;elimtype False; move: h2;rewrite h1.
    move=> varr Hvarr <- <- /=.
    have Hv'0 := value_uincl_word Hu Hv0.
    have [w [-> U]] := alloc_eP He Hv Hvali.
    have [??]:= value_uincl_int U Hi; subst vali w => /=.
    rewrite /= /on_arr_var.
    have [w [->]]:= check_varP Hvar H4 Ha.
    case: w => //= n0 a0 huincl. 
    have Hvar' := Hvar; move: Hvar'=> /andP [ /andP [Hnotinstk notstk] notrip].
    rewrite Hv'0 /=.
    have Ha0' : @val_uincl (sarr n) (sarr n0) a a0 := huincl.
    have [t' -> Htt' /=]:= Array_set_uincl Ha0' Ht.
    rewrite /set_var /=.
    have Utt': value_uincl (@Varr n t) (Varr t') := Htt'.
    have [varr' [-> Uarr] /=]:= pof_val_uincl Utt' Hvarr.
    exists {| emem := emem s2; evm := (evm s2).[vi <- ok varr'] |}; split=> //.
    split=> //=.
    + exact: eq_vm_write.
    + by rewrite /get_var Fv.setP_neq. 
    + by rewrite /get_var Fv.setP_neq.
    exact: valid_stk_write_notinstk.
  Qed.
*)

  Lemma check_vfresh_lvalP x tt : check_vfresh_lval gm x = ok tt ->
     ~~ is_vrsp gm x /\ ~~ is_vrip gm x.
  Proof. rewrite /check_vfresh_lval; case: ifP => //=; case: ifP => //=. Qed.

  Lemma write_var_nin_rm v v' sm s1 s2 s1' (x:var_i) : 
    valid sm s1 s2 ->
    ~~ is_in_stk sm x ->
    ~~ is_vrsp gm x -> 
    ~~ is_vrip gm x -> 
    value_uincl v v' ->
    write_var x v s1 = ok s1' ->
    ∃ s2' : estate, write_var x v' s2 = ok s2' ∧ 
      valid (map_remove sm x) s1' s2'.
  Proof.
    move=> Hvalid Hnotinstk Hnvrsp Hnvrip Hu. 
    rewrite /write_var; apply: rbindP=> z /=; apply: set_varP;rewrite /set_var.
    + move=> t /(pof_val_uincl Hu) [t' [-> Htt']] <- [<-] /=.
      eexists;split;first reflexivity.

admit.
(*      by apply valid_set_uincl. *)
    case: x Hnotinstk Hnvrsp Hnvrip => -[tvi nvi] vii /= Hnotinstk Hnvrsp Hnvrip.
    move=> /is_sboolP ?; subst tvi => /= /to_bool_undef ?; subst v => <- [<-].
    have [-> | [b1 ->]] /=:= pof_val_undef Hu erefl;
     (eexists;split;first reflexivity).
Check valid_set_uincl.
Lemma valid_set_uincl_rm : 
  
 apply valid_set_uincl.

  Lemma alloc_lvalP sm r1 r2 v v' ty (s1 s2: estate) :
    alloc_lval gm sm r1 ty = ok r2 -> valid sm s1 s2 -> 
    type_of_val v = ty -> value_uincl v v' ->
    forall s1', write_lval gd r1 v s1 = ok s1' ->
    exists s2', write_lval [::] r2.2 v' s2 = ok s2' /\ valid r2.1 s1' s2'.
  Proof.
    move=> Hr Hv Htr Hu; move: Hr.
    case: r1=> [vi t |vi|sz vi e|sz vi e] /=.
    + move=> [] ?;subst r2 => s1' H.
      have [-> _ /=]:= write_noneP H.
      by rewrite (uincl_write_none _ Hu H); exists s2.      

    + case: vi => -[vty vin] vii /=.
      case Hget: Mvar.get => [ofs | ]; last first.
      + t_xrbindP => ? /check_vfresh_lvalP /= [ nrsp nrip] ?; subst r2 => /=.



Print map_remove.
Print keep_addrvar.
        by apply: check_varW => //=;rewrite /check_var /= nrsp nrip /is_in_stk Hget.
      case hw: is_word_type => [ sz | //].
      have := is_word_typeP hw => ? {hw};subst vty.
      case: eqP => //  hty [?];subst ty r2 => /=.
      case: (Hv) => H1 H2 H3 H4 Hrip Hpstk H5 Hssz H6 hg s1'.
      rewrite Hpstk /=; apply: rbindP=> /= vm'; apply: set_varP => //= w1 h ?[?]; subst vm' s1'.
      have [{h} w' [??] ]:= type_of_val_to_pword hty h; subst v w1.
      have /= /(_ sz w') := value_uincl_word Hu .
      rewrite truncate_word_u => -> //=.
      rewrite /zero_extend !wrepr_unsigned.
      have Hvmem: valid_pointer (emem s2) (rsp + wrepr _ ofs) sz.
      + rewrite H3; apply/orP; left; apply/orP;right. exact: valid_get_w Hget.
      have [m' Hm'] : exists m', write_mem (emem s2) (rsp + wrepr _ ofs) sz w' = ok m'.
      + by apply/Memory.writeV.
      exists {| emem := m'; evm := evm s2 |}; split.
      + by rewrite Hm' /=.
      exact: valid_var_stk Hv Hm' Hget.
  
    + case: ifP => // hc; apply: rbindP => e' ha [<-].
      by apply: (check_memW hc ha Hv Hu).

    t_xrbindP => e' ha; case Hget: Mvar.get => [ ofs | // ]; last first.
    + case hf: check_vfresh=> //=.
      have [_ hnis hnig] := check_vfreshP hf => -[<-].
      by apply: (check_arrW _ ha Hv Hu); rewrite /check_var hnis /is_in_stk Hget.
    case: ifP => // hal [<-].
    case: vi Hget => [[vty vn] vi] /= Hget. 
    case: (Hv) => H1 H2 H3 H4 hrip Hpstk H5 Hssz H6 hg s1'.    
    apply on_arr_varP => n' t' /subtypeEl [n1] /= [??];subst vty => hget.
    have ? : n1 = n'; last subst n1.
    + by move: hget; apply on_vuP => //= ? _ /Varr_inj [].
    t_xrbindP => i ve he hi vw hvw t'' haset vm hset ?;subst s1'.
    have [ve' [hve' vu]]:= alloc_eP ha Hv he.
    have [??] := value_uincl_int vu hi;subst ve ve'.
    have -> := mk_ofsP sz ofs hve'.
    rewrite Hpstk (value_uincl_word Hu hvw) /= !zero_extend_u.
    apply: set_varP hset => //= t1 []??; subst t1 vm.
    cut (exists m', 
      write_mem (emem s2) (rsp + wrepr Uptr (i * wsize_size sz + ofs)) sz vw = ok m').
    - case => m' Hm'; rewrite Hm' /=; eexists; split;first by reflexivity.
      rewrite /WArray.inject Z.ltb_irrefl.
      by have := valid_arr_stk Hget hget Hm' haset Hv; case: (t'').
    apply/Memory.writeV.
    case: (validm (get_find_gvar Hget)) => sx [[heq]]. 
    rewrite -heq /ptr_size /= => -[hofs hofs' hal' hdisj] {hi}.
    have hi:= WArray.set_bound haset.
    rewrite H3; apply/orP; left; apply/orP; right.
    have ? := wsize_size_pos sz.
    have ? := wunsigned_range rsp; have [? hpstk] := rsp_add.
    rewrite /between wunsigned_add; last by nia.
    apply/andP; split; first by apply /andP; split; apply /ZleP;nia.
    have ->: (rsp + wrepr U64 (i * wsize_size sz + ofs))%R = 
           (wrepr U64 (wsize_size sz * i) + (rsp + wrepr U64 ofs))%R.
    + by rewrite !wrepr_add Z.mul_comm; ssrring.ssring.
    by apply: is_align_array; rewrite hpstk.
  Qed.

  Lemma alloc_lvalsP (r1 r2: lvals) vs vs' ty (s1 s2: estate) :
    mapM2 bad_lval_number (alloc_lval m) r1 ty = ok r2 -> valid s1 s2 ->
    seq.map type_of_val vs = ty -> 
    List.Forall2 value_uincl vs vs' ->
    forall s1', write_lvals gd s1 r1 vs = ok s1' ->
    exists s2', write_lvals [::] s2 r2 vs' = ok s2' /\ valid s1' s2'.
  Proof.
    elim: r1 r2 ty vs vs' s1 s2=> //= [|a l IH] r2 [ | ty tys] // [ | v vs] //.
    + move=> vs' ? s2 [<-] Hvalid _ /List_Forall2_inv_l -> {vs'} s1' [] <-.
      by exists s2; split.
    move=> ? s1 s2; t_xrbindP => a' ha l' /IH hrec <-.
    move=> Hvalid [] hty htys /List_Forall2_inv_l [v'] [vs'] [->] [hv hvs] s1' s1'' ha1 hl1.
    have [s2' [hs2' vs2']]:= alloc_lvalP ha Hvalid hty hv ha1.
    have [s2'' [hs2'' vs2'']]:= hrec _ _ _ _ vs2' htys hvs _ hl1.
    by exists s2''; split => //=; rewrite hs2'.
  Qed.

  Let Pi_r s1 (i1:instr_r) s2 :=
    forall ii1 ii2 i2, alloc_i m (MkI ii1 i1) = ok (MkI ii2 i2) ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem_i SP rip s1' i2 s2' /\ valid s2 s2'.

  Let Pi s1 (i1:instr) s2 :=
    forall i2, alloc_i m i1 = ok i2 ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem_I SP rip s1' i2 s2' /\ valid s2 s2'.

  Let Pc s1 (c1:cmd) s2 :=
    forall c2,  mapM (alloc_i m) c1 = ok c2 ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem SP rip s1' c2 s2' /\ valid s2 s2'.

  Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.

  Let Pfun (m1: mem) (fn: funname) (vargs: seq value) (m2: mem) (vres: seq value) := True.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    move=> s [] // => _ s' Hv.
    exists s'; split; [exact: S.Eskip|exact: Hv].
  Qed.

  Local Lemma Hcons : sem_Ind_cons P Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc c1 /=;t_xrbindP => i' hi c' hc <- s1' hv.
    have [s2' [si hv2]]:= Hi _ hi _ hv.
    have [s3' [sc hv3]]:= Hc _ hc _ hv2.
    exists s3'; split => //.
    apply: S.Eseq; [exact: si|exact: sc].
  Qed.

  Local Lemma HmkI : sem_Ind_mkI P Pi_r Pi.
  Proof.
    move=> ii i s1 s2 _ Hi [ii' ir'] ha s1' hv.
    by have [s2' [Hs2'1 Hs2'2]] := Hi _ _ _ ha _ hv; exists s2'; split.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn P Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' hv htr Hw ii1 ii2 i2 /=.
    t_xrbindP => i' x'; apply: add_iinfoP => ha e'.
    apply: add_iinfoP => he ??? s1' hs1; subst i' i2 ii1.
    have [v1 [He' Uvv1]] := alloc_eP he hs1 hv.
    have [v1' htr' Uvv1']:= truncate_value_uincl Uvv1 htr.
    have hty := truncate_val_has_type htr.
    have [s2' [Hw' Hs2']] := alloc_lvalP ha hs1 hty Uvv1' Hw.
    by exists s2'; split=> //;apply: S.Eassgn;eauto.
  Qed.

  Local Lemma Hopn : sem_Ind_opn P Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    rewrite /sem_sopn;t_xrbindP => vs va He Hop Hw ii1 ii2 i2 /=.
    t_xrbindP => i' x'; apply: add_iinfoP => ha e'.
    apply: add_iinfoP => he ??? s1' hs1; subst i' i2 ii1.
    have [va' [He' Uvv']] := (alloc_esP he hs1 He). 
    have [w' [Hop' Uww']]:= vuincl_exec_opn Uvv' Hop.
    have [s2' [Hw' Hvalid']] := alloc_lvalsP ha hs1 (sopn_toutP Hop) Uww' Hw.
    exists s2'; split=> //.
    by apply: S.Eopn;rewrite /sem_sopn He' /= Hop'.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true P Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc ii1 ii2 i2 /=.
    t_xrbindP => i' e'; apply: add_iinfoP => he c1' hc1 c2' hc2 ??? s1' hs1.
    subst i' i2 ii2; have [b [he']]:= alloc_eP he hs1 Hse.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s2' [Hsem Hvalid']] := Hc _ hc1 _ hs1.
    by exists s2'; split=> //; apply: S.Eif_true.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false P Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc ii1 ii2 i2 /=.
    t_xrbindP => i' e'; apply: add_iinfoP => he c1' hc1 c2' hc2 ??? s1' hs1.
    subst i' i2 ii2; have [b [he']]:= alloc_eP he hs1 Hse.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s2' [Hsem Hvalid']] := Hc _ hc2 _ hs1.
    by exists s2'; split=> //; apply: S.Eif_false.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true P Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c1 e c2 _ Hc1 Hv ? Hc2 ? Hwhile ii1 ii2 i2 /=.
    t_xrbindP => i' e'; apply: add_iinfoP => he c1' hc1 c2' hc2 ??? s1' hs1.
    subst i' i2 ii2.
    have [s2' [Hsem' Hvalid']]:= Hc1 _ hc1 _ hs1.
    have [s2'' [Hsem'' Hvalid'']] := Hc2 _ hc2 _ Hvalid'.
    have := Hwhile _.
    have [|s3' [Hsem''' Hvalid''']] := (Hwhile ii1 ii1 (Cwhile a c1' e' c2') _ _ Hvalid'').
    + by rewrite /= he hc1 hc2.
    exists s3'; split=> //.
    apply: S.Ewhile_true; eauto.
    have [v' [-> ]]:= alloc_eP he Hvalid' Hv.
    by move=> /value_uincl_bool /= -/(_ _ erefl) [_ ->].    
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false P Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ Hc Hv ii1 ii2 i2 /=.
    t_xrbindP => i' e'; apply: add_iinfoP => he c1' hc1 c2' hc2 ??? s1' hs1.
    subst i' i2 ii2.
    have [s2' [Hsem' Hvalid']]:= Hc _ hc1 _ hs1.
    exists s2'; split=> //.
    apply: S.Ewhile_false; eauto.
    have [v' [-> ]]:= alloc_eP he Hvalid' Hv.
    by move=> /value_uincl_bool /= -/(_ _ erefl) [_ ->].
  Qed.

  Local Lemma Hfor : sem_Ind_for P Pi_r Pfor.
  Proof. by []. Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. by []. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P Pc Pfor.
  Proof. by []. Qed.

  Local Lemma Hcall : sem_Ind_call P Pi_r Pfun.
  Proof. by []. Qed.

  Local Lemma Hproc : sem_Ind_proc P Pc Pfun.
  Proof. by []. Qed.

  Lemma check_cP s1 c s2: sem P s1 c s2 -> Pc s1 c s2.
  Proof.
    apply (@sem_Ind P Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.
End PROOF.

Definition valid_map1 (m:Mvar.t Z) (size:Z) :=
  forall x px, Mvar.get m x = Some px -> 
     exists sx, size_of (vtype x) = ok sx /\
     [/\ 0 <= px, px + sx <= size,
      aligned_for (vtype x) px &
         forall y py sy, x != y -> 
           Mvar.get m y = Some py -> size_of (vtype y) = ok sy ->
           px + sx <= py \/ py + sy <= px].

Lemma init_mapP l sz m :
  init_map sz l = ok m -> 
  valid_map1 m sz.
Proof.
  rewrite /init_map.
  set f1 := (f in foldM f _ _ ).
  set g := (g in foldM _ _ _ >>= g). 
  have : forall p p',
    foldM f1 p l = ok p' -> 
    valid_map1 p.1 p.2 -> 0 <= p.2 ->
    (forall y py sy, Mvar.get p.1 y = Some py ->
        size_of (vtype y) = ok sy -> py + sy <= p.2) ->
    (p.2 <= p'.2 /\ valid_map1 p'.1 p'.2).
  + elim:l => [|[v pn] l Hrec] p p'//=.
    + by move=>[] <- ???;split=>//;omega.
    case:ifPn=> //= /Z.leb_le Hle.
    case: ifP => // Hal.
    case Hs : size_of=> [svp|]//= /Hrec /= {Hrec}Hrec H2 H3 H4. 
    have Hpos := size_of_pos Hs.
    case:Hrec.
    + move=> x px;rewrite Mvar.setP;case:ifPn => /eqP Heq.
      + move=> [] ?;subst;exists svp;split=>//;split => //.
        + omega. + omega.
        move=> y py sy Hne.
        by rewrite Mvar.setP_neq // => /H4 H /H ?;omega.
      move=> /H2 [sx] [Hsx] [] Hle0 Hpx Hal' Hy;exists sx;split=>//;split=>//.
      + omega.
      move=> y py sy Hne;rewrite Mvar.setP;case:eqP=> [?[]? |].
      + subst;rewrite Hs => -[] ?;subst; omega.
      by move=> Hney;apply Hy.
    + omega.
    + move=> y py sy;rewrite Mvar.setP;case:eqP=> [?[]?|].
      + subst;rewrite Hs => -[] ->;omega.
      move=> ? /H4 H /H ?;omega.
    move=> Hle2 H';split=>//;first by omega.
  move=> H;case Heq : foldM => [p'|]//=.
  case: (H _ _ Heq)=> //= Hp' Hv.
  rewrite /g; case:ifP => //= /Z.leb_le Hp [<-].
  move=> x px Hx.
  case :(Hv x px Hx) => //= sx [] Hsx [] H1 H2 H3 H4.
  by exists sx;split=>//;split=>//;omega.
Qed.

Lemma getfun_alloc oracle oracle_g (P:prog) (SP:sprog) :
  alloc_prog oracle oracle_g P = ok SP ->
  exists lg mglob, 
    [/\ init_map (Z.of_nat (size SP.(sp_globs))) lg = ok mglob,
        check_globs (p_globs P) mglob SP.(sp_globs) &
        forall fn fd,
        get_fundef (p_funcs P) fn = Some fd ->
        exists fd', 
           get_fundef SP.(sp_funcs) fn = Some fd' /\
           alloc_fd SP.(sp_rip) mglob oracle (fn, fd) = ok (fn,fd')].
Proof.
  rewrite /alloc_prog.
  case: (oracle_g P) => -[data rip] l.
  t_xrbindP => mglob; apply: add_err_msgP => heq.
  case heq1: check_globs => //; t_xrbindP => sfd hm ?; subst SP => /=.
  exists l, mglob;split => //.
  elim: (p_funcs P) sfd hm => [ | [fn1 fd1] fs hrec sfd] //=.
  t_xrbindP => -[fn2 fd2] sfd1 H [??] sfds /hrec hm ?; subst fn2 fd2 sfd.
  move=> fn2 fd2 /=.
  case: eqP => ? .
  + by move=> [?]; subst fn2 fd2; exists sfd1;rewrite H.
  by move=> /hm.
Qed.

Definition extend_mem (m1:mem) (m2:mem) (rip:pointer) (data: seq u8) :=
  let glob_size := Z.of_nat (size data) in
  [/\ wunsigned rip + glob_size <= wbase U64 /\
      (forall ofs s, is_align (rip + wrepr _ ofs) s = is_align (wrepr _ ofs) s), 
      (forall w sz, valid_pointer m1 w sz -> read_mem m1 w sz = read_mem m2 w sz),
      (forall w sz, valid_pointer m1 w sz ->
          ~((wunsigned rip <? wunsigned w + wsize_size sz) && (wunsigned w <? wunsigned rip + glob_size))),
      (forall w sz, valid_pointer m2 w sz = 
         valid_pointer m1 w sz || (between rip glob_size w sz && is_align w sz)) &
      (forall i, 
         0 <= i < glob_size ->
         read_mem m2 (rip + wrepr U64 i) U8 = ok (nth (wrepr U8 0) data (Z.to_nat i)))].

Lemma all_In (T:Type) (P: T -> bool) (l:seq T) x :
  all P l ->
  List.In x l -> P x.
Proof. by elim: l => //= x' l hi /andP [] hp /hi h -[<- | /h]. Qed.

Lemma alloc_fdP oracle oracle_g (P: prog) (SP: sprog) fn fd fd':
  alloc_prog oracle oracle_g P = ok SP ->
  get_fundef (p_funcs P) fn = Some fd ->
  get_fundef (sp_funcs SP) fn = Some fd' ->
  forall m1 va m1' vr rip, 
    sem_call P m1 fn va m1' vr ->
    forall m2, extend_mem m1 m2 rip SP.(sp_globs) ->
    (exists p, alloc_stack m2 (sf_stk_sz fd') = ok p) ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      extend_mem m1' m2' rip SP.(sp_globs) /\
      S.sem_call SP rip m2 fn va m2' vr'.
Proof.
  move=> hap get Sget. 
  have [lg [mglob [higlob hcheck hf]]]:= getfun_alloc hap.
  have [fd1 [] {hf}]:= hf _ _ get.
  rewrite Sget => -[?];subst fd1.
  rewrite /alloc_fd.
  case: (oracle (fn, fd)) => -[stk_size isp] lv.
  t_xrbindP => fd1 mstk; rewrite /add_err_fun.
  case histk : init_map => [mstk1 | //] [?]; subst mstk1.
  move=> c; apply: add_finfoP => hc.
  case: andP => // -[] /andP [] hneq hargs hres [?] ?;subst fd1 fd' => /=.
  move=> m1 vargs m1' vres rip hcall m2 hm2 [m2s ha].
  pose m := {| mstk := mstk; rsp := isp; mglob := mglob; rip := sp_rip SP |}.
  pose glob_size := Z.of_nat (size (sp_globs SP)).
  have Hstk: ptr_ok (top_stack m2s) stk_size.
  + by move: ha=> /Memory.alloc_stackP [].
  have Hglob: ptr_ok rip (Z.of_nat (size (sp_globs SP))).
  + by rewrite /ptr_ok; case hm2.
  have hv : valid_map m stk_size glob_size.
  + move=> x ofsx; rewrite /find_gvar; case:ifP => his.
    + case heq: Mvar.get => [ofsx' | // ] [?]; subst ofsx'.
      have [sx [h1 [h2 h3 h4 h5]]] := init_mapP histk heq.
      exists sx;split => //; split => //.
      + by rewrite /ptr_size his.
      move=> y py sy hny h; rewrite /is_lvar -h -/(is_lvar x) his.
      by case heq1:  Mvar.get => [a|//] -[?];subst a; apply h5.
    case heq: Mvar.get => [ofsx' | // ] [?]; subst ofsx'.
    have [sx [h1 [h2 h3 h4 h5]]] := init_mapP higlob heq.
    exists sx;split => //; split => //.
    + by rewrite /ptr_size his.
    move=> y py sy hny h; rewrite /is_lvar -h -/(is_lvar x) his.
    by case heq1:  Mvar.get => [a|//] -[?];subst a; apply h5.
  have hvalid : valid P m stk_size (top_stack m2s) (Z.of_nat (size (sp_globs SP))) rip (sp_globs SP) 
                {| emem := m1; evm := vmap0 |} 
                {| emem := m2s; evm := vmap0.[vrsp m <- ok (pword_of_word (top_stack m2s))]
                                            .[vrip m <- ok (pword_of_word rip)] |}.
  + case: hm2 => halign2 hread_eq hdisj hval hglob.
    have [hin hread_eqs hvals hal hdisjs hca htop]:= Memory.alloc_stackP ha.
    constructor => //=.
    + move=> w sz hw; split; last by apply hdisj.
      by have := hdisjs w sz; rewrite hval hw /= => /(_ erefl) -[] h; apply /negP /nandP;
        [left|right];apply /ZltP; lia.
    + by move=> w sz hw; rewrite (hread_eq _ _ hw) hread_eqs // hval hw.
    + by move=> w sz; rewrite hvals hval -orbA (orbC (_ && _)) orbA.
    + by move=> x hnin hnrsp hnrip;rewrite !Fv.setP_neq // eq_sym.
    + by rewrite /get_var Fv.setP_eq.
    + rewrite /get_var Fv.setP_neq ? Fv.setP_eq //.
      by apply /eqP => -[?]; subst isp;move: hneq; rewrite eq_refl.
    + by rewrite htop eq_refl.
    + move=> x; rewrite /find_gvar.
      case: ifP => his; case heq: Mvar.get => [ofs | //].
      + have := init_mapP histk heq. 
        case Htype: (vtype (gv x))=> [| |n| sz] // [sx /= [[?] [h1 h2 h3 h4]]]; subst sx.
        + move=> off hoff; rewrite hvals; split.
          + apply /orP; right; rewrite is_align8 andbT.
            rewrite /between wsize8 /ptr_size /wptr his (wunsigned_rsp_add Hstk); [ | nia | nia ].
            by apply/andP; split; apply/ZleP; nia.
          move=> s' a; rewrite /get_gvar his /get_var Fv.get0 /on_vu /pundef_addr Htype /= => hok.
          by have /Varr_inj [e ?]:= ok_inj hok; subst s' a; rewrite WArray.get0.
        split.
        + rewrite hvals; apply /orP; right.
          have heq2 : v_var (gv x) = {| vtype := sword sz; vname := vname (gv x) |}.
          + by case: (v_var (gv x)) Htype => /= ?? ->.
          rewrite heq2 in heq; have := valid_get_w Hstk Hglob hv heq.
          by rewrite /wptr his.
        by move=> ?;rewrite /get_gvar his /get_var Fv.get0 /on_vu /pundef_addr Htype.
      have := init_mapP higlob heq. 
      case Htype: (vtype (gv x))=> [| |n| sz] // [sx /= [[?] [h1 h2 h3 h4]]]; subst sx.
      + move=> off hoff; rewrite hvals.
        have hvalid : valid_pointer m2 (wptr (top_stack m2s) rip x + wrepr U64 (off + ofs)) U8.
        + rewrite hval; apply /orP; right; rewrite is_align8 andbT.
          rewrite /between wsize8 /ptr_size /wptr his (wunsigned_rip_add Hglob); [ | nia | nia ].
          by apply/andP; split; apply/ZleP; nia.
        split; first by rewrite hvalid.
        move=> s' a; rewrite /get_gvar his /get_global /get_global_value.
        case heq1 : xseq.assoc => [[ | n' a'] //= | //]; case: eqP => //.
        rewrite Htype => -[?] heq2; subst n'; have /Varr_inj [e ?] := ok_inj heq2; subst n a => /=.
        have := all_In hcheck (xseq.assoc_mem' heq1).
        rewrite /check_glob /= heq => /andP [hle /allP hall] v hget. 
        have := hall (Z.to_nat off); rewrite mem_iota /= Z2Nat.id; last by lia.
        rewrite hget.
        match goal with |- (?A -> _) -> _ => have hh: A end.
        + by apply /ltP; case: hoff => ? /Z2Nat.inj_lt;apply.
        move=> /(_ hh) {hh} /eqP <-.
        rewrite /wptr his -hread_eqs;last by move: hvalid; rewrite /wptr his.
        rewrite hglob; last by lia. 
        rewrite Z.add_comm Z2Nat.z2nD;first last.
        + by apply /lezP;rewrite -ssrring.z0E;lia.
        + by apply /lezP;rewrite -ssrring.z0E;lia. 
        by rewrite -nth_drop wrepr0.
      rewrite /valid_ptr_word /get_gvar /wptr his.
      have hvalid : valid_pointer m2 (rip + wrepr U64 ofs) sz.
      + rewrite hval; apply /orP; right.
        case: halign2 => hh1 hh2; rewrite /between hh2 h3 andbT.
        rewrite (wunsigned_rip_add Hglob) //; last by have := @wsize_size_pos sz;lia.
        apply /andP;split; apply /ZleP;lia.
      rewrite hvals hvalid;split => // v. 
      rewrite -hread_eqs // /get_global /get_global_value Htype.
      case heq1 : xseq.assoc => [[ sz' w| ] //= | //];case: eqP => // -[?] [?]; subst sz' v.
      exists w => //; rewrite Memory.readP /CoreMem.read.
      have := validr_valid_pointer m2 (rip + wrepr U64 ofs)%R sz.
      rewrite hvalid => /is_okP => -[? ->] /=.
      have := all_In hcheck (xseq.assoc_mem' heq1).
Opaque Z.to_nat.
      rewrite /check_glob heq /= => /andP [hh1 /eqP hh2];subst w.
      f_equal; f_equal.
      rewrite /CoreMem.uread; apply: (@eq_from_nth _ (wrepr U8 0)).
      have hw := @le0_wsize_size sz.
      + rewrite size_map size_ziota size_take size_drop.
        case: ifPn => // /ltP; rewrite Nat2Z.inj_lt Z2Nat.id // Nat2Z.n2zB; last first. 
        rewrite -(Nat2Z.id (size _)); apply /leP; rewrite -Z2Nat.inj_le; lia.
        rewrite -subZE Z2Nat.id // => hh. 
        have -> : (wsize_size sz) = Z.of_nat (size (sp_globs SP)) - ofs by lia.
        by rewrite Z2Nat.inj_sub // Nat2Z.id.
      move=> i; rewrite size_map size_ziota => hi.
      rewrite (nth_map 0) ?size_ziota // nth_take // nth_drop nth_ziota // Memory.addP /=.
      rewrite -GRing.addrA -wrepr_add.
      move /ltP: hi; rewrite Nat2Z.inj_lt Z2Nat.id // => hi.
      have : 0 <= ofs + Z.of_nat i ∧ ofs + Z.of_nat i < Z.of_nat (size (sp_globs SP)) by lia.
      move=> /hglob; rewrite Memory.readP /CoreMem.read CoreMem.uread8_get. 
      t_xrbindP => ?? ->; rewrite Z2Nat.inj_add //; last by apply Zle_0_nat.
      by rewrite Nat2Z.id addP.
    move=> i [hi1 hi2]; rewrite -hread_eqs; first by apply hglob.
    rewrite hval is_align8 andbT;apply /orP;right.
    apply /andP;rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP; lia.
Transparent Z.to_nat.
  inversion_clear hcall.
  move: H;rewrite get => -[?];subst f.
  have uvargs0 : List.Forall2 value_uincl vargs0 vargs0.
  + by apply List_Forall2_refl.
  have [s2 [hwargs hvalid2 ]]:= check_varsW hargs hvalid uvargs0 H1.
  have hdisj : 0 < stk_size -> 0 < Z.of_nat (size (sp_globs SP)) ->
       ((wunsigned (top_stack m2s) + stk_size <=? wunsigned rip)
                || (wunsigned rip + Z.of_nat (size (sp_globs SP)) <=? wunsigned (top_stack m2s))).
  + case: hm2 =>  _ _ _ hvm2 _ hss hsg. 
    have [_ _ _ _ hh _ _]:= Memory.alloc_stackP ha.
    have /hh : valid_pointer m2 rip U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      by rewrite /between Z.leb_refl /= wsize8; apply /ZleP; lia.
    have /hh : valid_pointer m2 (rip + wrepr Uptr (Z.of_nat (size (sp_globs SP)) - 1)) U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between (wunsigned_rip_add Hglob); [ | lia | lia]. 
      by rewrite wsize8; apply /andP; split; apply /ZleP; lia.
    rewrite wsize8 (wunsigned_rip_add Hglob); [ | lia | lia]. 
    move=> a1 a2;apply /orP.
    rewrite /is_true !Z.leb_le. 
    case: a1; first by lia.
    case: a2; last by lia.
    move=> ??.
    have u1 : stk_size < Z.of_nat (size (sp_globs SP)) by lia.
    have /hh : valid_pointer m2 (top_stack m2s) U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      by rewrite /between wsize8; apply /andP; split; apply /ZleP; lia. 
    by rewrite wsize8; lia.   
  have [s3 [hssem hvalid3]] := check_cP (P:= P) SP Hstk Hglob hv hdisj H2 hc hvalid2.
  have [vres1 [H1' uincl1]]:= check_varsP hres (valid_vm hvalid3) H3.
  have [vres2 htr uincl2]:= mapM2_truncate_val H4 uincl1.
  exists (free_stack (emem s3) stk_size), vres2.
  split => //.
  split.
  + have /Memory.free_stackP [h1 h2 h3 h4 h5]: frame_size (emem s3) (top_stack (emem s3)) = Some stk_size.
    + by rewrite (valid_top hvalid3) (valid_frame hvalid3).
    have [u1 u2 u3 u4 u5] := hm2.
    have vdisj: forall w sz, valid_pointer m1' w sz ->  disjoint_zrange (top_stack m2s) stk_size w (wsize_size sz).
    + move=> w sz hw;have [ /negP /andP] := valid_disj hvalid3 hw.
      rewrite {1 2}/is_true !Z.ltb_lt => ??; split.
      + by apply /ZleP; case: Hstk.
      + by apply is_align_no_overflow; apply (Memory.valid_align hw).
      lia.
    split => //.
    + move=> w sz hw.
      rewrite (valid_eq hvalid3) // h1 // h2 (valid_def hvalid3) /= hw /=; split=> //.
      by rewrite (valid_top hvalid3);apply vdisj.
    + by move=> w sz /(valid_disj hvalid3) [].
    + move=> w sz. 
      apply Bool.eq_iff_eq_true; have := h2 w sz.
      rewrite {1}/is_true => ->.
      rewrite (valid_def hvalid3) /= (valid_top hvalid3); split.
      + move=> [] /orP [].
        + move=> /orP [-> //| ].
          move=> /andP [] /andP [] /ZleP ? /ZleP ?? [???].
          by have := wsize_size_pos sz;lia.
        by move=> /andP [-> ->] /=;rewrite orbT.         
      move=> /orP [ hw | /andP [hb hal]]. 
      + by rewrite hw /=;split => //; apply: vdisj.
      rewrite hb hal !orbT;split => //; split.
      + by apply /ZleP; case: Hstk.
      + by apply is_align_no_overflow.
      have : valid_pointer m2 w sz by rewrite u4 hb hal /= orbT.
      have [_ _ _ _ h _ _]:= Memory.alloc_stackP ha.
      by move=> /h; lia.
    move=> i [hi1 hi2].
    rewrite -h1.
    + by rewrite (valid_glob hvalid3).
    rewrite h2 (valid_top hvalid3) (valid_def hvalid3) is_align8 !andbT; split.
    + apply /orP;right; apply /andP.
      by rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP;lia.
    split.
    + by apply /ZleP; case: Hstk.
    + by apply is_align_no_overflow; apply is_align8.
    have :  valid_pointer m2 (rip + wrepr U64 i) U8.
    + rewrite u4 is_align8 andbT; apply /orP;right.
      by apply /andP; rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP;lia.
    have [_ _ _ _ h _ _]:= Memory.alloc_stackP ha.
    by move=> /h;lia.
  econstructor;eauto.
  + by rewrite /=; f_equal; f_equal; f_equal; f_equal; rewrite /pword_of_word;f_equal; f_equal;
      apply (Eqdep_dec.UIP_dec Bool.bool_dec).
  by have -> : {| emem := emem s3; evm := evm s3 |} = s3 by case: (s3).
Qed.

Definition alloc_ok SP fn m1 :=
  forall fd, get_fundef (sp_funcs SP) fn = Some fd ->
  exists p, alloc_stack m1 (sf_stk_sz fd) = ok p.

Lemma alloc_progP oracle oracle_g (P: prog) (SP: sprog) fn:
  alloc_prog oracle oracle_g P = ok SP ->
  forall m1 va m1' vr rip, 
    sem_call P m1 fn va m1' vr ->
    forall m2, extend_mem m1 m2 rip SP.(sp_globs) ->
    alloc_ok SP fn m2 ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      extend_mem m1' m2' rip SP.(sp_globs) /\
      S.sem_call SP rip m2 fn va m2' vr'.
Proof.
  move=> Hcheck m1 va m1' vr rip hsem m2 he ha.
  have [fd hget]: exists fd, get_fundef (p_funcs P) fn = Some fd.
  + by case: hsem => ??? fd *;exists fd.
  have [lg [mglob [higlob hcheck hf]]]:= getfun_alloc Hcheck.
  have [fd' [hgetS ?]]:= hf _ _ hget.
  by apply: (alloc_fdP Hcheck hget hgetS hsem he (ha _ hgetS)).
Qed.
