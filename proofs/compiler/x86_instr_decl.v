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


(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require oseq.
Require Import ZArith utils strings low_memory word sem_type global oseq.
Import Utf8 Relation_Operators.
Import Memory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import x86_decl.

(* -------------------------------------------------------------------- *)

Variant asm_op : Type := 
  (* Data transfert *)
| MOV    of wsize              (* copy *)
| MOVSX  of wsize & wsize      (* sign-extend *)
| MOVZX  of wsize & wsize      (* zero-extend *)
| CMOVcc of wsize              (* conditional copy *)

  (* Arithmetic *)
| ADD    of wsize                  (* add unsigned / signed *)
| SUB    of wsize                  (* sub unsigned / signed *)
| MUL    of wsize                  (* mul unsigned *)
| IMUL   of wsize                             (* mul signed with truncation *)
| IMULr  of wsize   (* oprd * oprd *)         (* mul signed with truncation *)
| IMULri of wsize   (* oprd * oprd * imm *)   (* mul signed with truncation *)

| DIV    of wsize                        (* div unsigned *)
| IDIV   of wsize                        (* div   signed *)
| CQO    of wsize                               (* CWD CDQ CQO: allows sign extention in many words *)
| ADC    of wsize                 (* add with carry *)
| SBB    of wsize                 (* sub with borrow *)

| NEG	   of wsize 	                      (* negation *)

| INC    of wsize                         (* increment *)
| DEC    of wsize                         (* decrement *)

  (* Flag *)
| SETcc                           (* Set byte on condition *)
| BT     of wsize                  (* Bit test, sets result to CF *)

  (* Pointer arithmetic *)
| LEA    of wsize              (* Load Effective Address *)

  (* Comparison *)
| TEST   of wsize                  (* Bit-wise logical and CMP *)
| CMP    of wsize                  (* Signed sub CMP *)


  (* Bitwise logical instruction *)
| AND    of wsize  (* bit-wise and *)
| ANDN   of wsize  (* bit-wise andn *)
| OR     of wsize  (* bit-wise or  *)
| XOR    of wsize  (* bit-wise xor *)
| NOT    of wsize  (* bit-wise not *)

  (* Bit shifts *)
| ROR    of wsize    (* rotation / right *)
| ROL    of wsize    (* rotation / left *)
| SHL    of wsize    (* unsigned / left  *)
| SHR    of wsize    (* unsigned / right *)
| SAL    of wsize    (*   signed / left; synonym of SHL *)
| SAR    of wsize    (*   signed / right *)
| SHLD   of wsize    (* unsigned (double) / left *)
| SHRD   of wsize    (* unsigned (double) / right *)

| BSWAP  of wsize                     (* byte swap *)

  (* SSE instructions *)
| MOVD     of wsize 
| VMOVDQU  `(wsize) 
| VPAND    `(wsize) 
| VPANDN   `(wsize) 
| VPOR     `(wsize) 
| VPXOR    `(wsize) 
| VPADD    `(velem) `(wsize) 
| VPSUB    `(velem) `(wsize) 
| VPMULL   `(velem) `(wsize) 
| VPMULU   `(wsize) 
| VPEXTR   `(wsize)
| VPINSR   `(velem) 
| VPSLL    `(velem) `(wsize) 
| VPSRL    `(velem) `(wsize) 
| VPSRA    `(velem) `(wsize) 
| VPSLLV   `(velem) `(wsize) 
| VPSRLV   `(velem) `(wsize) 
| VPSLLDQ  `(wsize) 
| VPSRLDQ  `(wsize) 
| VPSHUFB  `(wsize) 
| VPSHUFD  `(wsize)
| VPSHUFHW `(wsize)
| VPSHUFLW `(wsize)
| VPBLENDD `(wsize) 
| VPBROADCAST of velem & wsize 
| VBROADCASTI128 
| VPUNPCKH `(velem) `(wsize) 
| VPUNPCKL `(velem) `(wsize) 
| VEXTRACTI128 
| VINSERTI128 
| VPERM2I128 
| VPERMQ 
.

Require Import x86_instr_t.
(* -------------------------------------------------------------------- *)

Definition check_opdr a1 := 
  match a1 with
  | Imm _ _ | Glob _ | Reg _  | Adr _  => true
  | _ => false
  end.
  
Definition check_ri a1 := 
  match a1 with
  | Imm _ _  | Reg _  => true
  | _ => false
  end.

Definition check2_regmemi (args: list asm_arg) := 
  match args with
  | [::Reg _; a1] => check_opdr a1
  | [::Adr _; a1] => check_ri a1
  | _               => false
  end.

Definition MOV_desc sz := 
  {| id_msb_flag := MSB_CLEAR; 
     id_in  := [:: (E sz 1, sword sz) ];
     id_out := [:: (E sz 0, sword sz) ];
     id_semi := @x86_MOV sz;
     id_check := check2_regmemi |}.

Definition instr_desc (o:asm_op) : instr_desc_t := 
  match o with
  | MOV sz => MOV_desc sz
  | _ => MOV_desc U8
  end.
