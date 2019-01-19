(**********)
(* erc-vc-extract is a OCaml written program that 
 * extracts verification conditions of an annotated ERC program
 * written by Sewon Park @ KAIST (2019).
 *
 * initialcoq.ml: the file is a part of erc-vc-extract contains 
 * text that to be contained in *_prec.v Coq file declaring
 * definitions and few lemmas about precision embedding
*)
let coqprec : string = 
"
(*  Sewon Park @ SoC, KAIST 2018 
 *  The Coq file contains theorems which need to be proved
 *  in order to verify your ERC program.
 *  The first part contains the construction and simple theorems
 *  about precision embedding.
 *
 *  At the end of the file you can find theorems that need to be proved
 *  generated by mechanincally applying the Weakest Precondition Calculus
 *  Skip to line 265 to see the theorems.
 *)

Require Import Coq.Reals.Reals.
Require Import ZArith.
Require Import Coq.ZArith.Zorder.
Require Import Coq.PArith.Pnat.
Require Import Coq.NArith.Nnat.
Open Scope R_scope.


(***********************************)
(* Precision embedding
 * This file formalize the `precision embedding' as a function prec : Z -> R and 
 * proves its properties such as 
 * - prec is a group homomorphism: prec (z_1 + z_2) = prec z_1 * prec z_2
 * - prec is always positive: prec z > 0
 *)

Section prec_embedding.

  Fixpoint prec_nat (n:nat) : R :=
  match n with
  | O => 1
  | S n => 2 * prec_nat n
  end.

  Definition prec (z:Z) : R :=
  match z with
  | 0%Z => 1
  | Zpos n => prec_nat (Pos.to_nat n)
  | Zneg n => 1 */ (prec_nat (Pos.to_nat n))
  end.

  Lemma real_obvious_1 : 1>0.
  Proof.
    intuition.
  Qed.  
  Lemma real_obvious_2 : 2>0.
  Proof.
    intuition.
  Qed.  
  Lemma real_obvious_3 : 2+1=3.
  Proof.
    ring.
  Qed.

  Lemma prec_nat_pos : forall n : nat, prec_nat n > 0.
  Proof.
    intuition; induction n; intuition; simpl.
    pose proof (Rmult_gt_compat_l 2 (prec_nat n) 0 real_obvious_2 IHn).
    rewrite (Rmult_0_r 2) in H.
    exact H.
  Qed.

  Lemma prec_pos : forall z : Z, prec z > 0.
  Proof.
    intro z; case z.
    (* case 1: z = 0 *)
    intuition.
    (* case 2: z > 0 *)
    intro p; simpl.
    exact (prec_nat_pos (Pos.to_nat p)).
    (* case 3: z <0 *)
    intro p; simpl.
    pose proof (Rmult_gt_compat_l (/ prec_nat (Pos.to_nat p)) 1 0 (Rlt_gt 0 (/ prec_nat (Pos.to_nat p)) (Rinv_0_lt_compat (prec_nat (Pos.to_nat p)) (Rgt_lt (prec_nat (Pos.to_nat p)) 0 (prec_nat_pos (Pos.to_nat p))))) real_obvious_1).
    rewrite (Rmult_0_r (/ prec_nat (Pos.to_nat p))) in H.
    rewrite (Rmult_comm).
    exact H.
  Qed.

  Lemma prec_le_0 : forall z:Z, (z<=0)%Z -> prec (z) = 1 */ prec_nat ( Z.to_nat (-z)%Z ).
  Proof.
    intros z H.
    induction z; simpl; auto.
    rewrite Rinv_1; intuition.
    destruct H; simpl; intuition.
  Qed.

  Lemma prec_lt_0 : forall z:Z, (z<0)%Z -> prec (z) = 1 */ prec_nat ( Z.to_nat (-z)%Z ).
  Proof.
    intros z H.
    induction z; simpl; auto.
    rewrite Rinv_1; intuition.
    pose proof (Zgt_pos_0 p).
    contradict H; intuition.
  Qed.

  Lemma prec_ge_0 : forall z:Z, (z >= 0)%Z -> prec (z) = prec_nat (Z.to_nat(z)).
  Proof.
    intros z H.
    induction z; simpl; auto.
    contradict H; pose proof (Zlt_neg_0 p); intuition.
  Qed.

  Lemma prec_gt_0 : forall z:Z, (z > 0)%Z -> prec (z) = prec_nat (Z.to_nat(z)).
  Proof.
    intros z H.
    induction z; simpl; auto.
    contradict H; pose proof (Zlt_neg_0 p); intuition.
  Qed.

  Lemma prec_nat_mult : forall  z1 z2 : nat, prec_nat (z1 + z2) = prec_nat z1 * prec_nat z2.
  Proof.
    intros z1 z2.
    induction z1; simpl; intuition.
    rewrite  IHz1; intuition.
  Qed.

  Lemma prec_mult_neg_pos : forall z1 z2 : Z, (z1 < 0)%Z -> (z2 >0)%Z -> prec (z1 + z2) = prec z1 * prec z2.
  Proof.
    intros z1 z2 H H0.
    case (Ztrichotomy_inf (z1 + z2) 0).
    (* case 1: z1+z2<0 *)
    intuition.
    assert (a0 : (z1+z2<0)%Z).
      intuition.
    rewrite (prec_lt_0 (z1+z2) a0).
    rewrite Rmult_1_l.
    assert (prec_nat (Z.to_nat (- (z1 + z2))) <> 0).
      exact (Rgt_not_eq (prec_nat (Z.to_nat (- (z1 + z2)))) 0 (prec_nat_pos (Z.to_nat (- (z1 + z2)))))  .
    assert (prec_nat (Z.to_nat (- z1)) <> 0).
      exact (Rgt_not_eq (prec_nat (Z.to_nat (- z1))) 0 (prec_nat_pos (Z.to_nat (- z1))))  .
    rewrite (prec_lt_0 z1 H).
    rewrite (prec_gt_0 z2 H0).
    rewrite Rmult_1_l.
    apply (Rmult_eq_reg_r (prec_nat (Z.to_nat (- (z1 + z2)))) (/prec_nat (Z.to_nat (- (z1 + z2)))) (/ prec_nat (Z.to_nat (- z1)) * prec_nat (Z.to_nat z2)) ).
    rewrite (Rinv_l (prec_nat (Z.to_nat (- (z1 + z2)))) H1).
    apply (Rmult_eq_reg_l (prec_nat (Z.to_nat (- z1))) 1 (/ prec_nat (Z.to_nat (- z1)) * prec_nat (Z.to_nat z2) * prec_nat (Z.to_nat (- (z1 + z2)))) ).
    rewrite <- (Rmult_assoc).
    rewrite <- (Rmult_assoc).
    rewrite (Rinv_r (prec_nat (Z.to_nat (- z1))) H2).
    rewrite Rmult_1_l;   rewrite Rmult_1_r.
    rewrite <- prec_nat_mult.
    rewrite <- Z2Nat.inj_add.
    assert (- z1 = z2 + - (z1 +z2))%Z.
      intuition.
    rewrite H3.
    intuition.
    intuition.
    intuition.
    trivial.
    trivial.

    (* case 2: z1+z1 = 0 *)
    rewrite b; simpl.
    assert (- z1 = z2)%Z.
      intuition.
    pose proof (prec_nat_pos (Z.to_nat z2)).
    apply Rgt_not_eq in H2.
    rewrite (prec_lt_0 z1 H).
      rewrite (prec_gt_0 z2 H0).
    rewrite Rmult_1_l.
    rewrite  H1.
    rewrite (Rinv_l (prec_nat (Z.to_nat ( z2))) H2).
    intuition.
    
    (* case 3: z1+z2>0 *)
    intuition.
    rewrite prec_gt_0.
    pose proof (prec_nat_pos (Z.to_nat (- z1))).
    apply Rgt_not_eq in H1.
    rewrite (prec_lt_0 z1 H).
    rewrite (prec_gt_0 z2 H0).
    rewrite Rmult_1_l.  
    apply (Rmult_eq_reg_l (prec_nat (Z.to_nat (- z1))) (prec_nat (Z.to_nat (z1 + z2))) (/ prec_nat (Z.to_nat (- z1)) * prec_nat (Z.to_nat z2))).
    rewrite <- Rmult_assoc.
    rewrite (Rinv_r (prec_nat (Z.to_nat ( - z1))) H1).
    rewrite Rmult_1_l.
    rewrite  <- prec_nat_mult.
    rewrite <- Z2Nat.inj_add.
    assert (- z1 + (z1 +z2) = z2)%Z.
      intuition.
    rewrite H2.
    intuition.
    intuition.
    intuition.
    trivial.
    trivial.
  Qed.

  Lemma prec_mult : forall z1 z2 : Z, prec (z1 + z2) = prec z1 * prec z2.
  Proof.
    intuition.
    case (Ztrichotomy_inf z1 0).
    intuition.
    case (Ztrichotomy_inf z2 0).
    intuition.
    assert (z1+z2<0)%Z.
      intuition.
    (* case 1: z1, z2<0 *)
    rewrite (prec_lt_0 (z1 + z2) H).
    rewrite (prec_lt_0 (z1) a).
    rewrite (prec_lt_0 (z2) a0).
    repeat rewrite Rmult_1_l.
    rewrite <- (Rinv_mult_distr (prec_nat (Z.to_nat (- z1))) (prec_nat (Z.to_nat (- z2))) (Rgt_not_eq (prec_nat (Z.to_nat (- z1))) 0 (prec_nat_pos (Z.to_nat (- z1)))) (Rgt_not_eq (prec_nat (Z.to_nat (- z2))) 0 (prec_nat_pos (Z.to_nat (- z2))))).
    rewrite <- prec_nat_mult.
    rewrite <- Z2Nat.inj_add.
    assert (-(z1+z2) = -z1+-z2)%Z.
      intuition.
    rewrite H0.
    intuition.
    intuition.
    intuition.
    (* case 2: z1<0, z2=0 *)
    rewrite b; simpl.
    rewrite Rmult_1_r.
    rewrite Z.add_0_r.
    intuition.
    (* case 3: z1 <0, z2 >0 *)
    intuition.
    exact (prec_mult_neg_pos z1 z2 a g).
    (* case 4: z1 = 0 *)
    rewrite b; simpl; intuition.
    intuition.
    case (Ztrichotomy_inf z2 0); intuition.
    (* case 5: z1 > 0, z2 < 0 *)
    rewrite Z.add_comm.
    rewrite Rmult_comm.
    exact (prec_mult_neg_pos z2 z1 a g).
    (* case 6: z1 > 0, z2 = 0 *)
    rewrite b; simpl.
    rewrite Rmult_1_r.
    rewrite Z.add_0_r.
    intuition.
    (* case 7: z1 >0, z2 > 0 *)
    intuition.  
    assert (z1+z2>0)%Z.
      intuition.
    repeat rewrite prec_gt_0.
    rewrite <- prec_nat_mult.
    rewrite <- Z2Nat.inj_add.
    intuition.
    intuition.
    intuition.   
    intuition.  
    intuition.  
    intuition.   
  Qed.

  Lemma prec_div : forall z1 z2 : Z, prec(z1 - z2) = prec z1 */ prec z2.
  Proof.
    intros z1 z2.
    pose proof (Rmult_eq_compat_r (/ prec z2) (prec (z1 - z2) * (prec z2)) (prec z1)).
    rewrite (Rmult_assoc (prec (z1 - z2)) (prec z2) (/ prec z2)) in H.
    rewrite (Rinv_r (prec z2) (Rgt_not_eq (prec z2) 0 (prec_pos z2))) in H.
    rewrite (Rmult_1_r (prec (z1 - z2))) in H.
    apply H.
    rewrite <- (prec_mult (z1 - z2) z2).
    assert (z_triv : (forall z1 z2 : Z, (z1 - z2 + z2 = z1)%Z)).
      intuition.
    rewrite (z_triv z1 z2).  
    trivial.
  Qed.
End prec_embedding."

let fmatter : string =
"
(***********)
(*
 *  This is a Coq source code generated by ERC-wp-calc.
 *  ERC-wp-calc is a program extracts correctness conditions written by Sewon Park @ KAIST.
 *  If you see the message it means that the extraction program is at its stage of prototype.
 *  Any feedback or bug report will be appreciated! :)
 *)

(***********)
(*
 *  The program uses ***_prec.v which contains definition of prec (precision embedding) function and
 *  some may useful lemmas and their proofs:
 *
 * - prec : Z -> R such that prec z means 2^z
 * - Lemma prec_pos : forall z : Z, prec z > 0.
 * - Lemma prec_mult : forall z1 z2 : Z, prec (z1 + z2) = prec z1 * prec z2.
 * - Lemma prec_div : forall z1 z2 : Z, prec(z1 - z2) = prec z1 */ prec z2.
 *
 *  ***_prec.v can be loaded after compiling it \"coqc ***_prec.v\"
 *)
 "


