From Coq Require Import Strings.String.
Require Import Maps.
Require Import UVM.

(** * Linear Modality Ringoid *)
Inductive linear_mod :=
  | lm0
  | lm1
  | lm_omega.

Definition ladd (a b: linear_mod): linear_mod :=
  match a with
  | lm0 => match b with
          | lm0 => lm0
          | lm1 => lm1
          | lm_omega => lm_omega
          end
  | lm1 => match b with
          | lm0 => lm1
          | lm1 => lm_omega
          | lm_omega => lm_omega
          end
  | lm_omega => match b with
               | lm0 => lm_omega
               | lm1 => lm_omega
               | lm_omega => lm_omega
               end
  end.

Definition lmul (a b: linear_mod): linear_mod :=
  match a with
  | lm0 => match b with
          | lm0 => lm0
          | lm1 => lm0
          | lm_omega => lm0
          end
  | lm1 => match b with
          | lm0 => lm0
          | lm1 => lm1
          | lm_omega => lm_omega
          end
  | lm_omega => match b with
               | lm0 => lm0
               | lm1 => lm_omega
               | lm_omega => lm_omega
               end
  end.

Definition lmeet (a b: linear_mod): linear_mod :=
  match a with
  | lm0 => match b with
          | lm0 => lm0
          | lm1 => lm_omega
          | lm_omega => lm_omega
          end
  | lm1 => match b with
          | lm0 => lm_omega
          | lm1 => lm1
          | lm_omega => lm_omega
          end
  | lm_omega => match b with
               | lm0 => lm_omega
               | lm1 => lm_omega
               | lm_omega => lm_omega
               end
  end.

Lemma ladd_comm: forall a b, ladd a b = ladd b a.
Proof. destruct a, b; auto. Qed.

Lemma ladd_assoc: forall a b c, ladd a (ladd b c) = ladd (ladd a b) c.
Proof. destruct a, b, c; auto. Qed.

Lemma lzero_add_idr: forall a, ladd a lm0 = a.
Proof. destruct a; auto. Qed.

Lemma lzero_add_idl: forall a, ladd lm0 a = a.
Proof. destruct a; auto. Qed.

Lemma lmul_assoc: forall a1 a2 a3, lmul a1 (lmul a2 a3) = lmul (lmul a1 a2) a3.
Proof. destruct a1, a2, a3; auto. Qed.

Lemma lone_mul_idr: forall a, lmul a lm1 = a.
Proof. destruct a; auto. Qed.

Lemma lone_mul_idl: forall a, lmul lm1 a = a.
Proof. destruct a; auto. Qed.

Lemma lmul_add_distl: forall p q r, lmul p (ladd q r) = ladd (lmul p q) (lmul p r).
Proof. destruct p, q, r; auto. Qed.

Lemma lmul_add_distr: forall p q r, lmul (ladd p q) r = ladd (lmul p r) (lmul q r).
Proof. destruct p, q, r; auto. Qed.

Lemma lzero_absorbl: forall a, lmul a lm0 = lm0.
Proof. destruct a; auto. Qed.

Lemma lzero_absorbr: forall a, lmul lm0 a = lm0.
Proof. destruct a; auto. Qed.

Lemma lmeet_assoc: forall a1 a2 a3, lmeet a1 (lmeet a2 a3) = lmeet (lmeet a1 a2) a3.
Proof. destruct a1, a2, a3; auto. Qed.

Lemma lmeet_comm: forall a1 a2, lmeet a1 a2 = lmeet a2 a1.
Proof. destruct a1, a2; auto. Qed.

Lemma lmeet_idem: forall a1 a2, lmeet a1 (lmeet a1 a2) = lmeet a1 a2.
Proof. destruct a1, a2; auto. Qed.

Lemma lmul_meet_distl: forall p q r, lmul p (lmeet q r) = lmeet (lmul p q) (lmul p r).
Proof. destruct p, q, r; auto. Qed.

Lemma lmul_meet_distr: forall p q r, lmul (lmeet p q) r = lmeet (lmul p r) (lmul q r).
Proof. destruct p, q, r; auto. Qed.

Lemma ladd_meet_dist: forall p q r, ladd (lmeet p q) r = lmeet (ladd p r) (ladd q r).
Proof. destruct p, q, r; auto. Qed.

Instance r_linear_mod : Ringoid linear_mod :=
 {
   r0 := lm0;
   r1 := lm1;
   radd := ladd;
   rmul := lmul;
   rmeet := lmeet;

   radd_comm       := ladd_comm;
   radd_assoc      := ladd_assoc;
   rzero_add_idr   := lzero_add_idr;
   rzero_add_idl   := lzero_add_idl;
   rmul_assoc      := lmul_assoc;
   rone_mul_idr    := lone_mul_idr;
   rone_mul_idl    := lone_mul_idl;
   rmul_add_distl  := lmul_add_distl;
   rmul_add_distr  := lmul_add_distr;
   rzero_absorbl   := lzero_absorbl;
   rzero_absorbr   := lzero_absorbr;
   rmeet_assoc     := lmeet_assoc;
   rmeet_comm      := lmeet_comm;
   rmeet_idem      := lmeet_idem;
   rmul_meet_distl := lmul_meet_distl;
   rmul_meet_distr := lmul_meet_distr;
   radd_meet_dist  := ladd_meet_dist;
 }.


(** * Linearly Typed Lambda Calculus *)

Definition l_mctx0 := @mctx0 linear_mod r_linear_mod.

Lemma dup_lmctx0: l_mctx0 = l_mctx0 ::+:: l_mctx0.
Proof. auto. Qed.


(* \x. (x, x) : T -> (T, T) *)
Example prod_abs: forall T, l_mctx0 ;; empty |-
                       tm_abs lm1 "x" (tm_prod (tm_var "x") (tm_var "x")) \in
                       ty_arrow lm1 T (ty_prod T T).
Proof.
  intros.
  apply t_abs.
  rewrite dup_lmctx0.
  apply t_prod_intro;
    apply t_var; auto.
Qed.
