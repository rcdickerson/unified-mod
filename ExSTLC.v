From Coq Require Import Strings.String.
Require Import Maps.
Require Import UVM.

(** * Singleton Ringoid *)
Inductive singleton := u.
Definition sadd  (_ _: singleton): singleton := u.
Definition smul  (_ _: singleton): singleton := u.
Definition smeet (_ _: singleton): singleton := u.

Lemma sadd_comm: forall a b, sadd a b = sadd b a.
Proof. auto. Qed.

Lemma sadd_assoc: forall a b c, sadd a (sadd b c) = sadd (sadd a b) c.
Proof. auto. Qed.

Lemma szero_add_idr: forall a, sadd a u = a.
Proof. destruct a; auto. Qed.

Lemma szero_add_idl: forall a, sadd u a = a.
Proof. destruct a; auto. Qed.

Lemma smul_assoc: forall a1 a2 a3, smul a1 (smul a2 a3) = smul (smul a1 a2) a3.
Proof. auto. Qed.

Lemma sone_mul_idr: forall a, smul a u = a.
Proof. destruct a; auto. Qed.

Lemma sone_mul_idl: forall a, smul u a = a.
Proof. destruct a; auto. Qed.

Lemma smul_add_distl: forall p q r, smul p (sadd q r) = sadd (smul p q) (smul p r).
Proof. auto. Qed.

Lemma smul_add_distr: forall p q r, smul (sadd p q) r = sadd (smul p r) (smul q r).
Proof. auto. Qed.

Lemma szero_absorbl: forall a, smul a u = u.
Proof. auto. Qed.

Lemma szero_absorbr: forall a, smul u a = u.
Proof. auto. Qed.

Lemma smeet_assoc: forall a1 a2 a3, smeet a1 (smeet a2 a3) = smeet (smeet a1 a2) a3.
Proof. auto. Qed.

Lemma smeet_comm: forall a1 a2, smeet a1 a2 = smeet a2 a1.
Proof. auto. Qed.

Lemma smeet_idem: forall a1 a2, smeet a1 (smeet a1 a2) = smeet a1 a2.
Proof. auto. Qed.

Lemma smul_meet_distl: forall p q r, smul p (smeet q r) = smeet (smul p q) (smul p r).
Proof. auto. Qed.

Lemma smul_meet_distr: forall p q r, smul (smeet p q) r = smeet (smul p r) (smul q r).
Proof. auto. Qed.

Lemma sadd_meet_dist: forall p q r, sadd (smeet p q) r = smeet (sadd p r) (sadd q r).
Proof. auto. Qed.

Instance r_singleton : Ringoid singleton :=
 {
   r0 := u;
   r1 := u;
   radd := sadd;
   rmul := smul;
   rmeet := smeet;

   radd_comm       := sadd_comm;
   radd_assoc      := sadd_assoc;
   rzero_add_idr   := szero_add_idr;
   rzero_add_idl   := szero_add_idl;
   rmul_assoc      := smul_assoc;
   rone_mul_idr    := sone_mul_idr;
   rone_mul_idl    := sone_mul_idl;
   rmul_add_distl  := smul_add_distl;
   rmul_add_distr  := smul_add_distr;
   rzero_absorbl   := szero_absorbl;
   rzero_absorbr   := szero_absorbr;
   rmeet_assoc     := smeet_assoc;
   rmeet_comm      := smeet_comm;
   rmeet_idem      := smeet_idem;
   rmul_meet_distl := smul_meet_distl;
   rmul_meet_distr := smul_meet_distr;
   radd_meet_dist  := sadd_meet_dist;
 }.


(** * STLC *)

(* Instantiating the framework with a singleton ringoid should just
   recover the standard STLC (with sum and products types, etc.)
 *)

Definition s_mctx0 := @mctx0 singleton r_singleton.

Lemma dup_smctx0: s_mctx0 = s_mctx0 ::+:: s_mctx0.
Proof. auto. Qed.


(* \x. (x, x) : T -> (T, T) *)
Example prod_abs: forall T, s_mctx0 ;; empty |-
                       tm_abs u "x" (tm_prod (tm_var "x") (tm_var "x")) \in
                       ty_arrow u T (ty_prod T T).
Proof.
  intros.
  apply t_abs.
  rewrite dup_smctx0.
  apply t_prod_intro;
    apply t_var; auto.
Qed.
