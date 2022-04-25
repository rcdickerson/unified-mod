From Coq Require Import Strings.String.
Require Import Maps.

(** * Ringoids *)

Class Ringoid (A: Type) :=
  {
    r0    : A;
    r1    : A;
    radd  : A -> A -> A;
    rmul  : A -> A -> A;
    rmeet : A -> A -> A;

    radd_comm       : forall a1 a2, radd a1 a2 = radd a2 a1;
    radd_assoc      : forall a1 a2 a3, radd a1 (radd a2 a3) = radd (radd a1 a2) a3;
    rzero_add_idr   : forall a, radd a r0 = a;
    rzero_add_idl   : forall a, radd r0 a = a;
    rmul_assoc      : forall a1 a2 a3, rmul a1 (rmul a2 a3) = rmul (rmul a1 a2) a3;
    rone_mul_idr    : forall a, rmul a r1 = a;
    rone_mul_idl    : forall a, rmul r1 a = a;
    rmul_add_distl  : forall p q r, rmul p (radd q r) = radd (rmul p q) (rmul p r);
    rmul_add_distr  : forall p q r, rmul (radd p q) r = radd (rmul p r) (rmul q r);
    rzero_absorbl   : forall a, rmul a r0 = r0;
    rzero_absorbr   : forall a, rmul r0 a = r0;
    rmeet_assoc     : forall a1 a2 a3, rmeet a1 (rmeet a2 a3) = rmeet (rmeet a1 a2) a3;
    rmeet_comm      : forall a1 a2, rmeet a1 a2 = rmeet a2 a1;
    rmeet_idem      : forall a1 a2, rmeet a1 (rmeet a1 a2) = rmeet a1 a2;
    rmul_meet_distl : forall p q r, rmul p (rmeet q r) = rmeet (rmul p q) (rmul p r);
    rmul_meet_distr : forall p q r, rmul (rmeet p q) r = rmeet (rmul p r) (rmul q r);
    radd_meet_dist  : forall p q r, radd (rmeet p q) r = rmeet (radd p r) (radd q r);
  }.

Notation "x :/\: y" := (rmeet x y) (at level 60, right associativity).
Notation "x :+: y"  := (radd x y)  (at level 50, left associativity).
Notation "x :*: y"  := (rmul x y)  (at level 40, left associativity).
Notation "x :<=: y" := (x = x :/\: y) (at level 70).


(** * Types *)

Inductive ty {M: Type} `{Ringoid M} : Type :=
  | ty_const : ty
  | ty_unit  : ty
  | ty_tvar  : string -> ty
  | ty_tabs  : string -> ty -> ty
  | ty_mabs  : string -> ty -> ty
  | ty_sum   : ty -> ty -> ty
  | ty_prod  : ty -> ty -> ty
  | ty_arrow : M -> ty -> ty -> ty
  | ty_box   : M -> ty -> ty.

Reserved Notation "'[' x ':=' s ']' t" (at level 20, s at next level, t at next level).
Fixpoint ty_subst {M: Type} `{Ringoid M} (x: string) (s t: ty) : ty :=
  match t with
    | ty_const         => ty_const
    | ty_unit          => ty_unit
    | ty_tvar y        => if eqb x y then t else ty_tvar x
    | ty_tabs y t1     => if eqb x y
                         then ty_tabs y t1
                         else ty_tabs y ([x:=s] t1)
    | ty_mabs m t1     => ty_mabs m ([x:=s] t1)
    | ty_sum t1 t2     => ty_sum  ([x:=s] t1) ([x:=s] t2)
    | ty_prod t1 t2    => ty_prod ([x:=s] t1) ([x:=s] t2)
    | ty_arrow m t1 t2 => ty_arrow m ([x:=s] t1) ([x:=s] t2)
    | ty_box m t1      => ty_box m ([x:=s] t1)
  end
where "'[' x ':=' s ']' t" := (ty_subst x s t).

Reserved Notation "'[[' x ':=' s ']]' t" (at level 20, s at next level, t at next level).
Fixpoint m_subst {M: Type} `{Ringoid M} (x: string) (s: M) (t: ty) : ty :=
  match t with
    | ty_const         => ty_const
    | ty_unit          => ty_unit
    | ty_tvar y        => ty_tvar y
    | ty_tabs y t1     => ty_tabs y ([[x:=s]] t1)
    | ty_mabs m t1     => if eqb x m
                         then ty_mabs m t1
                         else ty_mabs m ([[x:=s]] t1)
    | ty_sum t1 t2     => ty_sum  ([[x:=s]] t1) ([[x:=s]] t2)
    | ty_prod t1 t2    => ty_prod ([[x:=s]] t1) ([[x:=s]] t2)
    | ty_arrow m t1 t2 => ty_arrow m ([[x:=s]] t1) ([[x:=s]] t2)
    | ty_box m t1      => ty_box m ([[x:=s]] t1)
  end
where "'[[' x ':=' s ']]' t" := (m_subst x s t).


(** * Terms *)

Inductive tm {M: Type} `{Ringoid M} : Type :=
  | tm_var  : string -> tm
  | tm_abs  : M -> string -> tm -> tm
  | tm_app  : tm -> M -> tm -> tm
  | tm_tabs : string -> tm -> tm
  | tm_tapp : tm -> ty -> tm
  | tm_mabs : string -> tm -> tm
  | tm_mapp : tm -> M -> tm
  | tm_inj1 : tm -> tm
  | tm_inj2 : tm -> tm
  | tm_case : M -> tm -> string -> tm -> string -> tm -> tm
  | tm_unit : tm
  | tm_prod : tm -> tm -> tm
  | tm_let  : tm -> M -> tm -> tm -> tm
  | tm_box  : M -> tm -> tm
  | tm_letbox : M -> string -> M -> tm -> tm -> tm.

Definition true  {M: Type} `{Ringoid M} := tm_inj1 tm_unit.
Definition false {M: Type} `{Ringoid M} := tm_inj2 tm_unit.


(** * Contexts *)

Definition mctx  {M: Type} `{Ringoid M} := partial_map M.
Definition mctx0 {M: Type} `{Ringoid M} := t_empty (Some r0).
Definition tctx  {M: Type} `{Ringoid M} := partial_map ty.

Definition mctx_le {M: Type} `{Ringoid M} (d g: mctx) :=
  forall x t t', d x = Some t ->
            g x = Some t' /\ t :<=: t'.
Notation "d ::<=:: g" := (mctx_le d g) (at level 70).

Definition mctx_add {M: Type} `{Ringoid M} (d g: mctx) :=
  fun x => match d x with
        | None   => g x
        | Some m => match g x with
                   | None => Some m
                   | Some m' => Some (m :+: m')
                   end
        end.
Notation "d ::+:: g" := (mctx_add d g) (at level 50, left associativity).

Definition mctx_mul {M: Type} `{Ringoid M} (q: M) (g: mctx) :=
  fun x => match g x with
        | None   => None
        | Some m => Some (q :*: m)
        end.
Notation "q ::*:: g" := (mctx_mul q g) (at level 40, left associativity).

Lemma dup_mctx0: mctx0 = mctx0 ::+:: mctx0.
Proof. auto. Qed.


(** * Typing Rules *)

Reserved Notation "g ';;' G '|-' t '\in' T" (at level 40,
  G at next level, t at next level, T at next level).

Inductive has_type {M: Type} `{Ringoid M} : mctx -> tctx -> tm -> ty -> Prop :=
  | t_var : forall G A x,
      G x = Some (ty_box r1 A) ->
      mctx0 ;; G |- tm_var x \in A
  | t_wk : forall d g G t A,
      d ;; G |- t \in A ->
      g ::<=:: d ->
      g ;; G |- t \in A
  | t_abs : forall g G x q t A B,
      g ;; (x |-> (ty_box q A); G) |- t \in B ->
      g ;; G |- tm_abs q x t \in ty_arrow q A B
  | t_app : forall g d G q t u A B,
      g ;; G |- t \in ty_arrow q A B ->
      d ;; G |- u \in A ->
      (g ::+:: (q ::*:: d)) ;; G |- tm_app t q u \in B
  | t_tabs : forall g G t B a,
      g ;; G |- t \in B ->
      g ;; G |- tm_tabs a t \in ty_tabs a B
  | t_tapp : forall g G t A B a,
      g ;; G |- t \in (ty_tabs a B) ->
      g ;; G |- tm_tapp t A \in [a:=A] B
  | t_mabs : forall g G t m B,
      g ;; G |- t \in B ->
      g ;; G |- tm_tabs m t \in ty_mabs m B
  | t_mapp : forall g G t m B q,
      g ;; G |- t \in ty_mabs m B ->
      g ;; G |- tm_mapp t q \in [[m:=q]] B
  | t_unit_intro : forall G,
      mctx0 ;; G |- tm_unit \in ty_unit
  | t_unit_elim : forall d g G t u p C,
      g ;; G |- t \in ty_unit ->
      d ;; G |- u \in C ->
      ((p ::*:: g) ::+:: d) ;; G |- tm_let tm_unit p t u \in C
  | t_sum_elim : forall d g G x1 x2 t u1 u2 q A1 A2 C,
      g ;; G |- t \in ty_sum A1 A2 ->
      d ;; (x1 |-> ty_box q A1;G) |- u1 \in C ->
      d ;; (x2 |-> ty_box q A2;G) |- u2 \in C ->
      q :<=: r1 ->
      ((q ::*:: g) ::+:: d) ;; G |- tm_case q t x1 u1 x2 u2 \in C
  | t_sum_intro1 : forall g G t A1 A2,
      g ;; G |- t \in A1 ->
      g ;; G |- tm_inj1 t \in ty_sum A1 A2
  | t_sum_intro2 : forall g G t A1 A2,
      g ;; G |- t \in A2 ->
      g ;; G |- tm_inj2 t \in ty_sum A1 A2
  | t_prod_intro : forall d g G t A u B,
      g ;; G |- t \in A ->
      d ;; G |- u \in B ->
      (d ::+:: g) ;; G |- tm_prod t u \in ty_prod A B
  | t_prod_elim : forall d g G t u q x y A B C,
      g ;; G |- t \in ty_prod A B ->
      d ;; (x |-> ty_box q A; y |-> ty_box q B; G) |- u \in C ->
      ((q ::*:: g) ::+:: d) ;; G |- tm_let (tm_prod (tm_var x) (tm_var y)) q t u \in C
  | t_box_intro : forall g G q t A,
      g ;; G |- t \in A ->
      g ;; G |- tm_box q t \in ty_box q A
  | t_box_elim : forall d g G p q t u A C x,
      g ;; G |- u \in ty_box p A ->
      d ;; x |-> (ty_box (q :*: p) A) ; G |- t \in C ->
      ((q ::*:: g) ::+:: d) ;; G |- tm_let (tm_box p (tm_var x)) q u t \in C

where "g ;; G '|-' t '\in' T" := (has_type g G t T).
