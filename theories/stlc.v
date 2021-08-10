From playground Require Import prelude.

(** This file is adapted from _Software Foundations_. The name binding approach
mostly follows the paper _The Locally Nameless Representation_, and is inspired
by the Coq development _formalmetacoq_ by the same author. *)

Module stlc.

Import atom_instance.

#[global]
Opaque atom.
#[global]
Opaque amap.
#[global]
Opaque aset.
#[global]
Opaque is_atom.

Section lang.

Implicit Types (x y : atom) (L : aset).

(** * Syntax *)

(** ** Type (τ) *)
Inductive ty : Type :=
| TBool
| TArrow (τ1 τ2 : ty)
.

(** ** Term (t) *)
Inductive tm : Type :=
| MFVar (x : atom)
| MBVar (k : nat)
| MApp (t1 t2 : tm)
| MAbs (τ : ty) (t : tm)
| MTrue
| MFalse
| MIf (t0 t1 t2 : tm)
.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "τ1 -> τ2" := (TArrow τ1 τ2) (in custom stlc at level 50,
                                          right associativity).
Notation "t1 t2" := (MApp t1 t2) (in custom stlc at level 1, left associativity).
Notation "\ : τ , t" :=
  (MAbs τ t) (in custom stlc at level 90,
                 τ custom stlc at level 99,
                 t custom stlc at level 99).

Coercion MFVar : atom >-> tm.
Coercion MBVar : nat >-> tm.

Notation "$ n" := (MBVar n) (in custom stlc at level 0, n constr at level 0,
                            format "$ n").
Notation "'Bool'" := TBool (in custom stlc at level 0).

Notation "'if' t0 'then' t1 'else' t2" :=
  (MIf t0 t1 t2) (in custom stlc at level 89,
                     t0 custom stlc at level 99,
                     t1 custom stlc at level 99,
                     t2 custom stlc at level 99,
                     left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := MTrue (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := MFalse (in custom stlc at level 0).

(** * Examples *)

Definition idB :=
  <{ \:Bool, 0 }>.

Notation idBB :=
  <{\:Bool->Bool, 0}>.

Notation idBBBB :=
  <{\:((Bool->Bool)->(Bool->Bool)), 0}>.

Notation fstBB := <{\:Bool, \:Bool, 1}>.

Notation notB := <{\:Bool, if 0 then false else true}>.

(** * Small-step semantics *)

(** ** Variable opening *)
Reserved Notation "'[' k '~>' s ']' t" (in custom stlc at level 20, k constr,
                                           format "[ k '~>' s ] t").
Fixpoint open_ (k : nat) (s : tm) (t : tm) : tm :=
  match t with
  | <{ $n }> => if decide (k = n) then s else t
  | <{ \:τ, t }> => <{ \:τ, [S k~>s]t }>
  | <{ t1 t2 }> => <{ ([k~>s]t1) ([k~>s]t2) }>
  | <{ if t0 then t1 else t2 }> => <{ if ([k~>s]t0) then ([k~>s]t1) else ([k~>s]t2) }>
  | _ => t
  end
where "'[' k '~>' s ']' t" := (open_ k s t) (in custom stlc).

Definition open s t := open_ 0 s t.

Notation "t ^ s" := (open s t) (in custom stlc at level 20,
                               format "t ^ s").

(** ** Values (v) *)
Inductive value : tm -> Prop :=
  | VAbs τ t :
      value <{ \:τ, t }>
  | VTrue :
      value <{ true }>
  | VFalse :
      value <{ false }>.

(* Unfortunately the notation --> is used in the standard library. *)
Reserved Notation "t '-->!' t'" (at level 40).

(** ** Step relation (t -->! t') *)
Inductive step : tm -> tm -> Prop :=
| SAppAbs τ t1 v2 :
    value v2 ->
    <{ (\:τ, t1) v2 }> -->! <{ t1^v2 }>
| SApp1 t1 t1' t2 :
    t1 -->! t1' ->
    <{ t1 t2 }> -->! <{ t1' t2 }>
| SApp2 v1 t2 t2' :
    value v1 ->
    t2 -->! t2' ->
    <{ v1 t2 }> -->! <{ v1 t2' }>
| SIfTrue t1 t2 :
    <{ if true then t1 else t2 }> -->! t1
| SIfFalse t1 t2 :
    <{ if false then t1 else t2 }> -->! t2
| SIf t0 t0' t1 t2 :
    t0 -->! t0' ->
    <{ if t0 then t1 else t2 }> -->! <{ if t0' then t1 else t2 }>

where "t '-->!' t'" := (step t t').

Notation multistep := (clos_refl_trans_1n _ step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** * Typing *)
Notation tctx := (amap ty).

Reserved Notation "Γ '⊢' t ':' τ" (at level 101,
                                   t custom stlc, τ custom stlc at level 0).
(** ** Typing relation (Γ ⊢ t : τ) *)
Inductive typing : tctx -> tm -> ty -> Prop :=
  | TVar Γ x τ :
      Γ !! x = Some τ ->
      Γ ⊢ x : τ
  | TAbs Γ τ1 τ2 t1 L :
      (forall x, x ∉ L -> <[x:=τ2]>Γ ⊢ t1^x : τ1) ->
      Γ ⊢ \:τ2, t1 : (τ2 -> τ1)
  | TApp Γ τ1 τ2 t1 t2 :
      Γ ⊢ t1 : (τ2 -> τ1) ->
      Γ ⊢ t2 : τ2 ->
      Γ ⊢ t1 t2 : τ1
  | TTrue Γ :
       Γ ⊢ true : Bool
  | TFalse Γ :
       Γ ⊢ false : Bool
  | TIf Γ t0 t1 t2 τ :
       Γ ⊢ t0 : Bool ->
       Γ ⊢ t1 : τ ->
       Γ ⊢ t2 : τ ->
       Γ ⊢ if t0 then t1 else t2 : τ

where "Γ '⊢' t ':' τ" := (typing Γ t τ).


(** * Infrastructure *)

(** ** Locally closed *)
Inductive lc : tm -> Prop :=
| LCVar x : lc <{ x }>
| LCTrue : lc <{ true }>
| LCFalse : lc <{ false }>
| LCIf t0 t1 t2 : lc t0 -> lc t1 -> lc t2 -> lc <{ if t0 then t1 else t2 }>
| LCApp t1 t2 : lc t1 -> lc t2 -> lc <{ t1 t2 }>
| LCAbs τ t L : (forall x, x ∉ L -> lc <{ t^x }>) -> lc <{ \:τ, t }>
.

(** ** Substitution *)
Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr,
                                       format "[ x ':=' s ] t").

Fixpoint subst (x : atom) (s : tm) (t : tm) : tm :=
  match t with
  | MFVar y => if decide (x = y) then s else t
  | <{ \:τ, t }> => <{ \:τ, [x:=s]t }>
  | <{ t1 t2 }> => <{ ([x:=s]t1) ([x:=s]t2) }>
  | <{ if t0 then t1 else t2 }> => <{ if ([x:=s]t0) then ([x:=s]t1) else ([x:=s]t2) }>
  | _ => t
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(** ** Free variables *)
Fixpoint fv (t : tm) : aset :=
  match t with
  | MFVar x => {[x]}
  | <{ \:_, t }> => fv t
  | <{ t1 t2 }> => fv t1 ∪ fv t2
  | <{ if t0 then t1 else t2 }> => fv t0 ∪ fv t1 ∪ fv t2
  | _ => ∅
  end.

Notation "x # t" := (x ∉ fv t) (at level 40).

Definition closed t := fv t = ∅.

Instance atom_stale : @Stale aset atom := singleton.
Arguments atom_stale /.

Instance tm_stale : Stale tm := fv.
Arguments tm_stale /.

Instance tctx_stale : Stale tctx := dom aset.
Arguments tctx_stale /.

Instance aset_stale : Stale aset := id.
Arguments aset_stale /.

Lemma open_lc_ t : forall s u i j,
  <{ [j~>u]([i~>s] t) }> = <{ [i~>s] t }> ->
  i <> j ->
  <{ [j~>u] t }> = t.
Proof.
  induction t; hauto.
Qed.

Lemma open_lc t s :
  lc t -> forall k, <{ [k~>s] t }> = t.
Proof.
  induction 1; try qauto.

  (* TAbs *)
  - simpl_cofin.
    qauto use: open_lc_.
Qed.

Lemma subst_fresh t : forall x s,
  x # t -> <{ [x:=s] t }> = t.
Proof.
  induction t; qauto solve: fast_set_solver*.
Qed.

Lemma subst_open t : forall x s v,
  lc s ->
  <{ [x:=s](t^v) }> = <{ ([x:=s]t)^([x:=s]v) }>.
Proof.
  unfold open. generalize 0.
  induction t; hauto use: open_lc.
Qed.

Lemma subst_open_comm t x y s :
  x <> y ->
  lc s ->
  <{ [x:=s] (t ^ y) }> = <{ ([x:=s] t) ^ y }>.
Proof.
  qauto use: subst_open.
Qed.

(** We may prove this one using [subst_open] and [subst_fresh], but a direct
induction gives us a slightly stronger version (without the local closure
constraint). *)
Lemma subst_intro t : forall s x,
  x # t ->
  <{ t ^ s }> = <{ [x:=s] (t ^ x) }>.
Proof.
  unfold open. generalize 0.
  induction t; hauto simp+: set_unfold.
Qed.

(** Well-typed terms are locally closed. *)
Lemma typing_lc Γ t τ :
  Γ ⊢ t : τ ->
  lc t.
Proof.
  induction 1; eauto using lc.
Qed.

Lemma open_fresh t : forall x x',
  x # t ->
  x <> x' ->
  x # <{ t^x' }>.
Proof.
  unfold open. generalize 0.
  induction t; intros; simpl in *;
    qauto solve: fast_set_solver*.
Qed.

(* These lemmas are not needed in this development. *)
Lemma typing_rename_ Γ t τ τ' x y :
  <[x:=τ']>Γ ⊢ t : τ ->
  y ∉ fv t ∪ dom aset Γ ->
  <[y:=τ']>Γ ⊢ [x:=y]t : τ.
Proof.
  remember (<[x:=τ']>Γ) as Γ'.
  intros H. revert dependent Γ.
  induction H; intros; subst; simpl in *;
    try solve [ case_decide; subst; econstructor; set_unfold; by simplify_map_eq
              | econstructor; auto_apply; auto; fast_set_solver!! ].
  - econstructor.
    simpl_cofin.
    rewrite <- subst_open_comm by (eauto using lc; fast_set_solver!!).
    rewrite insert_commute by fast_set_solver!!.
    auto_apply.
    by rewrite insert_commute by fast_set_solver!!.
    set_unfold.
    qauto use: open_fresh.
Qed.

Lemma typing_rename Γ t τ τ' x y :
  <[x:=τ']>Γ ⊢ t^x : τ ->
  x ∉ fv t ∪ dom aset Γ ->
  y ∉ fv t ∪ dom aset Γ ->
  <[y:=τ']>Γ ⊢ t^y : τ.
Proof.
  intros.
  destruct (decide (y = x)); subst; eauto.
  rewrite subst_intro with (x:=x) by fast_set_solver!!.
  apply typing_rename_; eauto.
  set_unfold.
  qauto use: open_fresh.
Qed.

(* The admissible existential introduction form of abstraction. *)
Lemma TAbs_intro Γ τ1 τ2 t1 x :
  x ∉ fv t1 ∪ dom aset Γ ->
  <[x:=τ2]>Γ ⊢ t1^x : τ1 ->
  Γ ⊢ \:τ2, t1 : (τ2 -> τ1).
Proof.
  intros.
  econstructor.
  simpl_cofin.
  eapply typing_rename; eauto.
  fast_set_solver!!.
Qed.

(** * Metatheories *)

(** ** Progress *)
Theorem progress t τ :
  ∅ ⊢ t : τ ->
  value t \/ exists t', t -->! t'.
Proof.
  remember ∅ as Γ.
  induction 1; simplify_eq;
    hauto ctrs: value, step inv: value, typing.
Qed.

(** ** Preservation *)
Lemma weakening Γ Γ' t τ :
  Γ ⊢ t : τ ->
  Γ ⊆ Γ' ->
  Γ' ⊢ t : τ.
Proof.
  intros H. revert Γ'.
  induction H; intros;
    econstructor; intros; eauto using lookup_weaken, insert_mono.
Qed.

Lemma weakening_insert Γ t τ x τ' :
  x ∉ dom aset Γ ->
  Γ ⊢ t : τ ->
  <[x:=τ']>Γ ⊢ t : τ.
Proof.
  eauto using weakening, insert_fresh_subseteq.
Qed.

Lemma subst_preversation t Γ x v τ1 τ2 :
  <[x:=τ1]>Γ ⊢ t : τ2 ->
  Γ ⊢ v : τ1 ->
  Γ ⊢ <{ [x:=v]t }> : τ2.
Proof.
  intros H.
  remember (<[x:=τ1]>Γ) as Γ'.
  generalize dependent Γ.
  induction H; intros; subst; simpl;
    try qauto simp+: simplify_map_eq ctrs: typing.
  (* TAbs *)
  - econstructor.
    simpl_cofin.
    rewrite <- subst_open_comm by (eauto using typing_lc; fast_set_solver!!).
    auto_apply.
    by rewrite insert_commute by fast_set_solver!!.
    eauto using weakening_insert.
Qed.

Theorem preservation Γ t t' τ :
  Γ ⊢ t : τ ->
  t -->! t' ->
  Γ ⊢ t' : τ.
Proof.
  intros H. generalize dependent t'.
  induction H; intros ? Hs; sinvert Hs; subst;
    eauto using typing.
  (* TApp *)
  - select (_ ⊢ \:_, _ : _) (fun H => sinvert H).
    simpl_cofin.
    erewrite subst_intro by eauto.
    eauto using subst_preversation.
Qed.

(** ** Soundness *)
Definition stuck (t : tm) : Prop :=
  (nf step) t /\ ~ value t.

Corollary soundness t t' τ :
  ∅ ⊢ t : τ ->
  t -->* t' ->
  ~(stuck t').
Proof.
  induction 2; qauto unfold: nf, stuck use: progress, preservation.
Qed.

End lang.
End stlc.
