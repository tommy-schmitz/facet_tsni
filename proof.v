Require Import ZArith.

Variable Var : Set.

Variable Principal : Set.
Variable dec_eq_Principal : forall (l1 l2:Principal), {l1=l2}+{l1<>l2}.
Variable Label : Set.
Variable Labels_are_functions : Label -> Principal -> bool.
Coercion Labels_are_functions : Label >-> Funclass.
Variable Label_ineq : forall (l1 l2:Label), l1<>l2 -> exists k, l1 k <> l2 k.
Variable dec_eq_Label : forall (l1 l2:Label), {l1=l2}+{l1<>l2}.
Definition flows (l1 l2 : Label) :=
  forall k, l1 k = true -> l2 k = true.
Variable dec_flows : forall l1 l2, {flows l1 l2}+{not (flows l1 l2)}.
Definition PC := Principal -> option bool.

Variable InputHandle : Set.
Variable OutputHandle : Set.
Variable input_label : InputHandle -> Label.
Variable output_label : OutputHandle -> Label.
Inductive BufferPointer :=
  | BPNum : nat -> BufferPointer
  | BPFacet : Principal -> BufferPointer -> BufferPointer -> BufferPointer
  .
Definition Pointers := InputHandle -> BufferPointer.
Definition Inputs := InputHandle -> list Z.
Definition Outputs := OutputHandle -> list Z.
Variable P_upd : Pointers -> InputHandle -> BufferPointer -> Pointers.
Variable O_upd : Outputs -> OutputHandle -> list Z -> Outputs.

Inductive Term :=
  | TLam : Var -> Term -> Term
  | TRaw : Term -> Term
  | TOneFacet : Term -> Term
  | TNum : Z -> Term
  | TUnit : Term
  | TReturn : Term -> Term
  | TVar : Var -> Term
  | TApp : Term -> Term -> Term
  | TBindFac : Term -> Term -> Term
  | TPlus : Term -> Term -> Term
  | TIf : Term -> Term -> Term -> Term
  | TBindFIO : Term -> Term -> Term
  | TrunFacFIO : Term -> Term
  | TGet : InputHandle -> Term
  | TPut : OutputHandle -> Term -> Term
  | TFacet : Principal -> Term -> Term -> Term
  | TThreads : Principal -> Term -> Term -> Term
  .
Variable subs : Term -> Var -> Term -> Term.
Variable ffacet : PC -> Term -> Term -> Term.

Inductive Context :=
  | EApp : Term -> Context
  | EBindFac : Term -> Context
  | EPlus1 : Term -> Context
  | EPlus2 : Z -> Context
  | EIf : Term -> Term -> Context
  | EBindFIO : Term -> Context
  | ErunFacFIO : Context
  | EPut : OutputHandle -> Context
  .
Definition fill : Context -> Term -> Term :=
  fun E t =>
    match E with
    | EApp t2 => TApp t t2
    | EBindFac t2 => TBindFac t t2
    | EPlus1 t2 => TPlus t t2
    | EPlus2 n => TPlus (TNum n) t
    | EIf t2 t3 => TIf t t2 t3
    | EBindFIO t2 => TBindFIO t t2
    | ErunFacFIO => TrunFacFIO t
    | EPut o => TPut o t
    end.

Definition Config : Set := Term * Pointers * Inputs * Outputs.

Fixpoint list_at l j :=
  match l with
  | nil => (-1)%Z
  | cons n l =>
      match j with
      | 0 => n
      | S j => list_at l j
      end
  end.
Definition snoc {A} l (x:A) := app l (cons x nil).

Inductive StdStep : Config -> Config -> Prop :=
  | SContext : forall t P I O t' I' O' P' E,
      StdStep (t, P, I, O) (t', P', I', O') ->
      StdStep (fill E t, P, I, O) (fill E t', P, I, O)
  | SApp : forall x t1 t2 P I O,
      StdStep (TApp (TLam x t1) t2, P, I, O) (subs t1 x t2, P, I, O)
  | SBindFac1 : forall t1 t2 P I O,
      StdStep (TBindFac (TRaw t1) t2, P, I, O) (TApp t2 t1, P, I, O)
  | SBindFac2 : forall t1 t2 P I O,
      StdStep (TBindFac (TOneFacet t1) t2, P, I, O) (TOneFacet (TBindFac t1 t2), P, I, O)
  | SPlus : forall n1 n2 P I O,
      StdStep (TPlus (TNum n1) (TNum n2), P, I, O) (TNum (n1+n2), P, I, O)
  | SIf1 : forall t1 t2 P I O,
      StdStep (TIf (TNum 0) t1 t2, P, I, O) (t1, P, I, O)
  | SIf2 : forall n t1 t2 P I O,
      n <> 0%Z ->
      StdStep (TIf (TNum n) t1 t2, P, I, O) (t1, P, I, O)
  | SBindFIO : forall t1 t2 P I O,
      StdStep (TBindFIO (TReturn t1) t2, P, I, O) (TApp t2 t1, P, I, O)
  | SrunFacFIO1 : forall t P I O,
      StdStep (TrunFacFIO (TRaw t), P, I, O) (t, P, I, O)
  | SrunFacFIO2 : forall t P I O,
      StdStep (TrunFacFIO (TOneFacet t), P, I, O) (TrunFacFIO t, P, I, O)
  | SRead : forall i P I O j,
      P i = BPNum j ->
      StdStep (TGet i, P, I, O) (TReturn (TRaw (TNum (list_at (I i) j))), P_upd P i (BPNum (j + 1)), I, O)
  | SWrite : forall o n P I O,
      StdStep (TPut o (TNum n), P, I, O) (TReturn TUnit, P, I, O_upd O o (snoc (O o) n))
  .

Definition pI l (I:Inputs) i :=
  if dec_flows (input_label i) l then
    I i
  else
    nil.
Definition pO l (O:Outputs) o :=
  if dec_eq_Label (output_label o) l then
    O o
  else
    nil.

Fixpoint fac_read i p (I:Inputs) :=
  match p with
  | BPNum n =>
      (TNum (list_at (I i) n), BPNum (S n))
  | BPFacet k p1 p2 =>
      let (t1, p1') := fac_read i p1 I  in
      let (t2, p2') := fac_read i p2 I  in
      (TFacet k t1 t2, BPFacet k p1' p2')
  end.
Definition l2pc : Label -> PC :=
  fun l => fun k => Some (l k).
Definition Subsumes (pc:PC) (l:Label) :=
  forall k,
    match pc k with
    | Some b => b = l k
    | None => True
    end.
Definition add : PC -> Principal -> PC :=
  fun pc k1 k2 =>
    if dec_eq_Principal k1 k2 then
      Some true
    else
      pc k2.
Definition subtract : PC -> Principal -> PC :=
  fun pc k1 k2 =>
    if dec_eq_Principal k1 k2 then
      Some false
    else
      pc k2.
Inductive FacStep : PC -> Config -> Config -> Prop :=
  | FContext : forall pc t P I O t' I' O' P' E,
      FacStep pc (t, P, I, O) (t', P', I', O') ->
      FacStep pc (fill E t, P, I, O) (fill E t', P, I, O)
  | FApp : forall pc x t1 t2 P I O,
      FacStep pc (TApp (TLam x t1) t2, P, I, O) (subs t1 x t2, P, I, O)
  | FBindFac1 : forall pc t1 t2 P I O,
      FacStep pc (TBindFac (TRaw t1) t2, P, I, O) (TApp t2 t1, P, I, O)
  | FBindFac2 : forall pc t1 t2 P I O,
      FacStep pc (TBindFac (TOneFacet t1) t2, P, I, O) (TOneFacet (TBindFac t1 t2), P, I, O)
  | FPlus : forall pc n1 n2 P I O,
      FacStep pc (TPlus (TNum n1) (TNum n2), P, I, O) (TNum (n1+n2), P, I, O)
  | FIf1 : forall pc t1 t2 P I O,
      FacStep pc (TIf (TNum 0) t1 t2, P, I, O) (t1, P, I, O)
  | FIf2 : forall pc n t1 t2 P I O,
      n <> 0%Z ->
      FacStep pc (TIf (TNum n) t1 t2, P, I, O) (t1, P, I, O)
  | FBindFIO : forall pc t1 t2 P I O,
      FacStep pc (TBindFIO (TReturn t1) t2, P, I, O) (TApp t2 t1, P, I, O)
  | FrunFacFIO1 : forall pc t P I O,
      FacStep pc (TrunFacFIO (TRaw t), P, I, O) (t, P, I, O)
  | FrunFacFIO2 : forall pc t P I O,
      FacStep pc (TrunFacFIO (TOneFacet t), P, I, O) (TrunFacFIO t, P, I, O)

  | FRead : forall pc i P I O t p',
      (t, p') = fac_read i (P i) I ->
      FacStep pc (TGet i, P, I, O) (TReturn (ffacet (l2pc (input_label i)) t (TRaw (TNum 0))), P_upd P i p', I, O)
  | FWrite : forall pc o n P I O,
      Subsumes pc (output_label o) ->
      FacStep pc (TPut o (TNum n), P, I, O) (TReturn TUnit, P, I, O_upd O o (snoc (O o) n))
  | FWriteSkip : forall pc o n P I O,
      not (Subsumes pc (output_label o)) ->
      FacStep pc (TPut o (TNum n), P, I, O) (TReturn TUnit, P, I, O)
  | FBindFac3 : forall pc k t1 t2 t3 P I O,
      FacStep pc (TBindFac (TFacet k t1 t2) t3, P, I, O) (TFacet k (TBindFac t1 t3) (TBindFac t2 t3), P, I, O)
  | FrunFacFIO3 : forall pc k t1 t2 P I O,
      pc k = Some true ->
      FacStep pc (TrunFacFIO (TFacet k t1 t2), P, I, O) (TrunFacFIO t1, P, I, O)
  | FrunFacFIO4 : forall pc k t1 t2 P I O,
      pc k = Some false ->
      FacStep pc (TrunFacFIO (TFacet k t1 t2), P, I, O) (TrunFacFIO t2, P, I, O)
  | FrunFacFIO5 : forall pc k t1 t2 P I O,
      pc k = None ->
      FacStep pc (TrunFacFIO (TFacet k t1 t2), P, I, O) (TThreads k (TrunFacFIO t1) (TrunFacFIO t2), P, I, O)
  | FTimeout : forall pc E k t1 t2 P I O,
      FacStep pc (fill E (TThreads k t1 t2), P, I, O) (TThreads k (fill E t1) (fill E t2), P, I, O)
  | FMerge : forall pc k t1 t2 P I O,
      FacStep pc (TThreads k (TReturn t1) (TReturn t2), P, I, O) (TReturn (TFacet k t1 t2), P, I, O)
  | FThread1 : forall pc k t1 t2 P I O t1' P' I' O',
      FacStep (add pc k) (t1, P, I, O) (t1', P', I', O') ->
      FacStep pc (TThreads k t1 t2, P, I, O) (TThreads k t1' t2, P', I', O')
  | FThread2 : forall pc k t1 t2 P I O t2' P' I' O',
      FacStep (subtract pc k) (t2, P, I, O) (t2', P', I', O') ->
      FacStep pc (TThreads k t1 t2, P, I, O) (TThreads k t1 t2', P', I', O')
  .

Fixpoint pt l t :=
  match t with
  | TFacet k t1 t2 =>
      if l k then
        TOneFacet (pt l t1)
      else
        TOneFacet (pt l t2)
  | TThreads k t1 t2 =>
      if l k then
        (pt l t1)
      else
        (pt l t2)
  | TPut o t =>
      if dec_eq_Label (output_label o) l then
        TPut o (pt l t)
      else
        TReturn TUnit
  | TLam x t => TLam x (pt l t)
  | TRaw t => TRaw (pt l t)
  | TOneFacet t => TOneFacet (pt l t)
  | TNum n => TNum n
  | TUnit => TUnit
  | TReturn t => TReturn (pt l t)
  | TVar x => TVar x
  | TApp t1 t2 => TApp (pt l t1) (pt l t2)
  | TBindFac t1 t2 => TBindFac (pt l t1) (pt l t2)
  | TPlus t1 t2 => TPlus (pt l t1) (pt l t2)
  | TIf t1 t2 t3 => TIf (pt l t1) (pt l t2) (pt l t3)
  | TBindFIO t1 t2 => TBindFIO (pt l t1) (pt l t2)
  | TrunFacFIO t => TrunFacFIO (pt l t)
  | TGet i => TGet i
  end.
Variable subs_lemma : forall l t1 t2 x,
  pt l (subs t1 x t2) = subs (pt l t1) x (pt l t2).

Lemma fill_lemma : forall l E t,
  match E with
  | EPut _ => False
  | E => True
  end ->
  {E' | (pt l (fill E t)) = fill E' (pt l t)}.
 destruct E; intros.
        exists (EApp (pt l t)); auto.
       exists (EBindFac (pt l t)); auto.
      exists (EPlus1 (pt l t)); auto.
     exists (EPlus2 z); auto.
    exists (EIf (pt l t) (pt l t0)); auto.
   exists (EBindFIO (pt l t)); auto.
  exists ErunFacFIO; auto.
 inversion H.
Qed.

Fixpoint pp (l:Label) p :=
  match p with
  | BPNum n => BPNum n
  | BPFacet k p1 p2 =>
      if l k then
        pp l p1
      else
        pp l p2
  end.
Definition pP l (P:Pointers) i := pp l (P i).
Definition pC (l:Label) (C:Config) : Config :=
  match C with
  | (t, P, I1, O1) => (pt l t, pP l P, pI l I1, pO l O1)
  end.

Definition emptypc : PC :=
  fun k => None.

Definition hints_F := (FContext, FApp, FBindFac1, FBindFac2, FPlus, FIf1, FIf2, FBindFIO, FrunFacFIO1, FrunFacFIO2, FRead, FWrite, FWriteSkip, FBindFac3, FrunFacFIO3, FrunFacFIO4, FrunFacFIO5, FTimeout, FMerge, FThread1, FThread2).
Definition hints_S := (SContext, SApp, SBindFac1, SBindFac2, SPlus, SIf1, SIf2, SBindFIO, SrunFacFIO1, SrunFacFIO2, SRead, SWrite).
Definition hints := (hints_F, hints_S, fill_lemma, subs_lemma).
(*
StdStep
  TApp (TLam x (pt l t1)) (pt l t2)
  pt l (subs t1 x t2)
  (subs (pt l t1) x (pt l t2))
*)

Ltac helper := unfold pt; simpl; fold pt.
Variable ffacet_Axiom1 : forall l1 l2 t1 t2,
  flows l2 l1 ->
  (pt l1 (ffacet (l2pc l2) t1 t2)) = pt l1 t1.
Variable ffacet_Axiom2 : forall l1 l2 t1 t2,
  not (flows l2 l1) ->
  (pt l1 (ffacet (l2pc l2) t1 t2)) = pt l1 t2.

Theorem projection_1 : forall C C' l pc,
  FacStep pc C C' ->
  or (pC l C = pC l C') (StdStep (pC l C) (pC l C')).
 induction 1; unfold pC; simpl;
(*   try solve [helper; pose (hints := hints); intuition]; *)
 idtac.
                     admit.
                    helper.
                    rewrite subs_lemma.
                    pose (hints := hints); intuition.
                   admit.
                  admit.
                 admit.
                admit.
               admit.
              admit.
             admit.
            admit.
           helper.
           destruct (dec_flows (input_label i) l).
            rewrite ffacet_Axiom1; try assumption.
            right.
            eapply SRead.

   (* FContext *)
   admit.
(*
   destruct IHFacStep.
    left.
    unfold pC.
    unfold pC in H0.
    injection H0; intros.
    unfold fill.
    destruct E; simpl; try congruence.
    destruct (dec_eq_Label (output_label o) l); congruence.
   right.
   remember E as E_temp.
   destruct E.
   destruct (fill_lemma l E_temp t) as (E', H1).
    destruct E_temp; try trivial; discriminate.
   destruct (fill_lemma l E_temp t') as (E'', H2).
    destruct E_temp; try trivial; discriminate.
   unfold pC.
   rewrite H1.
   rewrite H2.
   apply SContext.
   ; try (
    destruct (fill_lemma l E t) as (E', H1); [trivial | intuition]
   ).
   injection H0; intros.
   trivial.
   right.
   apply SContext.
   unfold pC.
   rewrite fill_lemma with (t' := t').
    trivial.
*)
