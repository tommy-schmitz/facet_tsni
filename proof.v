Require Import ZArith.

Variable Var : Set.

Variable Principal : Set.
Definition Label := Principal -> bool.
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
Variable fill : Context -> Term -> Term.

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
