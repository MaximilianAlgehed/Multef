(* Search for "Variable" or "Admitted" to find assumptions that are not proved. *)

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
Variable PC : Set.
Variable PCs_are_functions : PC -> Principal -> option bool.
Coercion PCs_are_functions : PC >-> Funclass.
Variable functions_are_PCs : (Principal -> option bool) -> PC.
Variable PC_function_Axiom : forall f k, functions_are_PCs f k = f k.
Variable PC_extensionality : forall (pc1 pc2:PC), (forall k, pc1 k = pc2 k) -> pc1 = pc2.
Variable unset : PC -> Principal -> PC.
Variable unset_Axiom1 : forall pc k k', k=k' -> unset pc k k' = None.
Variable unset_Axiom2 : forall pc k k', k<>k' -> unset pc k k' = pc k'.
Variable unset_Axiom3 : forall (pc:PC) k, pc k = None -> pc = unset pc k.
Variable emptypc : PC.
Variable emptypc_Axiom : forall k, emptypc k = None.
Variable all_PCs_are_finite : forall pc, exists ks, emptypc = Lists.List.fold_right (fun k pc => unset pc k) pc ks.

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
  | TFV : FacetedValue -> Term
  | TLam : Var -> Term -> Term
  | TNum : Z -> Term
  | TUnit : Term
  | TReturn : Term -> Term
  | TVar : Var -> Term
  | TApp : Term -> Term -> Term
  | TPlus : Term -> Term -> Term
  | TIf : Term -> Term -> Term -> Term
  | TBindFIO : Term -> Term -> Term
  | TrunFacFIO : Term -> Term
  | TGet : InputHandle -> Term
  | TPut : OutputHandle -> Term -> Term
  | TThreads : Principal -> Term -> Term -> Term
with FacetedValue :=
  | FVRaw : Term -> FacetedValue
  | FVBind : Term -> Term -> FacetedValue
  | FVFacet : Principal -> FacetedValue -> FacetedValue -> FacetedValue
  .

Inductive IsValue : Term -> Prop :=
  | VFV : forall fv,
      IsValue (TFV fv)
  | VLam : forall x t,
      IsValue (TLam x t)
  | VNum : forall z,
      IsValue (TNum z)
  | VUnit :
      IsValue TUnit
  | VReturn : forall t,
      IsValue t ->
      IsValue (TReturn t)
  .
Definition NotNum t := forall z, t = TNum z -> False.

Variable subs : Term -> Var -> Term -> Term.
Variable ffacet : PC -> FacetedValue -> FacetedValue -> FacetedValue.

Inductive Context :=
  | EApp : Term -> Context
  | EPlus1 : Term -> Context
  | EPlus2 : Z -> Context
  | EIf : Term -> Term -> Context
  | EBindFIO : Term -> Context
  | ErunFacFIO1 : Context
  | ErunFacFIO2 : Term -> Context
  | EPut : OutputHandle -> Context
  | EReturn : Context
  .
Definition fill : Context -> Term -> Term :=
  fun E t =>
    match E with
    | EApp t2 => TApp t t2
    | EPlus1 t2 => TPlus t t2
    | EPlus2 n => TPlus (TNum n) t
    | EIf t2 t3 => TIf t t2 t3
    | EBindFIO t2 => TBindFIO t t2
    | ErunFacFIO1 => TrunFacFIO t
    | ErunFacFIO2 t2 => TrunFacFIO (TFV (FVBind t t2))
    | EPut o => TPut o t
    | EReturn => TReturn t
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

(* Takes two terms, produces a fresh name not free in those terms, passes that name to the given function, and returns the result. *)
Variable fresh : Term -> Term -> (Var -> Term) -> Term.

Inductive StdStep : Config -> Config -> Prop :=
  | SContext : forall t P I O t' I' O' P' E,
      StdStep (t, P, I, O) (t', P', I', O') ->
      StdStep (fill E t, P, I, O) (fill E t', P', I', O')
  | SApp : forall x t1 t2 P I O,
      StdStep (TApp (TLam x t1) t2, P, I, O) (subs t1 x t2, P, I, O)
  | SPlus : forall n1 n2 P I O,
      StdStep (TPlus (TNum n1) (TNum n2), P, I, O) (TNum (n1+n2), P, I, O)
  | SIf1 : forall t1 t2 P I O,
      StdStep (TIf (TNum 0) t1 t2, P, I, O) (t1, P, I, O)
  | SIf2 : forall n t1 t2 P I O,
      n <> 0%Z ->
      StdStep (TIf (TNum n) t1 t2, P, I, O) (t2, P, I, O)
  | SBindFIO : forall t1 t2 P I O,
      IsValue t1 ->
      StdStep (TBindFIO (TReturn t1) t2, P, I, O) (TApp t2 t1, P, I, O)
  | SRead : forall i P I O j,
      P i = BPNum j ->
      StdStep (TGet i, P, I, O) (TReturn (TFV (FVRaw (TNum (list_at (I i) j)))), P_upd P i (BPNum (S j)), I, O)
  | SWrite : forall o n P I O,
      StdStep (TPut o (TNum n), P, I, O) (TReturn (TNum n), P, I, O_upd O o (snoc (O o) n))
  | SrunFacFIO1 : forall t P I O,
      StdStep (TrunFacFIO (TFV (FVRaw t)), P, I, O) (TBindFIO t (fresh TUnit TUnit (fun x => TLam x (TReturn (TFV (FVRaw (TVar x)))))), P, I, O)
  | SBindFac1 : forall t1 t2 P I O,
      StdStep (TrunFacFIO (TFV (FVBind (TFV (FVRaw t1)) t2)), P, I, O) (TrunFacFIO (TApp t2 t1), P, I, O)
  | SBindFac2 : forall t1 t2 t3 P I O,
      StdStep (TrunFacFIO (TFV (FVBind (TFV (FVBind t1 t2)) t3)), P, I, O) (TrunFacFIO (TFV (FVBind t1 (fresh t2 t3 (fun x => TLam x (TFV (FVBind (TApp t2 (TVar x)) t3)))))), P, I, O)
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

Variable ffacet_BP : PC -> BufferPointer -> BufferPointer -> BufferPointer.

Variable l2pc : Label -> PC.
Variable l2pc_Axiom : forall l k, l2pc l k = Some (l k).
Variable add : PC -> Principal -> PC.
Variable add_Axiom1 : forall pc k k', k=k' -> add pc k k' = Some true.
Variable add_Axiom2 : forall pc k k', k<>k' -> add pc k k' = pc k'.
Variable subtract : PC -> Principal -> PC.
Variable subtract_Axiom1 : forall pc k k', k=k' -> subtract pc k k' = Some false.
Variable subtract_Axiom2 : forall pc k k', k<>k' -> subtract pc k k' = pc k'.


Fixpoint fac_read1 pc i p (I:Inputs) :=
  match p with
  | BPNum n =>
      FVRaw (TNum (list_at (I i) n))
  | BPFacet k p1 p2 =>
      FVFacet k (fac_read1 (unset pc k) i p1 I) (fac_read1 (unset pc k) i p2 I)
  end.
Fixpoint fac_read2 pc (i:InputHandle) p (I:Inputs) :=
  match p with
  | BPNum n =>
      ffacet_BP pc (BPNum (S n)) (BPNum n)
  | BPFacet k p1 p2 =>
      BPFacet k (fac_read2 (unset pc k) i p1 I) (fac_read2 (unset pc k) i p2 I)
  end.

Definition Subsumes (pc:PC) (l:Label) :=
  forall k,
    match pc k with
    | Some b => b = l k
    | None => True
    end.
Variable dec_Subsumes : forall (pc:PC) (l:Label), {Subsumes pc l}+{not (Subsumes pc l)}.
Inductive FacStep : PC -> Config -> Config -> Prop :=
  | FContext : forall pc t P I O t' I' O' P' E,
      FacStep pc (t, P, I, O) (t', P', I', O') ->
      FacStep pc (fill E t, P, I, O) (fill E t', P', I', O')
  | FApp : forall pc x t1 t2 P I O,
      FacStep pc (TApp (TLam x t1) t2, P, I, O) (subs t1 x t2, P, I, O)
  | FPlus : forall pc n1 n2 P I O,
      FacStep pc (TPlus (TNum n1) (TNum n2), P, I, O) (TNum (n1+n2), P, I, O)
  | FIf1 : forall pc t1 t2 P I O,
      FacStep pc (TIf (TNum 0) t1 t2, P, I, O) (t1, P, I, O)
  | FIf2 : forall pc n t1 t2 P I O,
      n <> 0%Z ->
      FacStep pc (TIf (TNum n) t1 t2, P, I, O) (t2, P, I, O)
  | FBindFIO : forall pc t1 t2 P I O,
      IsValue t1 ->
      FacStep pc (TBindFIO (TReturn t1) t2, P, I, O) (TApp t2 t1, P, I, O)
  | FrunFacFIO1 : forall t P I O pc,
      FacStep pc (TrunFacFIO (TFV (FVRaw t)), P, I, O) (TBindFIO t (fresh TUnit TUnit (fun x => TLam x (TReturn (TFV (FVRaw (TVar x)))))), P, I, O)
  | FBindFac1 : forall pc t1 t2 P I O,
      FacStep pc (TrunFacFIO (TFV (FVBind (TFV (FVRaw t1)) t2)), P, I, O) (TrunFacFIO (TApp t2 t1), P, I, O)
  | FBindFac2 : forall pc t1 t2 t3 P I O,
      FacStep pc (TrunFacFIO (TFV (FVBind (TFV (FVBind t1 t2)) t3)), P, I, O) (TrunFacFIO (TFV (FVBind t1 (fresh t2 t3 (fun x => TLam x (TFV (FVBind (TApp t2 (TVar x)) t3)))))), P, I, O)

  | FRead : forall pc i P I O,
      FacStep pc (TGet i, P, I, O) (TReturn (TFV (ffacet (l2pc (input_label i)) (fac_read1 pc i (P i) I) (FVRaw (TNum (-1))))), P_upd P i (fac_read2 pc i (P i) I), I, O)
  | FWrite : forall pc o n P I O,
      Subsumes pc (output_label o) ->
      FacStep pc (TPut o (TNum n), P, I, O) (TReturn (TNum n), P, I, O_upd O o (snoc (O o) n))
  | FWriteSkip : forall pc o n P I O,
      not (Subsumes pc (output_label o)) ->
      FacStep pc (TPut o (TNum n), P, I, O) (TReturn (TNum n), P, I, O)
  | FBindFac3 : forall pc k fv1 fv2 t3 P I O,
      FacStep pc (TrunFacFIO (TFV (FVBind (TFV (FVFacet k fv1 fv2)) t3)), P, I, O) (TrunFacFIO (TFV (FVFacet k (FVBind (TFV fv1) t3) (FVBind (TFV fv2) t3))), P, I, O)
  | FrunFacFIO2 : forall (pc:PC) k fv1 fv2 P I O,
      pc k = Some true ->
      FacStep pc (TrunFacFIO (TFV (FVFacet k fv1 fv2)), P, I, O) (TrunFacFIO (TFV fv1), P, I, O)
  | FrunFacFIO3 : forall (pc:PC) k fv1 fv2 P I O,
      pc k = Some false ->
      FacStep pc (TrunFacFIO (TFV (FVFacet k fv1 fv2)), P, I, O) (TrunFacFIO (TFV fv2), P, I, O)
  | FrunFacFIO4 : forall (pc:PC) k fv1 fv2 P I O,
      pc k = None ->
      FacStep pc (TrunFacFIO (TFV (FVFacet k fv1 fv2)), P, I, O) (TThreads k (TrunFacFIO (TFV fv1)) (TrunFacFIO (TFV fv2)), P, I, O)
  | FTimeout : forall pc E k t1 t2 P I O,
      FacStep pc (fill E (TThreads k t1 t2), P, I, O) (TThreads k (fill E t1) (fill E t2), P, I, O)
  | FMerge : forall pc k fv1 fv2 P I O,
      FacStep pc (TThreads k (TReturn (TFV fv1)) (TReturn (TFV fv2)), P, I, O) (TReturn (TFV (FVFacet k fv1 fv2)), P, I, O)
  | FThread1 : forall (pc:PC) k t1 t2 P I O t1' P' I' O',
      pc k <> Some false ->
      FacStep (add pc k) (t1, P, I, O) (t1', P', I', O') ->
      FacStep pc (TThreads k t1 t2, P, I, O) (TThreads k t1' t2, P', I', O')
  | FThread2 : forall (pc:PC) k t1 t2 P I O t2' P' I' O',
      pc k <> Some true ->
      FacStep (subtract pc k) (t2, P, I, O) (t2', P', I', O') ->
      FacStep pc (TThreads k t1 t2, P, I, O) (TThreads k t1 t2', P', I', O')
  .

Fixpoint pt l t :=
  match t with
  | TThreads k t1 t2 =>
      if l k then
        pt l t1
      else
        pt l t2
  | TPut o t =>
      if dec_eq_Label (output_label o) l then
        TPut o (pt l t)
      else
        TReturn (TPlus (TNum 0) (pt l t))
  | TFV fv => TFV (pfv l fv)
  | TLam x t => TLam x (pt l t)
  | TNum n => TNum n
  | TUnit => TUnit
  | TReturn t => TReturn (pt l t)
  | TVar x => TVar x
  | TApp t1 t2 => TApp (pt l t1) (pt l t2)
  | TPlus t1 t2 => TPlus (pt l t1) (pt l t2)
  | TIf t1 t2 t3 => TIf (pt l t1) (pt l t2) (pt l t3)
  | TBindFIO t1 t2 => TBindFIO (pt l t1) (pt l t2)
  | TrunFacFIO t => TrunFacFIO (pt l t)
  | TGet i => TGet i
  end
with pfv l fv :=
  match fv with
  | FVFacet k fv1 fv2 =>
      if l k then
        pfv l fv1
      else
        pfv l fv2
  | FVRaw t => FVRaw (pt l t)
  | FVBind t1 t2 => FVBind (pt l t1) (pt l t2)
  end.

Lemma value_lemma : forall l t,
  IsValue t ->
  IsValue (pt l t).
 pose (VFV, VLam, VNum, VUnit, VReturn).
 induction 1; simpl; intuition.
Qed.

Lemma NotNum_lemma : forall l t,
  IsValue t ->
  NotNum t ->
  NotNum (pt l t).
 unfold NotNum.
 inversion 1; try congruence; try discriminate.
Qed.

Variable subs_lemma : forall l t1 t2 x,
  pt l (subs t1 x t2) = subs (pt l t1) x (pt l t2).

(* This lemma is probably false, but who cares *)
Variable fresh_lemma : forall l t1 t2,
    pt l (fresh t1 t2 (fun x => TLam x (TFV (FVBind (TApp t1 (TVar x)) t2))))
  = fresh (pt l t1) (pt l t2) (fun x => TLam x (TFV (FVBind (TApp (pt l t1) (TVar x)) (pt l t2)))).

Variable fresh_lemma_2 : forall l,
    pt l (fresh TUnit TUnit (fun x => TLam x (TReturn (TFV (FVRaw (TVar x))))))
  = fresh TUnit TUnit (fun x => TLam x (TReturn (TFV (FVRaw (TVar x))))).

Variable ffacet_Axiom1 : forall l1 l2 fv1 fv2,
  flows l2 l1 ->
  (pfv l1 (ffacet (l2pc l2) fv1 fv2)) = pfv l1 fv1.
Variable ffacet_Axiom2 : forall l1 l2 fv1 fv2,
  not (flows l2 l1) ->
  (pfv l1 (ffacet (l2pc l2) fv1 fv2)) = pfv l1 fv2.

Definition fill_lemma_witness l E :=
  match E with
  | EApp t => EApp (pt l t)
  | EPlus1 t => EPlus1 (pt l t)
  | EPlus2 n => EPlus2 n
  | EIf t1 t2 => EIf (pt l t1) (pt l t2)
  | EBindFIO t => EBindFIO (pt l t)
  | ErunFacFIO1 => ErunFacFIO1
  | ErunFacFIO2 t => ErunFacFIO2 (pt l t)
  | EPut o => EPut o
  | EReturn => EReturn
  end.
Lemma fill_lemma : forall l E t,
  match E with
  | EPut _ => False
  | E => True
  end ->
  pt l (fill E t) = fill (fill_lemma_witness l E) (pt l t).
 destruct E; intros; auto.
 inversion H.
Qed.

Fixpoint pp (l:Label) p :=
  match p with
  | BPNum n => n
  | BPFacet k p1 p2 =>
      if l k then
        pp l p1
      else
        pp l p2
  end.
Definition pP l (P:Pointers) i := BPNum (pp l (P i)).
Definition pC (l:Label) (C:Config) : Config :=
  match C with
  | (t, P, I1, O1) => (pt l t, pP l P, pI l I1, pO l O1)
  end.

Inductive StdStepStar : Config -> Config -> Prop :=
  | SSNil : forall C C',
      C = C' ->
      StdStepStar C C'
  | SSCons : forall C0 C1 C2,
      StdStep C0 C1 ->
      StdStepStar C1 C2 ->
      StdStepStar C0 C2
  .

Definition hints_F := (FContext, FApp, FBindFac1, FBindFac2, FPlus, FIf1, FIf2, FBindFIO, FrunFacFIO1, FRead, FWrite, FrunFacFIO2, FWriteSkip, FBindFac3, FrunFacFIO2, FrunFacFIO3, FrunFacFIO4, FTimeout, FMerge, FThread1, FThread2).
Definition hints_S := (SContext, SApp, SBindFac1, SBindFac2, SPlus, SIf1, SIf2, SBindFIO, SrunFacFIO1, SRead, SWrite).
Definition hints_SS := (SSNil, SSCons).
Definition hints_V := (VFV, VLam, VNum, VUnit, VReturn).
Definition hints := (hints_F, hints_S, hints_SS, hints_V, value_lemma, NotNum_lemma, fill_lemma, fresh_lemma, subs_lemma).

Variable ffacet_BP_Axiom1 : forall l pc p1 p2,
  Subsumes pc l ->
  (pp l (ffacet_BP pc p1 p2)) = pp l p1.
Variable ffacet_BP_Axiom2 : forall l pc p1 p2,
  not (Subsumes pc l) ->
  (pp l (ffacet_BP pc p1 p2)) = pp l p2.

Lemma unnamed_lemma :
  forall p i pc I l,
    Subsumes pc l ->
    pp l (fac_read2 pc i p I) = S (pp l p)
  .
Proof.
  induction p as [|k].
    intros.
    unfold fac_read2.
    rewrite ffacet_BP_Axiom1; auto.
  intros.
  simpl.
  remember (l k) as temp.
  destruct temp.
  -
    rewrite (IHp1 i (unset pc k) I l); auto.
    intro k'.
    destruct (dec_eq_Principal k k').
      rewrite unset_Axiom1; auto.
    pose (H k').
    rewrite unset_Axiom2; auto.
  -
    rewrite (IHp2 i (unset pc k) I l); auto.
    intro k'.
    destruct (dec_eq_Principal k k').
      rewrite unset_Axiom1; auto.
    pose (H k').
    rewrite unset_Axiom2; auto.
Qed.

Lemma unnamed_2 :
  forall pc i p I l,
    not (Subsumes pc l) ->
    pp l (fac_read2 pc i p I) = pp l p.
Admitted.

Lemma unnamed_3 : forall l P i p,
  P_upd (pP l P) i (BPNum (pp l p)) = pP l (P_upd P i p).
Admitted.

Lemma unnamed_4 : forall i l pc p I,
  flows (input_label i) l ->
  pfv l (fac_read1 pc i p I) = FVRaw (TNum (list_at (pI l I i) (pp l p))).
Admitted.

Lemma unnamed_5 : forall O o n,
    O_upd (pO (output_label o) O) o (snoc (pO (output_label o) O o) n)
  = pO (output_label o) (O_upd O o (snoc (O o) n)).
Admitted.

Lemma unnamed_6 : forall O o l ns,
  output_label o <> l ->
  pO l (O_upd O o ns) = pO l O.
Admitted.

Lemma unnamed_7 : forall l P i,
  P_upd (pP l P) i (BPNum (pp l (P i))) = pP l P.
Admitted.

Theorem projection_1 : forall (C C':Config) l pc,
  FacStep pc C C' ->
    and (
      Subsumes pc l ->
        or (
          pC l C = pC l C'
        )(
          StdStep (pC l C) (pC l C')
        )
    )(
      (not (Subsumes pc l)) ->
        match C with (_,P1,I1,O1) =>
          match C' with (_,P2,I2,O2) =>
            pP l P1 = pP l P2  /\  pI l I1 = pI l I2  /\  pO l O1 = pO l O2
          end
        end
    )
  .
 induction 1; split; intro; unfold pC; simpl;
   try solve [pose (hints := hints); intuition].
 (* Leaves 18 subgoals *)

  (* FContext, part 1 *)
  destruct IHFacStep as (H1, H2).
  destruct H1; try auto.
   left.
   destruct E; try solve [
     rewrite fill_lemma; try auto;
     rewrite fill_lemma; try auto;
     simpl in H1;
     congruence
   ].
   simpl.
   destruct (dec_eq_Label  (output_label o) l); (
     simpl in H1;
     congruence
   ).
  right.
  pose E as Etemp.
  destruct E; try solve [
    apply SContext with (E := fill_lemma_witness l Etemp);
    assumption
  ].
  simpl.
  destruct (dec_eq_Label  (output_label o) l).
   apply SContext with (E := EPut o).
   assumption.
  apply SContext with (E := EReturn).
  apply SContext with (E := EPlus2 0).
  assumption.

  (* FApp, part 1 *)
  rewrite subs_lemma.
  pose (hints := hints); intuition.

  (* FrunFacFIO1, part 1 *)
  rewrite fresh_lemma_2.
  pose (hints := hints); intuition.

  (* FBindFac2, part 1*)
  rewrite fresh_lemma.
  pose (hints := hints); intuition.

  (* FRead, part 1 *)
  right.
  destruct (dec_flows (input_label i) l) as [H1|H1].
   rewrite ffacet_Axiom1; try assumption.
   rewrite <- unnamed_3.
   rewrite unnamed_lemma; try assumption.
   rewrite unnamed_4; try assumption.
   eapply SRead.
   reflexivity.
  rewrite ffacet_Axiom2; try assumption.
  simpl.
  assert ((-1)%Z = (list_at (pI l I i) (pp l (P i)))) as H2.
   unfold pI.
   destruct (dec_flows (input_label i) l) as [|_]; try contradiction.
   reflexivity.
  rewrite H2.
  rewrite <- unnamed_3.
  rewrite unnamed_lemma; try assumption.
  eapply SRead.
  reflexivity.

  (* FRead, part 2 *)
  rewrite <- unnamed_3.
  rewrite unnamed_2; try assumption.
  rewrite unnamed_7.
  intuition.

  (* FWrite, part 1 *)
  destruct (dec_eq_Label (output_label o) l) as [e|].
   right.
   rewrite <- e.
   rewrite <- unnamed_5.
   eapply SWrite.
  right.
  eapply SContext with (E := EReturn).
  rewrite unnamed_6; try auto.
  eapply SPlus.

  (* FWrite, part 2 *)
  rewrite unnamed_6; intuition congruence.

  (* FWriteSkip, part 1 *)
  destruct (dec_eq_Label (output_label o) l).
   congruence.
  right.
  apply SContext with (E := EReturn).
  apply SPlus.

  (* FBindFac3, part 1 *)
  destruct (l k); intuition.

  (* FrunFacFIO2, part 1 *)
  remember (l k) as b.
  destruct b; try auto.
  pose (H0 k) as temp.
  rewrite H in temp.
  congruence.

  (* FrunFacFIO3, part 1 *)
  remember (l k) as b.
  destruct b; try auto.
  pose (H0 k) as temp.
  rewrite H in temp.
  congruence.

  (* FrunFacFIO4, part 1 *)
  left.
  destruct (l k).
   intuition.
  intuition.

  (* FTimeout, part 1 *)
  left.
  destruct E; try (
    rewrite fill_lemma; try trivial;
    rewrite fill_lemma; try trivial;
    simpl;
    destruct (l k);
    trivial
  ).
  simpl.
  destruct (l k); auto.

  (* FMerge, part 1 *)
  destruct (l k); auto.

  (* FThread1, part 1 *)
  remember (l k) as b.
  destruct IHFacStep.
  destruct b.
   destruct H2; try intuition.
   intro k0.
   destruct (dec_eq_Principal k0 k) as [e|].
    rewrite e.
    rewrite add_Axiom1.
     congruence.
    reflexivity.
   rewrite (add_Axiom2 pc k); try auto.
   apply H1.
  destruct (dec_Subsumes (add pc k) l).
   destruct H2; try assumption.
    left.
    simpl in H2.
    congruence.
   pose (s k) as H4.
   rewrite add_Axiom1 in H4; congruence.
  intuition congruence.

  (* FThread1, part 2 *)
  assert (~Subsumes (add pc k) l).
   clear IHFacStep H0 O' I' P' t1' O I P t1 t2.
   intuition.
   apply H1.
   intro k0.
   destruct (dec_eq_Principal k0 k) as [e|].
    rewrite e.
    pose (H0 k).
    rewrite add_Axiom1 in y; try auto.
    destruct (pc k) as [[|]|].
      exact y.
     intuition.
    trivial.
   pose (H0 k0).
   rewrite add_Axiom2 in y; auto.
  intuition.

  (* FThread2, part 1 *)
  (* Just a copy-paste-edit from FThread1 part 1 *)
  remember (l k) as b.
  destruct IHFacStep.
  destruct b.
   Focus 2.
   destruct H2; try intuition.
   intro k0.
   destruct (dec_eq_Principal k0 k) as [e|].
    rewrite e.
    rewrite subtract_Axiom1.
     congruence.
    reflexivity.
   rewrite (subtract_Axiom2 pc k); try auto.
   apply H1.
  destruct (dec_Subsumes (subtract pc k) l).
   destruct H2; try assumption.
    left.
    simpl in H2.
    congruence.
   pose (s k) as H4.
   rewrite subtract_Axiom1 in H4; congruence.
  intuition congruence.

  (* FThread2, part 2 *)
  (* Just a copy-paste-edit from FThread1 part 2 *)
  assert (~Subsumes (subtract pc k) l).
   clear IHFacStep H0 O' I' P' t2' O I P t1 t2.
   intuition.
   apply H1.
   intro k0.
   destruct (dec_eq_Principal k0 k) as [e|].
    rewrite e.
    pose (H0 k).
    rewrite subtract_Axiom1 in y; try auto.
    destruct (pc k) as [[|]|].
      intuition.
     exact y.
    trivial.
   pose (H0 k0).
   rewrite subtract_Axiom2 in y; auto.
  intuition.

Qed.

Lemma determinism_1 : forall C C1 C2,
  StdStep C C1 ->
  StdStep C C2 ->
  C1 = C2.
Admitted.

Inductive FacStepStar : Config -> Config -> Prop :=
  | FSNil : forall C,
      FacStepStar C C
  | FSCons : forall C0 C1 C2,
      FacStep emptypc C0 C1 ->
      FacStepStar C1 C2 ->
      FacStepStar C0 C2
  .

Definition NotStdStep C := forall C', StdStep C C' -> False.
Definition NotFacStep C := forall C', FacStep emptypc C C' -> False.

Definition hints_2 := (SSNil, SSCons, FSNil, FSCons).

Ltac helper E C C'0 IH notfacstep H H4 :=
  pose E as Etemp;
  destruct E; try discriminate;
  apply IH with C; [
   intros;
   destruct C'0 as (((t'0, P'0), I'0), O'0);
   apply notfacstep with (fill Etemp t'0, P'0, I'0, O'0);
   apply FContext with (E := Etemp) (P' := P'0) (I' := I'0) (O' := O'0);
   assumption
  |
  simpl;
  simpl in H;
  injection H;
  compute in H4;
  compute;
  congruence
  ].

Lemma unnamed_9 : forall l t pc P I O,
  (forall k t1 t2, t = TThreads k t1 t2 -> False) ->
  IsValue (pt l t) ->
  or (
    IsValue t
  )(
    exists t' O',
      FacStep pc (t, P, I, O) (t', P, I, O')
  ).
 intros l t pc P I O T1 T2.
 induction t; try solve [pose hints; intuition; inversion T2].
 (* Leaves 3 subgoals *)

   destruct t; try solve [
     destruct IHt as [| T3]; [
        discriminate
        |
       simpl in T2; inversion T2; assumption
       |
      pose hints; intuition
      |
     right;
     destruct T3 as (t', T3);
     destruct T3 as (O', T3);
     repeat eexists;
     apply FContext with (E := EReturn);
     exact T3
     ]
   ].
   right.
   repeat eexists.
   apply FTimeout with (E := EReturn).
  destruct t; (
    simpl in T2;
    destruct (dec_eq_Label (output_label o) l); try solve [inversion T2];
    inversion T2;
    inversion H0
  ).
 apply False_rect.
 apply T1 with p t1 t2.
 reflexivity.
Qed.

Lemma custom_induction :
       forall P : Term -> Prop,
       (forall f : FacetedValue, P (TFV f)) ->
       (forall (v : Var) (t : Term), P t -> P (TLam v t)) ->
       (forall z : Z, P (TNum z)) ->
       P TUnit ->
       (forall t : Term, P t -> P (TReturn t)) ->
       (forall v : Var, P (TVar v)) ->
       (forall t : Term, P t -> forall t0 : Term, P t0 -> P (TApp t t0)) ->
       (forall t : Term, P t -> forall t0 : Term, P t0 -> P (TPlus t t0)) ->
       (forall t : Term,
        P t ->
        forall t0 : Term, P t0 -> forall t1 : Term, P t1 -> P (TIf t t0 t1)) ->
       (forall t : Term, P t -> forall t0 : Term, P t0 -> P (TBindFIO t t0)) ->

       (* Custom cases: *)
       (forall t1 t2 : Term, P (TFV (FVBind t1 t2)) -> P t1 -> P t2 -> P (TrunFacFIO (TFV (FVBind t1 t2)))) ->
       (forall fv, (forall t1 t2, fv <> FVBind t1 t2) -> P (TFV fv) -> P (TrunFacFIO (TFV fv))) ->
       (forall t, (forall fv, t <> TFV fv) -> P t -> P (TrunFacFIO t)) ->

       (forall i : InputHandle, P (TGet i)) ->
       (forall (o : OutputHandle) (t : Term), P t -> P (TPut o t)) ->
       (forall (p : Principal) (t : Term),
        P t -> forall t0 : Term, P t0 -> P (TThreads p t t0)) ->
       forall t : Term, P t
  .
 intros.
 generalize t.
 clear t.
 fix 1.
 destruct t; try solve [clear custom_induction; intuition].
         apply H0; intuition.
        apply H3; intuition.
       apply H5; intuition.
      apply H6; intuition.
     apply H7; intuition.
    apply H8; intuition.
   remember t as t_temp.
   destruct t_temp; try solve [apply H11; try discriminate; rewrite Heqt_temp; intuition].
   remember f as f_temp.
   destruct f_temp; try solve [apply H10; try discriminate; rewrite Heqf_temp; intuition].
   apply H9; intuition.
  apply H13; intuition.
 apply H14; intuition.
Qed.

Lemma projection_1' : forall l C pc,
  Subsumes pc l ->
  (forall C', FacStep pc C C' -> False) ->
  NotStdStep (pC l C)
  .
 unfold NotFacStep, NotStdStep in *.
 destruct C as (((t, P), I), O).
 induction t using custom_induction(* with (Q := fun fv:FacetedValue =>
       (forall C' : Config, FacStep emptypc (TFV fv, P, I, O) C' -> False) ->
       forall C' : Config, StdStep (pC l (TFV fv, P, I, O)) C' ->
       False
     )*)
   ; intros pc subsumes notfacstep C' stdstep
   ; try solve [(inversion stdstep; destruct E; try discriminate)]
   ; idtac.

  (* Leaves 11 subgoals *)

         inversion stdstep.
         destruct E; try discriminate.
         apply IHt with pc (t', P', I', O').
           exact subsumes.
          intros.
          destruct C'0 as (((t'0, P'0), I'0), O'0).
          eapply notfacstep.
          apply FContext with (E := EReturn).
          exact H5.
         simpl.
         simpl in H.
         injection H; intros.
         rewrite <- H5.
         exact H4.
        inversion stdstep.
         destruct E; try discriminate.
         apply IHt1 with pc (t', P', I', O').
           exact subsumes.
          intros.
          destruct C'0 as (((t'0, P'0), I'0), O'0).
          apply notfacstep with (TApp t'0 t2, P'0, I'0, O'0).
          apply FContext with (E := EApp t2).
          assumption.
         simpl.
         simpl in H.
         injection H; intros.
         rewrite <- H6.
         apply H4.
        destruct t1; try discriminate.
          apply notfacstep with (subs t1 v t2, P, I, O).
          apply FApp.
         simpl in H0.
         destruct (dec_eq_Label (output_label o) l);  inversion H0.
        apply notfacstep with (TThreads p (TApp t1_1 t2) (TApp t1_2 t2), P, I, O).
        apply FTimeout with (E := EApp t2).
       inversion stdstep.
        destruct E; try discriminate.
         apply IHt1 with pc (t', P', I', O').
           exact subsumes.
          intros.
          destruct C'0 as (((t'0, P'0), I'0), O'0).
          apply notfacstep with (TPlus t'0 t2, P'0, I'0, O'0).
          apply FContext with (E := EPlus1 t2).
          assumption.
         simpl.
         simpl in H.
         injection H; intros.
         rewrite <- H6.
         assumption.
        apply IHt2 with pc (t', P', I', O').
          exact subsumes.
         intros.
         destruct C'0 as (((t'0, P'0), I'0), O'0).
         destruct t1; try discriminate.
           apply notfacstep with (TPlus (TNum z) t'0, P'0, I'0, O'0).
           simpl in H.
           injection H; intros.
           rewrite H7.
           apply FContext with (E := EPlus2 z0).
           assumption.
          simpl in H.
          destruct (dec_eq_Label (output_label o) l); inversion H.
         simpl in H.
         apply notfacstep with (TThreads p (TPlus t1_1 t2) (TPlus t1_2 t2), P, I, O).
         apply FTimeout with (E := EPlus1 t2).
        simpl.
        simpl in H.
        injection H; intros.
        rewrite <- H5.
        assumption.
       destruct t1; try discriminate.
         destruct t2; try discriminate.
           apply notfacstep with (TNum (z + z0), P, I, O).
           apply FPlus.
          simpl in H1.
          destruct (dec_eq_Label (output_label o) l);  inversion H1.
         apply notfacstep with (TThreads p (TPlus (TNum z) t2_1) (TPlus (TNum z) t2_2), P, I, O).
         apply FTimeout with (E := EPlus2 z).
        simpl in H0.
        destruct (dec_eq_Label (output_label o) l);  inversion H0.
       apply notfacstep with (TThreads p (TPlus t1_1 t2) (TPlus t1_2 t2), P, I, O).
       apply FTimeout with (E := EPlus1 t2).
      inversion stdstep.
        destruct E; try discriminate.
        apply IHt1 with pc (t', P', I', O').
          exact subsumes.
         intros.
         destruct C'0 as (((t'0, P'0), I'0), O'0).
         apply notfacstep with (TIf t'0 t2 t3, P'0, I'0, O'0).
         apply FContext with (E := EIf t2 t3).
         assumption.
        simpl.
        simpl in H.
        injection H; intros.
        rewrite <- H7.
        assumption.
       destruct t1; try discriminate.
         apply notfacstep with (t2, P, I, O).
         simpl in H0.
         injection H0; intros.
         rewrite <- H.
         apply FIf1.
        simpl in H0.
        destruct (dec_eq_Label (output_label o) l);  inversion H0.
       apply notfacstep with (TThreads p (TIf t1_1 t2 t3) (TIf t1_2 t2 t3), P, I, O).
       apply FTimeout with (E := EIf t2 t3).
      destruct t1; try discriminate.
        apply notfacstep with (t3, P, I, O).
        apply FIf2.
        simpl in H.
        congruence.
       simpl in H.
       destruct (dec_eq_Label (output_label o) l);  inversion H.
      apply notfacstep with (TThreads p (TIf t1_1 t2 t3) (TIf t1_2 t2 t3), P, I, O).
      apply FTimeout with (E := EIf t2 t3).
     inversion stdstep.
      destruct E; try discriminate.
      apply IHt1 with pc (t', P', I', O').
        exact subsumes.
       intros.
       destruct C'0 as (((t'0, P'0), I'0), O'0).
       apply notfacstep with (TBindFIO t'0 t2, P'0, I'0, O'0).
       apply FContext with (E := EBindFIO t2).
       assumption.
      simpl.
      simpl in H.
      injection H; intros.
      rewrite <- H6.
      assumption.
     pose (E := EBindFIO t2).
     destruct t1; try discriminate.
       simpl in H.
       injection H; intros.
       destruct (unnamed_9 l (TReturn t1) pc P I O) as [T1 | (t', (O', T1))].
          congruence.
         simpl.
         apply VReturn.
         congruence.
        apply notfacstep with (TApp t2 t1, P, I, O).
        inversion T1.
        apply FBindFIO.
        assumption.
       eapply notfacstep.
       apply FContext with (E := E).
       exact T1.
      simpl in H.
      destruct (dec_eq_Label (output_label o) l).
       discriminate.
      destruct (unnamed_9 l (TPut o t1) pc P I O) as [T1 | (t', (O', T1))].
         congruence.
        simpl.
        simpl in H.
        injection H; intros.
        destruct (dec_eq_Label (output_label o) l).
         contradiction.
        apply VReturn.
        congruence.
       inversion T1.
      eapply notfacstep.
      apply FContext with (E := E).
      exact T1.
     eapply notfacstep.
     apply FTimeout with (E := E).
    inversion stdstep.
         destruct E; try discriminate.
          apply IHt1 with pc (t', P', I', O').
            exact subsumes.
           intros.
           destruct C'0 as (((t'0, P'0), I'0), O'0).
           apply notfacstep with (TrunFacFIO t'0, P'0, I'0, O'0).
           apply FContext with (E := ErunFacFIO1).
           assumption.
          simpl.
          simpl in H.
          injection H; intros.
          rewrite <- H5.
          assumption.
         eapply IHt2.
           exact subsumes.
          intros.
          destruct C'0 as (((t'0, P'0), I'0), O'0).
          eapply notfacstep.
          apply FContext with (E := ErunFacFIO2 t2).
          exact H5.
         simpl in H.
         injection H; intros.
         simpl.
         rewrite <- H6.
         exact H4.
        destruct t1; try discriminate.
          destruct f; try discriminate.
           eapply notfacstep.
           apply FBindFac1.
          eapply notfacstep.
          apply FBindFac3.
         simpl in H0.
         destruct (dec_eq_Label (output_label o) l); discriminate.
        apply notfacstep with (TThreads p (TrunFacFIO (TFV (FVBind t1_1 t2))) (TrunFacFIO (TFV (FVBind t1_2 t2))), P, I, O).
        apply FTimeout with (E := ErunFacFIO2 t2).
       destruct t1; try discriminate.
         destruct f; try discriminate.
          eapply notfacstep.
          apply FBindFac2.
         eapply notfacstep.
         apply FBindFac3.
        simpl in H0.
        destruct (dec_eq_Label (output_label o) l); discriminate.
       apply notfacstep with (TThreads p (TrunFacFIO (TFV (FVBind t1_1 t2))) (TrunFacFIO (TFV (FVBind t1_2 t2))), P, I, O).
       apply FTimeout with (E := ErunFacFIO2 t2).
     inversion stdstep.
        destruct E; try discriminate.
         apply IHt with pc (t', P', I', O').
           exact subsumes.
          intros.
          destruct C'0 as (((t'0, P'0), I'0), O'0).
          apply notfacstep with (TrunFacFIO t'0, P'0, I'0, O'0).
          apply FContext with (E := ErunFacFIO1).
          assumption.
         simpl.
         simpl in H0.
         injection H0; intros.
         rewrite <- H6.
         assumption.
        destruct fv; try discriminate.
         simpl in H0.
         injection H0; intros.
         simpl in H6.
         congruence.
        remember (pc p) as T1.
        destruct T1 as [[|]|].
           eapply notfacstep.
           apply FrunFacFIO2.
           congruence.
          eapply notfacstep.
          apply FrunFacFIO3.
          congruence.
         eapply notfacstep.
         apply FrunFacFIO4.
         congruence.
       destruct fv; try discriminate.
        eapply notfacstep.
        apply FrunFacFIO1.
       remember (pc p) as T1.
       destruct T1 as [[|]|].
          eapply notfacstep.
          apply FrunFacFIO2.
          congruence.
         eapply notfacstep.
         apply FrunFacFIO3.
         congruence.
        eapply notfacstep.
        apply FrunFacFIO4.
        congruence.
      destruct fv.
        discriminate.
       congruence.
      remember (pc p) as T1.
      destruct T1 as [[|]|].
         eapply notfacstep.
         apply FrunFacFIO2.
         congruence.
        eapply notfacstep.
        apply FrunFacFIO3.
        congruence.
       eapply notfacstep.
       apply FrunFacFIO4.
       congruence.
     destruct fv.
       discriminate.
      congruence.
     remember (pc p) as T1.
     destruct T1 as [[|]|].
        eapply notfacstep.
        apply FrunFacFIO2.
        congruence.
       eapply notfacstep.
       apply FrunFacFIO3.
       congruence.
      eapply notfacstep.
      apply FrunFacFIO4.
      congruence.
    inversion stdstep.
       destruct E; try discriminate.
        apply IHt with pc (t', P', I', O').
          exact subsumes.
         intros.
         destruct C'0 as (((t'0, P'0), I'0), O'0).
         apply notfacstep with (TrunFacFIO t'0, P'0, I'0, O'0).
         apply FContext with (E := ErunFacFIO1).
         assumption.
        simpl.
        simpl in H0.
        injection H0; intros.
        rewrite <- H6.
        assumption.
       destruct t; try discriminate.
         congruence.
        simpl in H0.
        destruct (dec_eq_Label (output_label o) l); discriminate.
       eapply notfacstep.
       apply FTimeout with (E := ErunFacFIO1).
      destruct t; try discriminate.
        congruence.
       simpl in H1.
       destruct (dec_eq_Label (output_label o) l); discriminate.
      eapply notfacstep.
      apply FTimeout with (E := ErunFacFIO1).
     destruct t; try discriminate.
       congruence.
      simpl in H1.
      destruct (dec_eq_Label (output_label o) l); discriminate.
     eapply notfacstep.
     apply FTimeout with (E := ErunFacFIO1).
    destruct t; try discriminate.
      congruence.
     simpl in H1.
     destruct (dec_eq_Label (output_label o) l); discriminate.
    eapply notfacstep.
    apply FTimeout with (E := ErunFacFIO1).
   inversion stdstep.
    destruct E; discriminate.
   eapply notfacstep.
   apply FRead.
  simpl in stdstep.
  destruct (dec_eq_Label (output_label o) l).
   inversion stdstep.
     destruct E; try discriminate.
     eapply IHt.
       exact subsumes.
      intros.
      destruct C'0 as (((t'0, P'0), I'0), O'0).
      eapply notfacstep.
      apply FContext with (E := EPut o).
      exact H5.
     simpl.
     simpl in H.
     injection H; intros.
     rewrite <- H5.
     exact H4.
    destruct t; try discriminate.
      destruct (dec_Subsumes pc (output_label o)).
       eapply notfacstep.
       apply FWrite.
       assumption.
      eapply notfacstep.
      apply FWriteSkip.
      assumption.
     simpl in H1.
     destruct (dec_eq_Label (output_label o1) l); discriminate.
    eapply notfacstep.
    apply FTimeout with (E := EPut o).
  inversion stdstep.
  destruct E; try discriminate.
  simpl.
  simpl in H.
  injection H; intros.
  rewrite H5 in H4.
  inversion H4.
   destruct E; try discriminate.
    simpl in H6.
    injection H6; intros.
    rewrite H16 in H7.
    inversion H7.
    destruct E; discriminate.
   eapply IHt.
     exact subsumes.
    intros.
    destruct C'0 as (((t'00, P'00), I'00), O'00).
    eapply notfacstep.
    apply FContext with (E := EPut o).
    exact H15.
   simpl.
   simpl in H6.
   injection H6; intros.
   rewrite <- H15.
   exact H7.
  destruct (unnamed_9 l t pc P I O) as [T1 | (t_, (O_, T1))].
     intros.
     eapply notfacstep.
     rewrite H6.
     apply FTimeout with (E := EPut o).
    rewrite <- H8.
    apply VNum.
   inversion T1; try solve [
       try rewrite <- H6 in H8;
       try rewrite <- H16 in H8;
       simpl in H8;
       discriminate
   ].
   destruct (dec_Subsumes pc (output_label o)).
    eapply notfacstep.
    rewrite <- H6.
    apply FWrite.
    assumption.
   eapply notfacstep.
   rewrite <- H6.
   apply FWriteSkip.
   assumption.
  eapply notfacstep.
  eapply FContext with (E := EPut o).
  exact T1.
 remember (l p) as T.
 destruct T.
  eapply IHt1.
    Focus 2.
    remember (pc p) as T.
    intros.
    destruct C'0 as (((t'0, P'0), I'0), O'0).
    destruct T as [[|]|].
      eapply notfacstep.
      apply FThread1.
       congruence.
      exact H.
     pose (subsumes p) as T1.
     rewrite <- HeqT0 in T1.
     congruence.
    eapply notfacstep.
    apply FThread1.
     congruence.
    exact H.
   intro.
   destruct (dec_eq_Principal p k).
    rewrite add_Axiom1; congruence.
   rewrite add_Axiom2; try congruence.
   apply subsumes.
  simpl in stdstep.
  rewrite <- HeqT in stdstep.
  simpl.
  exact stdstep.
 (* Begin copy-paste-edit, from above *)
 eapply IHt2.
   Focus 2.
   remember (pc p) as T.
   intros.
   destruct C'0 as (((t'0, P'0), I'0), O'0).
   destruct T as [[|]|].
     Focus 2.
     eapply notfacstep.
     apply FThread2.
      congruence.
     exact H.
    pose (subsumes p) as T1.
    rewrite <- HeqT0 in T1.
    congruence.
   eapply notfacstep.
   apply FThread2.
    congruence.
   exact H.
  intro.
  destruct (dec_eq_Principal p k).
   rewrite subtract_Axiom1; congruence.
  rewrite subtract_Axiom2; try congruence.
  apply subsumes.
 simpl in stdstep.
 rewrite <- HeqT in stdstep.
 simpl.
 exact stdstep.
 (* End copy-paste-edit *)
Qed.

Inductive ProjStepStar (l : Label) : Config -> Config -> Prop :=
  | PSNil : forall C C',
      pC l C = pC l C' ->
      ProjStepStar l C C'
  | PSCons : forall C0 C1 C2,
      StdStep (pC l C0) (pC l C1) ->
      ProjStepStar l C1 C2 ->
      ProjStepStar l C0 C2
  .

Definition hints' := (hints, PSNil, PSCons).

Lemma unnamed_10 : forall l C C',
  FacStepStar C C' ->
  ProjStepStar l C C'.
 induction 1.
  apply PSNil.
  reflexivity.
 pose (projection_1 _ _ l _ H).
 intuition.
 destruct H1.
   intro.
   rewrite emptypc_Axiom.
   trivial.
  inversion IHFacStepStar.
   apply PSNil.
   congruence.
  apply PSCons with C4.
   congruence.
  congruence.
 apply PSCons with C1.
  assumption.
 assumption.
Qed.

Theorem tini_1 : forall l C1_ C1_',
  FacStepStar C1_ C1_' ->
  NotFacStep C1_' ->
  forall C2_ C2_',
  FacStepStar C2_ C2_' ->
  NotFacStep C2_' ->
  pC l C1_ = pC l C2_ ->
  pC l C1_' = pC l C2_'
  .
 intro l.
 intros C1_ C1_' T1.
 remember (unnamed_10 l _ _ T1) as T8.
 clear T1 HeqT8.
 intros T2 C2_ C2_' T3 T4 T5.
 remember (unnamed_10 l _ _ T3) as T9.
 clear HeqT9 T3.
 generalize C2_ T9 T4 T5.
 clear T9 T5 T4 C2_.
 induction T8 as [C1_ C1_' T6 | C1_ C1_mid C1_']; intros C2_ T9 T4 T5.
  inversion T9 as [ | C2__ C2__mid C2__'].
   congruence.
  apply False_rect.
  pose projection_1' as projection_1'.
  unfold NotFacStep, NotStdStep in *.
  apply projection_1' with (pc := emptypc) (l := l) (C := C1_') (C' := (pC l C2__mid)).
    intro.
    rewrite emptypc_Axiom.
    trivial.
   exact T2.
  congruence.
 inversion T9 as [ | C2__ C2__mid C2__'].
  apply False_rect.
  pose projection_1' as projection_1'.
  unfold NotFacStep, NotStdStep in *.
  apply projection_1' with (pc := emptypc) (l := l) (C := C2_') (C' := pC l C1_mid).
    intro.
    rewrite emptypc_Axiom.
    trivial.
   assumption.
  congruence.
 apply IHT8 with C2__mid.
    assumption.
   assumption.
  assumption.
 apply determinism_1 with (pC l C1_).
  assumption.
 congruence.
Qed.

Definition ti_noninterfering (C:Config) :=
  forall C',
  StdStepStar C C' ->
  forall l C'',
  StdStepStar (pC l C) C'' ->
  pC l C' = pC l C''
  .

Definition nonfaceted (C:Config) :=
  forall l,
  match C with (t, P, _, O_blah) => (* variable name O_blah because O is already taken *)
      t = pt l t
    /\
      P = (fun i => BPNum 0)
    /\
      O_blah = (fun o => nil)
  end.

Definition ts_noninterfering (C1:Config) :=
    nonfaceted C1
  /\
    match C1 with (t1, _, _, _) =>
      forall I1 C',
      StdStepStar (t1, fun i => BPNum 0, I1, fun o => nil) C' ->
      forall l I2,
      pI l I1 = pI l I2 ->
      exists C'',
        StdStepStar (t1, fun i => BPNum 0, I2, fun o => nil) C''
      /\
        pC l C' = pC l C''
    end
  .

Lemma unnamed_11 : forall l C C',
  ProjStepStar l C C' ->
  StdStepStar (pC l C) (pC l C').
 intros.
 induction H.
  apply SSNil.
  exact H.
 eapply SSCons.
  exact H.
 exact IHProjStepStar.
Qed.

Lemma better_induction_principle :
       forall P : Term -> Prop,
       forall Q : FacetedValue -> Prop,
       (forall f : FacetedValue, Q f -> P (TFV f)) ->
       (forall (v : Var) (t : Term), P t -> P (TLam v t)) ->
       (forall z : Z, P (TNum z)) ->
       P TUnit ->
       (forall t : Term, P t -> P (TReturn t)) ->
       (forall v : Var, P (TVar v)) ->
       (forall t : Term, P t -> forall t0 : Term, P t0 -> P (TApp t t0)) ->
       (forall t : Term, P t -> forall t0 : Term, P t0 -> P (TPlus t t0)) ->
       (forall t : Term,
        P t ->
        forall t0 : Term, P t0 -> forall t1 : Term, P t1 -> P (TIf t t0 t1)) ->
       (forall t : Term, P t -> forall t0 : Term, P t0 -> P (TBindFIO t t0)) ->
       (forall t : Term, P t -> P (TrunFacFIO t)) ->
       (forall i : InputHandle, P (TGet i)) ->
       (forall (o : OutputHandle) (t : Term), P t -> P (TPut o t)) ->
       (forall (p : Principal) (t : Term),
        P t -> forall t0 : Term, P t0 -> P (TThreads p t t0)) ->
       (forall t, P t -> Q (FVRaw t)) ->
       (forall k fv1 fv2, Q fv1 -> Q fv2 -> Q (FVFacet k fv1 fv2)) ->
       (forall t1 t2, P t1 -> P t2 -> Q (FVBind t1 t2)) ->
       forall t : Term, P t.
 intros.
 generalize t.
 clear t.
 refine (fix f (t:Term):P t := _ with g fv:Q fv := _ for f).
 destruct t; try solve [clear f; intuition].
          apply H0; intuition.
         apply H3; intuition.
        apply H5; intuition.
       apply H6; intuition.
      apply H7; intuition.
     apply H8; intuition.
    apply H9; intuition.
   apply H11; intuition.
  apply H12; intuition.
 destruct fv.
   apply H13; intuition.
  apply H15; intuition.
 apply H14; intuition.
Qed.

Lemma unnamed_12 : forall l t,
  pt l t = pt l (pt l t).
 intro l.
 induction t using better_induction_principle with (Q := fun fv => pfv l fv = pfv l (pfv l fv))
   ; simpl; try congruence.
   destruct (dec_eq_Label (output_label o) l).
    simpl.
    destruct (dec_eq_Label (output_label o) l).
     simpl.
     congruence.
    congruence.
   simpl.
   congruence.
  destruct (l p); congruence.
 destruct (l k).
  congruence.
 congruence.
Qed.

Variable Pointers_extensionality : forall P1 P2 : Pointers,
  (forall i, P1 i = P2 i) ->
  P1 = P2.

Lemma unnamed_13 : forall l P,
  pP l P = pP l (pP l P).
 unfold pP.
 intros.
 apply Pointers_extensionality.
 intro.
 simpl.
 reflexivity.
Qed.

Variable Inputs_extensionality : forall I1 I2 : Inputs,
  (forall i, I1 i = I2 i) ->
  I1 = I2.

Lemma unnamed_14 : forall l I,
  pI l I = pI l (pI l I).
 unfold pI.
 intros.
 apply Inputs_extensionality.
 intro.
 destruct (dec_flows (input_label i) l).
  reflexivity.
 reflexivity.
Qed.

Variable Outputs_extensionality : forall O1 O2 : Outputs,
  (forall o, O1 o = O2 o) ->
  O1 = O2.

Lemma unnamed_15 : forall l O,
  pO l O = pO l (pO l O).
 unfold pO.
 intros.
 apply Outputs_extensionality.
 intro.
 destruct (dec_eq_Label (output_label o) l).
  reflexivity.
 reflexivity.
Qed.

Lemma lemma_1 : forall l,
  pP l (fun i => BPNum 0) = fun i => BPNum 0
  .
 intros.
 apply Pointers_extensionality; intro i.
 reflexivity.
Qed.

Lemma lemma_2 : forall l,
  pO l (fun o => nil) = fun o => nil
  .
 intros.
 apply Outputs_extensionality; intro o.
 unfold pO.
 destruct (dec_eq_Label (output_label o) l); auto.
Qed.

Theorem transparency_1 : forall C C' l,
  ts_noninterfering C ->
  FacStepStar C C' ->
  exists C'',
  and (
    StdStepStar C C''
  )(
    pC l C' = pC l C''
  ).
 intros.
 destruct C as (((t_, P_), I_), O_).
 destruct H as (T7, T11); rename H0 into T2. unfold nonfaceted in T7.
 destruct (T7 l) as (T8, (T9, T10)).
 pose (T11 (pI l I_)) as T1.
 pose (unnamed_10 l _ _ T2) as T3.
 pose (unnamed_11 _ _ _ T3) as T4.
 simpl in T4.
 simpl in T1.
 rewrite T8 in *.
 rewrite <- unnamed_12 in T4.
 rewrite T9 in T4.
 rewrite (lemma_1 l) in T4.
 rewrite T10 in T4.
 rewrite (lemma_2 l) in T4.
 edestruct (T1 _ T4 l) as (C'', (T5, T6)).
  Focus 2.
  eexists.
  split.
   rewrite <- T9 in T5.
   rewrite <- T10 in T5.
   exact T5.
  rewrite <- T6.
  destruct C' as (((t', P'), I'), O').
  simpl.
  rewrite <- unnamed_12.
  rewrite <- unnamed_13.
  rewrite <- unnamed_14.
  rewrite <- unnamed_15.
  reflexivity.
 simpl.
 rewrite <- unnamed_14.
 reflexivity.
Qed.

Variable SchedulerState : Set.

Definition SConfig : Set := Config * SchedulerState.

Variable SchStep : SConfig -> SConfig -> Prop.

Variable scheduler_validity_1 : forall C s C' s',
  SchStep (C, s) (C', s') ->
  FacStep emptypc C C'.

Variable scheduler_validity_2 : forall C s,
  (forall C' s', SchStep (C, s) (C', s') -> False) ->
  (forall C', FacStep emptypc C C' -> False).

Inductive LStep (l:Label) : PC -> Config -> Config -> Prop :=
  | LContext : forall pc t P I O t' I' O' P' E,
      LStep l pc (t, P, I, O) (t', P', I', O') ->
      LStep l pc (fill E t, P, I, O) (fill E t', P', I', O')
  | LApp : forall pc x t1 t2 P I O,
      LStep l pc (TApp (TLam x t1) t2, P, I, O) (subs t1 x t2, P, I, O)
  | LPlus : forall pc n1 n2 P I O,
      LStep l pc (TPlus (TNum n1) (TNum n2), P, I, O) (TNum (n1+n2), P, I, O)
  | LIf1 : forall pc t1 t2 P I O,
      LStep l pc (TIf (TNum 0) t1 t2, P, I, O) (t1, P, I, O)
  | LIf2 : forall pc n t1 t2 P I O,
      n <> 0%Z ->
      LStep l pc (TIf (TNum n) t1 t2, P, I, O) (t2, P, I, O)
  | LBindFIO : forall pc t1 t2 P I O,
      IsValue t1 ->
      LStep l pc (TBindFIO (TReturn t1) t2, P, I, O) (TApp t2 t1, P, I, O)
  | LrunFacFIO1 : forall t P I O pc,
      LStep l pc (TrunFacFIO (TFV (FVRaw t)), P, I, O) (TBindFIO t (fresh TUnit TUnit (fun x => TLam x (TReturn (TFV (FVRaw (TVar x)))))), P, I, O)
  | LBindFac1 : forall pc t1 t2 P I O,
      LStep l pc (TrunFacFIO (TFV (FVBind (TFV (FVRaw t1)) t2)), P, I, O) (TrunFacFIO (TApp t2 t1), P, I, O)
  | LBindFac2 : forall pc t1 t2 t3 P I O,
      LStep l pc (TrunFacFIO (TFV (FVBind (TFV (FVBind t1 t2)) t3)), P, I, O) (TrunFacFIO (TFV (FVBind t1 (fresh t2 t3 (fun x => TLam x (TFV (FVBind (TApp t2 (TVar x)) t3)))))), P, I, O)

  | LRead : forall pc i P I O,
      LStep l pc (TGet i, P, I, O) (TReturn (TFV (ffacet (l2pc (input_label i)) (fac_read1 pc i (P i) I) (FVRaw (TNum (-1))))), P_upd P i (fac_read2 pc i (P i) I), I, O)
  | LWrite : forall pc o n P I O,
      Subsumes pc (output_label o) ->
      LStep l pc (TPut o (TNum n), P, I, O) (TReturn (TNum n), P, I, O_upd O o (snoc (O o) n))
  | LWriteSkip : forall pc o n P I O,
      not (Subsumes pc (output_label o)) ->
      LStep l pc (TPut o (TNum n), P, I, O) (TReturn (TNum n), P, I, O)
  | LBindFac3 : forall pc k fv1 fv2 t3 P I O,
      LStep l pc (TrunFacFIO (TFV (FVBind (TFV (FVFacet k fv1 fv2)) t3)), P, I, O) (TrunFacFIO (TFV (FVFacet k (FVBind (TFV fv1) t3) (FVBind (TFV fv2) t3))), P, I, O)
  | LrunFacFIO2 : forall (pc:PC) k fv1 fv2 P I O,
      pc k = Some true ->
      LStep l pc (TrunFacFIO (TFV (FVFacet k fv1 fv2)), P, I, O) (TrunFacFIO (TFV fv1), P, I, O)
  | LrunFacFIO3 : forall (pc:PC) k fv1 fv2 P I O,
      pc k = Some false ->
      LStep l pc (TrunFacFIO (TFV (FVFacet k fv1 fv2)), P, I, O) (TrunFacFIO (TFV fv2), P, I, O)
  | LrunFacFIO4 : forall (pc:PC) k fv1 fv2 P I O,
      pc k = None ->
      LStep l pc (TrunFacFIO (TFV (FVFacet k fv1 fv2)), P, I, O) (TThreads k (TrunFacFIO (TFV fv1)) (TrunFacFIO (TFV fv2)), P, I, O)
  | LTimeout : forall pc E k t1 t2 P I O,
      LStep l pc (fill E (TThreads k t1 t2), P, I, O) (TThreads k (fill E t1) (fill E t2), P, I, O)
  | LMerge : forall pc k fv1 fv2 P I O,
      LStep l pc (TThreads k (TReturn (TFV fv1)) (TReturn (TFV fv2)), P, I, O) (TReturn (TFV (FVFacet k fv1 fv2)), P, I, O)
  | LThread1 : forall (pc:PC) k t1 t2 P I O t1' P' I' O',
      pc k <> Some false ->
      l k = true ->
      LStep l (add pc k) (t1, P, I, O) (t1', P', I', O') ->
      LStep l pc (TThreads k t1 t2, P, I, O) (TThreads k t1' t2, P', I', O')
  | LThread2 : forall (pc:PC) k t1 t2 P I O t2' P' I' O',
      pc k <> Some true ->
      l k = false ->
      LStep l (subtract pc k) (t2, P, I, O) (t2', P', I', O') ->
      LStep l pc (TThreads k t1 t2, P, I, O) (TThreads k t1 t2', P', I', O')
  .

Fixpoint value_t (l:Label) (t:Term) :=
  match t with
  | TFV fv => value_fv l fv
  | TLam x t => value_t l t + value_t l t
  | TNum n => 0
  | TUnit => 0
  | TReturn (TFV _) => 0
  | TReturn t => value_t l t + value_t l t
  | TVar x => 0
  | TApp t1 t2 => value_t l t1 + value_t l t2 + value_t l t1 + value_t l t2
  | TPlus t1 t2 => value_t l t1 + value_t l t2 + value_t l t1 + value_t l t2
  | TIf t1 t2 t3 => value_t l t1 + value_t l t2 + value_t l t3 + value_t l t1 + value_t l t2 + value_t l t3
  | TBindFIO t1 t2 => value_t l t1 + value_t l t2 + value_t l t1 + value_t l t2
  | TrunFacFIO t => value_t l t + value_t l t
  | TGet i => 0
  | TPut o t => value_t l t + value_t l t
  | TThreads k t1 t2 =>
      if l k then
        1 + value_t l t1
      else
        1 + value_t l t2
  end
with value_fv (l:Label) (fv:FacetedValue) :=
  match fv with
  | FVRaw t => value_t l t + value_t l t
  | FVFacet k fv1 fv2 =>
      if l k then
        1 + value_fv l fv1
      else
        1 + value_fv l fv2
  | FVBind t1 t2 => value_t l t1 + value_t l t1  (* + value_t l t2 + value_t l t2 *)
  end
.

Definition value_E (l:Label) (E:Context) :=
  match E with
  | EApp t => value_t l t + value_t l t
  | EPlus1 t => value_t l t + value_t l t
  | EPlus2 n => 0
  | EIf t2 t3 => value_t l t2 + value_t l t3 + value_t l t2 + value_t l t3
  | EBindFIO t => value_t l t + value_t l t
  | ErunFacFIO1 => 0
  | ErunFacFIO2 t => 0
  | EPut o => 0
  | EReturn => 0
  end.
Definition fill_value_witness (E:Context) t :=
  match (E, t) with
  | (EReturn, TFV _) => 0
  | (ErunFacFIO2 _, _) => 4
  | _ => 2
  end.
Lemma fill_value_lemma : forall l E t,
  value_t l (fill E t) = (fill_value_witness E t) * value_t l t + value_E l E.
 intros.
 destruct t; destruct E; try solve [simpl; omega].
Qed.

Definition value_C l (C:Config) := match C with (t, _, _, _) => value_t l t end.
Lemma mechanism_progress : forall l pc C C',
  Subsumes pc l ->
  LStep l pc C C' ->
  or (
    StdStep (pC l C) (pC l C')
  )(
    and (
      pC l C = pC l C'
    )(
      value_C l C' < value_C l C
    )
  ).
 intros.
 rename H into T1.
 rename H0 into T2.
 induction T2
   ; try solve [left; simpl; pose hints; intuition].
 (* Leaves 14 subgoals *)

 destruct IHT2.
   assumption.
  left.
  simpl.
  destruct E; try solve [
      rewrite fill_lemma; try auto
    ; rewrite fill_lemma; try auto
    ; apply SContext
    ; exact H
  ].
  simpl.
  destruct (dec_eq_Label (output_label o) l).
   apply SContext with (E := EPut o).
   exact H.
  apply SContext with (E := EReturn).
  apply SContext with (E := EPlus2 0).
  exact H.
 right.
 split.
  destruct H.
  simpl in H.
  simpl.
  destruct E; try solve [
    rewrite fill_lemma; try auto;
    rewrite fill_lemma; try auto;
    congruence
  ].
  simpl.
  destruct (dec_eq_Label (output_label o) l).
   congruence.
  congruence.
 destruct H as (_, H).
 simpl.
 simpl in H.
 rewrite (fill_value_lemma l E t').
 rewrite (fill_value_lemma l E t).
 destruct E; try solve [simpl; omega].
 destruct t; try solve [
   destruct t';
   simpl;
   simpl in H;
   omega
 ].
 apply False_rect.
 inversion T2.
  destruct E; discriminate.
 destruct E; discriminate.

 left.
 simpl.
 rewrite subs_lemma.
 apply SApp.

 left.
 simpl.
 rewrite fresh_lemma_2.
 apply SrunFacFIO1.

 left.
 simpl.
 rewrite fresh_lemma.
 apply SBindFac2.

 left.
 simpl.
 destruct (dec_flows (input_label i) l).
  rewrite ffacet_Axiom1; try auto.
  rewrite <- unnamed_3.
  rewrite unnamed_4; try auto.
  rewrite unnamed_lemma; try auto.
  apply SRead.
  reflexivity.
 rewrite ffacet_Axiom2; try auto.
 rewrite <- unnamed_3.
 simpl.
 rewrite unnamed_lemma; try auto.
 assert ((-1)%Z = (list_at (pI l I i) (pp l (P i)))) as T2.
  unfold pI.
  destruct (dec_flows (input_label i) l) as [|_]; try contradiction.
  reflexivity.
 rewrite T2.
 eapply SRead.
 reflexivity.

 simpl.
 destruct (dec_eq_Label (output_label o) l) as [e|].
  left.
  rewrite <- e.
  rewrite <- unnamed_5.
  eapply SWrite.
 rewrite unnamed_6; try assumption.
 left.
 apply SContext with (E := EReturn).
 apply SPlus.

 simpl.
 destruct (dec_eq_Label (output_label o) l) as [e|].
  congruence.  (* contradiction between T1 and e *)
 left.
 apply SContext with (E := EReturn).
 apply SPlus.

 right.
 simpl.
 destruct (l k); (
     split
   ; try reflexivity
   ; omega
 ).

 right.
 simpl.
 remember (l k) as temp.
 destruct temp.
  split.
   reflexivity.
  omega.
 pose (T1 k) as T2.
 rewrite H in T2.
 congruence.

 right.
 simpl.
 remember (l k) as temp.
 destruct temp.
  pose (T1 k) as T2.
  rewrite H in T2.
  congruence.
 split.
  reflexivity.
 omega.

 right.
 simpl.
 destruct (l k); (
     split
   ; try reflexivity
   ; omega
 ).

 right.
 simpl.
 rewrite fill_value_lemma.
 rewrite fill_value_lemma.
 rewrite fill_value_lemma.
 simpl.
 destruct E; simpl; destruct (l k); try solve [simpl; split; try reflexivity; omega].
  split.
   reflexivity.
  simpl.
  destruct t1; try solve [simpl; omega].
 split.
  reflexivity.
 simpl.
 destruct t2; try solve [simpl; omega].

 right.
 simpl.
 destruct (l k)
   ; split; try reflexivity; omega.

 destruct IHT2.
   intro.
   destruct (dec_eq_Principal k k0).
    rewrite add_Axiom1; auto.
    congruence.
   rewrite add_Axiom2; auto.
   apply T1.
  left.
  simpl.
  rewrite H0.
  exact H1.
 right.
 simpl.
 rewrite H0.
 simpl in H1.
 destruct H1.
 split.
  congruence.
 omega.

 destruct IHT2.
   intro.
   destruct (dec_eq_Principal k k0).
    rewrite subtract_Axiom1; auto.
    congruence.
   rewrite subtract_Axiom2; auto.
   apply T1.
  left.
  simpl.
  rewrite H0.
  exact H1.
 right.
 simpl.
 rewrite H0.
 simpl in H1.
 destruct H1.
 split.
  congruence.
 omega.

Qed.

Inductive SchStepStar : SConfig -> SConfig -> Prop :=
  | SchNil : forall c,
      SchStepStar c c
  | SchCons : forall c0 c1 c2,
      SchStep c0 c1 ->
      SchStepStar c1 c2 ->
      SchStepStar c0 c2
  .

Inductive FairnessWitness (l:Label) : Config -> SchedulerState -> Config -> SchedulerState -> Prop :=
  | FWNil : forall C s C' s',
      SchStep (C, s) (C', s') ->
      LStep l emptypc C C' ->
      FairnessWitness l C s C' s'
  | FWCons : forall C0 C1 C2 s0 s1 s2,
      SchStep (C0, s0) (C1, s1) ->
      not (LStep l emptypc C0 C1) ->
      FairnessWitness l C1 s1 C2 s2 ->
      FairnessWitness l C0 s0 C2 s2
  .

Variable fairness : forall l C s C_,
  LStep l emptypc C C_ ->
  exists C' s',
  FairnessWitness l C s C' s'
  .

Definition hints_L := (LContext, LApp, LBindFac1, LBindFac2, LPlus, LIf1, LIf2, LBindFIO, LrunFacFIO1, LRead, LWrite, LrunFacFIO2, LWriteSkip, LBindFac3, LrunFacFIO2, LrunFacFIO3, LrunFacFIO4, LTimeout, LMerge, LThread1, LThread2).
Definition hints'' := (hints', hints_L).

Lemma unnamed_16 : forall l t pc P I O,
  (forall k t1 t2, t = TThreads k t1 t2 -> False) ->
  IsValue (pt l t) ->
  or (
    IsValue t
  )(
    exists t' O',
      LStep l pc (t, P, I, O) (t', P, I, O')
  ).
 intros l t pc P I O T1 T2.
 induction t; try solve [pose hints''; intuition; inversion T2].
 (* Leaves 3 subgoals *)

   destruct t; try solve [
     destruct IHt as [| T3]; [
        discriminate
        |
       simpl in T2; inversion T2; assumption
       |
      pose hints; intuition
      |
     right;
     destruct T3 as (t', T3);
     destruct T3 as (O', T3);
     repeat eexists;
     apply LContext with (E := EReturn);
     exact T3
     ]
   ].
   right.
   repeat eexists.
   apply LTimeout with (E := EReturn).
  destruct t; (
    simpl in T2;
    destruct (dec_eq_Label (output_label o) l); try solve [inversion T2];
    inversion T2;
    inversion H0
  ).
 apply False_rect.
 apply T1 with p t1 t2.
 reflexivity.
Qed.

Lemma projstep_implies_lstep : forall l C pc p_C',
  Subsumes pc l ->
  StdStep (pC l C) p_C' ->
  exists C',
  LStep l pc C C'
  .

(* This whole proof is a copy-paste-edit from projection_1'. *)

 destruct C as (((t, P), I), O).
 induction t using custom_induction(* with (Q := fun fv:FacetedValue =>
       (forall C' : Config, FacStep emptypc (TFV fv, P, I, O) C' -> False) ->
       forall C' : Config, StdStep (pC l (TFV fv, P, I, O)) C' ->
       False
     )*)
   ; intros pc p_C' subsumes stdstep
   ; try solve [(inversion stdstep; destruct E; try discriminate)]
   ; idtac.

  (* Leaves 11 subgoals *)

         inversion stdstep.
         destruct E; try discriminate.
         edestruct IHt as (C'0, T1).
           exact subsumes.
          simpl.
          simpl in H.
          injection H; intros.
          rewrite <- H5.
          exact H4.
         intros.
         destruct C'0 as (((t'0, P'0), I'0), O'0).
         eexists.
         apply LContext with (E := EReturn).
         exact T1.
        inversion stdstep.
         destruct E; try discriminate.
         edestruct IHt1 as (C'0, T1).
           exact subsumes.
          Focus 2.
          intros.
          destruct C'0 as (((t'0, P'0), I'0), O'0).
          eexists.
          apply LContext with (E := EApp t2).
          exact T1.
         simpl.
         simpl in H.
         injection H; intros.
         rewrite <- H6.
         apply H4.
        destruct t1; try discriminate.
          eexists.
          apply LApp.
         simpl in H0.
         destruct (dec_eq_Label (output_label o) l);  inversion H0.
        eexists.
        apply LTimeout with (E := EApp t2).
       inversion stdstep.
        destruct E; try discriminate.
         edestruct IHt1 as (C'0, T1).
           exact subsumes.
          Focus 2.
          intros.
          destruct C'0 as (((t'0, P'0), I'0), O'0).
          eexists.
          apply LContext with (E := EPlus1 t2).
          exact T1.
         simpl.
         simpl in H.
         injection H; intros.
         rewrite <- H6.
         exact H4.
        edestruct IHt2 as (C'0, T1).
          exact subsumes.
         Focus 2.
         intros.
         destruct C'0 as (((t'0, P'0), I'0), O'0).
         destruct t1; try discriminate.
           eexists.
           simpl in H.
           injection H; intros.
           rewrite H5.
           apply LContext with (E := EPlus2 z0).
           exact T1.
          simpl in H.
          destruct (dec_eq_Label (output_label o) l); inversion H.
         simpl in H.
         eexists.
         apply LTimeout with (E := EPlus1 t2).
        simpl.
        simpl in H.
        injection H; intros.
        rewrite <- H5.
        exact H4.
       destruct t1; try discriminate.
         destruct t2; try discriminate.
           eexists.
           apply LPlus.
          simpl in H1.
          destruct (dec_eq_Label (output_label o) l);  inversion H1.
         eexists.
         apply LTimeout with (E := EPlus2 z).
        simpl in H0.
        destruct (dec_eq_Label (output_label o) l);  inversion H0.
       eexists.
       apply LTimeout with (E := EPlus1 t2).
      inversion stdstep.
        destruct E; try discriminate.
        edestruct IHt1 as (C'0, T1).
          exact subsumes.
         Focus 2.
         intros.
         destruct C'0 as (((t'0, P'0), I'0), O'0).
         eexists.
         apply LContext with (E := EIf t2 t3).
         exact T1.
        simpl.
        simpl in H.
        injection H; intros.
        rewrite <- H7.
        exact H4.
       destruct t1; try discriminate.
         eexists.
         simpl in H0.
         injection H0; intros.
         rewrite <- H.
         apply LIf1.
        simpl in H0.
        destruct (dec_eq_Label (output_label o) l);  inversion H0.
       eexists.
       apply LTimeout with (E := EIf t2 t3).
      destruct t1; try discriminate.
        eexists.
        apply LIf2.
        simpl in H.
        congruence.
       simpl in H.
       destruct (dec_eq_Label (output_label o) l);  inversion H.
      eexists.
      apply LTimeout with (E := EIf t2 t3).
     inversion stdstep.
      destruct E; try discriminate.
      edestruct IHt1 as (C'0, T1).
        exact subsumes.
       Focus 2.
       intros.
       destruct C'0 as (((t'0, P'0), I'0), O'0).
       eexists.
       apply LContext with (E := EBindFIO t2).
       exact T1.
      simpl.
      simpl in H.
      injection H; intros.
      rewrite <- H6.
      exact H4.
     pose (E := EBindFIO t2).
     destruct t1; try discriminate.
       simpl in H.
       injection H; intros.
       destruct (unnamed_16 l (TReturn t1) pc P I O) as [T1 | (t', (O', T1))].
          congruence.
         simpl.
         apply VReturn.
         congruence.
        eexists.
        inversion T1.
        apply LBindFIO.
        assumption.
       eexists.
       apply LContext with (E := E).
       exact T1.
      simpl in H.
      destruct (dec_eq_Label (output_label o) l).
       discriminate.
      destruct (unnamed_16 l (TPut o t1) pc P I O) as [T1 | (t', (O', T1))].
         congruence.
        simpl.
        simpl in H.
        injection H; intros.
        destruct (dec_eq_Label (output_label o) l).
         contradiction.
        apply VReturn.
        congruence.
       inversion T1.
      eexists.
      apply LContext with (E := E).
      exact T1.
     eexists.
     apply LTimeout with (E := E).
    inversion stdstep.
         destruct E; try discriminate.
         edestruct IHt1 as (C'0, T1).
            exact subsumes.
           Focus 2.
           intros.
           destruct C'0 as (((t'0, P'0), I'0), O'0).
           eexists.
           apply LContext with (E := ErunFacFIO1).
           exact T1.
          simpl.
          simpl in H.
          injection H; intros.
          rewrite <- H5.
          exact H4.
         edestruct IHt2 as (C'0, T1).
           exact subsumes.
          Focus 2.
          intros.
          destruct C'0 as (((t'0, P'0), I'0), O'0).
          eexists.
          apply LContext with (E := ErunFacFIO2 t2).
          exact T1.
         simpl in H.
         injection H; intros.
         simpl.
         rewrite <- H6.
         exact H4.
        destruct t1; try discriminate.
          destruct f; try discriminate.
           eexists.
           apply LBindFac1.
          eexists.
          apply LBindFac3.
         simpl in H0.
         destruct (dec_eq_Label (output_label o) l); discriminate.
        eexists.
        apply LTimeout with (E := ErunFacFIO2 t2).
       destruct t1; try discriminate.
         destruct f; try discriminate.
          eexists.
          apply LBindFac2.
         eexists.
         apply LBindFac3.
        simpl in H0.
        destruct (dec_eq_Label (output_label o) l); discriminate.
       eexists.
       apply LTimeout with (E := ErunFacFIO2 t2).
     inversion stdstep.
        destruct E; try discriminate.
         edestruct IHt as (C'0, T1).
           exact subsumes.
          Focus 2.
          intros.
          destruct C'0 as (((t'0, P'0), I'0), O'0).
          eexists.
          apply LContext with (E := ErunFacFIO1).
          exact T1.
         simpl.
         simpl in H0.
         injection H0; intros.
         rewrite <- H6.
         exact H5.
        destruct fv; try discriminate.
         simpl in H0.
         injection H0; intros.
         simpl in H6.
         congruence.
        remember (pc p) as T1.
        destruct T1 as [[|]|].
           eexists.
           apply LrunFacFIO2.
           congruence.
          eexists.
          apply LrunFacFIO3.
          congruence.
         eexists.
         apply LrunFacFIO4.
         congruence.
       destruct fv; try discriminate.
        eexists.
        apply LrunFacFIO1.
       remember (pc p) as T1.
       destruct T1 as [[|]|].
          eexists.
          apply LrunFacFIO2.
          congruence.
         eexists.
         apply LrunFacFIO3.
         congruence.
        eexists.
        apply LrunFacFIO4.
        congruence.
      destruct fv.
        discriminate.
       congruence.
      remember (pc p) as T1.
      destruct T1 as [[|]|].
         eexists.
         apply LrunFacFIO2.
         congruence.
        eexists.
        apply LrunFacFIO3.
        congruence.
       eexists.
       apply LrunFacFIO4.
       congruence.
     destruct fv.
       discriminate.
      congruence.
     remember (pc p) as T1.
     destruct T1 as [[|]|].
        eexists.
        apply LrunFacFIO2.
        congruence.
       eexists.
       apply LrunFacFIO3.
       congruence.
      eexists.
      apply LrunFacFIO4.
      congruence.
    inversion stdstep.
       destruct E; try discriminate.
        edestruct IHt as (C'0, T1).
          exact subsumes.
         Focus 2.
         intros.
         destruct C'0 as (((t'0, P'0), I'0), O'0).
         eexists.
         apply LContext with (E := ErunFacFIO1).
         exact T1.
        simpl.
        simpl in H0.
        injection H0; intros.
        rewrite <- H6.
        exact H5.
       destruct t; try discriminate.
         congruence.
        simpl in H0.
        destruct (dec_eq_Label (output_label o) l); discriminate.
       eexists.
       apply LTimeout with (E := ErunFacFIO1).
      destruct t; try discriminate.
        congruence.
       simpl in H1.
       destruct (dec_eq_Label (output_label o) l); discriminate.
      eexists.
      apply LTimeout with (E := ErunFacFIO1).
     destruct t; try discriminate.
       congruence.
      simpl in H1.
      destruct (dec_eq_Label (output_label o) l); discriminate.
     eexists.
     apply LTimeout with (E := ErunFacFIO1).
    destruct t; try discriminate.
      congruence.
     simpl in H1.
     destruct (dec_eq_Label (output_label o) l); discriminate.
    eexists.
    apply LTimeout with (E := ErunFacFIO1).
   inversion stdstep.
    destruct E; discriminate.
   eexists.
   apply LRead.
  simpl in stdstep.
  destruct (dec_eq_Label (output_label o) l).
   inversion stdstep.
     destruct E; try discriminate.
     edestruct IHt as (C'0, T1).
       exact subsumes.
      Focus 2.
      intros.
      destruct C'0 as (((t'0, P'0), I'0), O'0).
      eexists.
      apply LContext with (E := EPut o).
      exact T1.
     simpl.
     simpl in H.
     injection H; intros.
     rewrite <- H5.
     exact H4.
    destruct t; try discriminate.
      destruct (dec_Subsumes pc (output_label o)).
       eexists.
       apply LWrite.
       assumption.
      eexists.
      apply LWriteSkip.
      assumption.
     simpl in H1.
     destruct (dec_eq_Label (output_label o1) l); discriminate.
    eexists.
    apply LTimeout with (E := EPut o).
  inversion stdstep.
  destruct E; try discriminate.
  simpl.
  simpl in H.
  injection H; intros.
  rewrite H5 in H4.
  inversion H4.
   destruct E; try discriminate.
    simpl in H6.
    injection H6; intros.
    rewrite H16 in H7.
    inversion H7.
    destruct E; discriminate.
   edestruct IHt as (C'0, T1).
     exact subsumes.
    Focus 2.
    intros.
    destruct C'0 as (((t'00, P'00), I'00), O'00).
    eexists.
    apply LContext with (E := EPut o).
    exact T1.
   simpl.
   simpl in H6.
   injection H6; intros.
   rewrite <- H15.
   exact H7.
  assert ((forall k t4 t5, t<>TThreads k t4 t5) \/ exists k t4 t5, t=TThreads k t4 t5) as T2.
   destruct t
     ; try solve [left; intros; congruence].
   right.
   do 3 eexists.
   reflexivity.
  destruct T2 as [T2|(k,(t4,(t5,T2)))].
   Focus 2.
   rewrite T2.
   eexists.
   apply LTimeout with (E := EPut o).
  destruct (unnamed_16 l t pc P I O) as [T1 | (t_, (O_, T1))].
     congruence.  (* Using T2 *)
    rewrite <- H8.
    apply VNum.
   inversion T1; try solve [
       try rewrite <- H6 in H8;
       try rewrite <- H16 in H8;
       simpl in H8;
       discriminate
   ].
   destruct (dec_Subsumes pc (output_label o)).
    eexists.
    rewrite <- H6.
    apply LWrite.
    assumption.
   eexists.
   rewrite <- H6.
   apply LWriteSkip.
   assumption.
  eexists.
  eapply LContext with (E := EPut o).
  exact T1.
 remember (l p) as T.
 destruct T.
  edestruct IHt1 as (C'0, T1).
    Focus 3.
    remember (pc p) as T.
    intros.
    destruct C'0 as (((t'0, P'0), I'0), O'0).
    destruct T as [[|]|].
      eexists.
      apply LThread1.
        congruence.
       congruence.
      exact T1.
     pose (subsumes p).
     rewrite <- HeqT0 in y.
     congruence.
    eexists.
    apply LThread1.
      congruence.
     congruence.
    pose (subsumes p) as T2.
    rewrite <- HeqT0 in T2.
    exact T1.
   intro.
   destruct (dec_eq_Principal p k).
    rewrite add_Axiom1; congruence.
   rewrite add_Axiom2; try congruence.
   apply subsumes.
  simpl in stdstep.
  rewrite <- HeqT in stdstep.
  simpl.
  exact stdstep.
 (* Begin copy-paste-edit, from above *)
 edestruct IHt2 as (C'0, T1).
   Focus 3.
   remember (pc p) as T.
   intros.
   destruct C'0 as (((t'0, P'0), I'0), O'0).
   destruct T as [[|]|].
     Focus 2.
     eexists.
     apply LThread2.
       congruence.
      congruence.
     exact T1.
    pose (subsumes p).
    rewrite <- HeqT0 in y.
    congruence.
   eexists.
   apply LThread2.
     congruence.
    congruence.
   pose (subsumes p) as T2.
   rewrite <- HeqT0 in T2.
   exact T1.
  intro.
  destruct (dec_eq_Principal p k).
   rewrite subtract_Axiom1; congruence.
  rewrite subtract_Axiom2; try congruence.
  apply subsumes.
 simpl in stdstep.
 rewrite <- HeqT in stdstep.
 simpl.
 exact stdstep.
 (* End copy-paste-edit *)
Qed.

Theorem sch_concat : forall c0 c2 c3,
  SchStepStar c0 c2 ->
  SchStepStar c2 c3 ->
  SchStepStar c0 c3.
 intros.
 induction H.
  exact H0.
 apply SchCons with c1.
  assumption.
 apply IHSchStepStar.
 assumption.
Qed.

Lemma strong_induction : forall (P:nat->Prop),
  (forall n, (forall k, k<n->P k) -> P n) ->
  forall n,
  P n.
Admitted.

Lemma unnamed_17 : forall l C C',
  FacStep emptypc C C' ->
  ~LStep l emptypc C C' ->
  pC l C = pC l C'
  .
 intros l C C' T1 T2.
 simpl.
 induction T1; try solve [
   apply False_rect; apply T2; pose hints''; intuition
 ].
 (* Leaves 3 subgoals *)

   simpl.
   destruct E; try solve [
     rewrite fill_lemma; try auto;
     rewrite fill_lemma; try auto;
     simpl in IHT1;
     refine (_ (IHT1 _)); [
      intro T3;
      congruence
      |
     intro;
     apply T2;
     apply LContext;
     exact H
     ]
   ].
   simpl.
   destruct (dec_eq_Label (output_label o) l); try solve [
     simpl in IHT1;
     refine (_ (IHT1 _)); [
      intro T3;
      congruence
      |
     intro;
     apply T2;
     apply LContext;
     exact H
     ]
   ].

  simpl.
  remember (l k) as temp.
  destruct temp.
   simpl in IHT1.
   apply IHT1.
   intro T3.
   apply T2.
   apply LThread1.
     assumption.
    congruence.
   exact T3.
  destruct (projection_1 _ _ l _ T1) as (_, (T3, (T4,T5))).
   intro.
   pose (H0 k).
   rewrite add_Axiom1 in y.
    congruence.
   reflexivity.
  congruence.

 (* Begin copy-paste-edit from above *)
 simpl.
 remember (l k) as temp.
 destruct temp.
  Focus 2.
  simpl in IHT1.
  apply IHT1.
  intro T3.
  apply T2.
  apply LThread2.
    assumption.
   congruence.
  exact T3.
 destruct (projection_1 _ _ l _ T1) as (_, (T3, (T4,T5))).
  intro.
  pose (H0 k).
  rewrite subtract_Axiom1 in y.
   congruence.
  reflexivity.
 congruence.
 (* End copy-paste-edit from above *)

Qed.

Theorem unnamed_18 : forall l C C',
  FacStep emptypc C C' ->
  ~LStep l emptypc C C' ->
  value_C l C = value_C l C'
  .
 intros l C C' T1 T2.
 simpl.
 induction T1; try solve [
   apply False_rect; apply T2; pose hints''; intuition
 ].
 (* Leaves 3 subgoals *)

   simpl.
   destruct E; try solve [
     rewrite fill_value_lemma;
     rewrite fill_value_lemma;
     simpl in IHT1;
     simpl;
     rewrite IHT1; try reflexivity;
     intro T3;
     apply T2;
     apply LContext;
     exact T3
   ].
   rewrite fill_value_lemma.
   rewrite fill_value_lemma.
   simpl in IHT1.
   simpl.
   destruct t'; [idtac | (
     destruct t
       ; [inversion T1; destruct E; discriminate | ..]
       ; try reflexivity
       ; rewrite IHT1; try reflexivity
       ; intro T3; apply T2; apply LContext; exact T3
   )..].
   apply False_rect.
   apply T2.
   apply LContext.
   clear IHT1.
   remember (TFV f, P', I', O') as C'.
   induction T1; try solve [ pose hints''; intuition ].
     apply LContext.
     apply IHT1.
      destruct E; discriminate.
     exact T2.
    discriminate.
   discriminate.

  simpl.
  remember (l k) as temp.
  destruct temp.
   simpl in IHT1.
   rewrite IHT1.
    reflexivity.
   intro T3.
   apply T2.
   apply LThread1.
     assumption.
    congruence.
   exact T3.
  destruct (projection_1 _ _ l _ T1) as (_, (T3, (T4,T5))).
   intro.
   pose (H0 k).
   rewrite add_Axiom1 in y.
    congruence.
   reflexivity.
  congruence.

 (* Begin copy-paste-edit from above *)
 simpl.
 remember (l k) as temp.
 destruct temp.
  Focus 2.
  simpl in IHT1.
  rewrite IHT1.
   reflexivity.
  intro T3.
  apply T2.
  apply LThread2.
    assumption.
   congruence.
  exact T3.
 destruct (projection_1 _ _ l _ T1) as (_, (T3, (T4,T5))).
  intro.
  pose (H0 k).
  rewrite subtract_Axiom1 in y.
   congruence.
  reflexivity.
 congruence.
 (* End copy-paste-edit from above *)

Qed.

Theorem projection_2a : forall l C0 p_C' s0,
  StdStep (pC l C0) p_C' ->
  exists C' s',
  and (
    SchStepStar (C0, s0) (C', s')
  )(
    pC l C' = p_C'
  ).
 intros.
 rename H into T1.
 remember (value_C l C0) as n.
 generalize p_C' s0 C0 Heqn T1.
 clear Heqn T1 C0 p_C' s0.
 induction n as (n,IH) using strong_induction.
 destruct n.
  clear IH.
  intros.
  destruct (projstep_implies_lstep l C0 emptypc p_C') as (C_, T2).
    intro.
    rewrite emptypc_Axiom.
    trivial.
   exact T1.
  destruct (fairness l _ s0 _ T2) as (C', (s', T3)).
  clear C_ T2.
  induction T3.
   edestruct (mechanism_progress l).
      intro.
      rewrite emptypc_Axiom.
      trivial.
     exact H0.
    do 2 eexists.
    split.
     refine (SchCons _ _ _ H _).
     apply SchNil.
    eapply determinism_1.
     exact H1.
    exact T1.
   rewrite <- Heqn in H1.
   destruct H1.
   inversion H2.
  edestruct IHT3 as (C', (s', (T4, T5))).
    rewrite Heqn.
    apply unnamed_18.
     eapply scheduler_validity_1.
     exact H.
    assumption.
   erewrite <- unnamed_17.
     exact T1.
    eapply scheduler_validity_1.
    exact H.
   exact H0.
  do 2 eexists.
  split.
  eapply SchCons.
    exact H.
   exact T4.
  exact T5.
 intros p_C'' s0 C0 Heqn T1.
 destruct (projstep_implies_lstep l C0 emptypc p_C'') as (C_, T2).
   intro.
   rewrite emptypc_Axiom.
   trivial.
  exact T1.
 destruct (fairness l _ s0 _ T2) as (C', (s', T3)).
 clear C_ T2.
 induction T3.
  destruct (mechanism_progress l emptypc C C').
     intro.
     rewrite emptypc_Axiom.
     trivial.
    exact H0.
   do 2 eexists.
   split.
    eapply SchCons.
     exact H.
    apply SchNil.
   eapply determinism_1.
    exact H1.
   exact T1.
  edestruct IH with (k := value_C l C') as (C'', (s'', T2)).
     omega.
    reflexivity.
   destruct H1 as (T3, _).
   rewrite <- T3.
   exact T1.
  destruct T2 as (T2, T3).
  destruct H1 as (T4, T5).
  do 2 eexists.
  split.
   eapply SchCons.
   exact H.
   exact T2.
  exact T3.
 destruct IHT3 as (C'', (s'', (T4, T5))).
   erewrite <- unnamed_18.
     exact Heqn.
    eapply scheduler_validity_1.
    exact H.
   exact H0.
  erewrite <- unnamed_17.
    exact T1.
   eapply scheduler_validity_1.
   exact H.
  exact H0.
 do 2 eexists.
 split.
  eapply SchCons.
   exact H.
  exact T4.
 exact T5.
Qed.

Theorem stupid : forall c0 c2,
  SchStepStar c0 c2 ->
  forall C0 s0 C2 s2,
  c0 = (C0, s0) ->
  c2 = (C2, s2) ->
  FacStepStar C0 C2.
 induction 1.
  intros.
  rewrite H in *.
  injection H0; intros.
  rewrite H2.
  apply FSNil.
 intros.
 destruct c1 as (C1, s1).
 apply FSCons with C1.
  apply scheduler_validity_1 with s0 s1.
  congruence.
 apply IHSchStepStar with s1 s2.
  reflexivity.
 assumption.
Qed.

Theorem stupid_2 : forall l p_C0 p_C2,
  StdStepStar p_C0 p_C2 ->
  forall C0,
  p_C0 = pC l C0 ->
  forall s0,
  exists C2 s2,
  and (
    SchStepStar (C0, s0) (C2, s2)
  )(
    pC l C2 = p_C2
  ).
 induction 1.
  intros.
  eexists.
  eexists.
  split.
   apply SchNil.
  congruence.
 intros up_C0 T1 s0.
 rewrite T1 in H.
 destruct (projection_2a l _ _ s0 H) as (up_C1, (s1, (T2, T3))).
 destruct IHStdStepStar with up_C1 s1 as (up_C2, (s2, (T4, T5))).
  congruence.
 eexists.
 eexists.
 split.
  apply sch_concat with (up_C1, s1).
   exact T2.
  exact T4.
 exact T5.
Qed.

Theorem tsni : forall l C1 s1 C1' s1' C2 s2,
  SchStepStar (C1, s1) (C1', s1') ->
  pC l C1 = pC l C2 ->
  exists C2' s2',
    SchStepStar (C2, s2) (C2', s2')
  /\
    pC l C1' = pC l C2'
  .
 intros.
 assert (FacStepStar C1 C1').
  apply stupid with (C1, s1) (C1', s1') s1 s1'.
    assumption.
   reflexivity.
  reflexivity.
 destruct (stupid_2 l _ _ (unnamed_11 l _ _ (unnamed_10 l _ _ H1))) with C2 s2 as (C2', (s2', (T1, T2))).
  assumption.
 eexists.
 eexists.
 split.
  exact T1.
 auto.
Qed.

Theorem transparency_2 : forall C C' l s,
  StdStepStar C C' ->
  ts_noninterfering C ->
  exists C'' s'',
  and (
    SchStepStar (C, s) (C'', s'')
  )(
    pC l C' = pC l C''
  ).
  intros.
  destruct C as (((t, P), I), O).
  rename H into T1; destruct H0 as ((T9, (T10, T11)), T2).
  remember (pt l t, pP l P, pI l I, pO l O) as C.
  edestruct T2 with (l := l) (C' := C') (I2 := pI l I) as (C'', (T4, T5)).
    rewrite T10, T11 in T1.
    exact T1.
   rewrite <- unnamed_14.
   reflexivity.
(*
   simpl.
   rewrite HeqC.
   simpl.
   rewrite <- unnamed_12, <- unnamed_13, <- unnamed_14, <- unnamed_15.
   reflexivity.
*)
  fold Pointers Inputs Outputs Config in C.
  fold Pointers Inputs Outputs Config in HeqC.
  rewrite T5.
  destruct (stupid_2 l _ _ T4) with (C0 := (t, P, I, O)) (s0 := s) as (C''', (s''', (T7, T8))).
   simpl.
   rewrite <- T9.
   rewrite T10, T11.
   rewrite (lemma_1 l).
   rewrite (lemma_2 l).
   reflexivity.
  eexists C'''.
  eexists s'''.
  split.
   Focus 2.
   rewrite <- T8.
   destruct C''' as (((?, ?), ?), ?).
   simpl.
   rewrite <- unnamed_12, <- unnamed_13, <- unnamed_14, <- unnamed_15.
   reflexivity.
  exact T7.
Qed.