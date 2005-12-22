(*Fixpoint sum_sort (t : term) : term :=
  match t with
  | Sum U V => sum_sort V
  | _ => t
  end.

Definition sum_dec : forall t, {exists U, exists V, t = Sum U V} + {forall U V, t <> Sum U V}.
Proof.
intros.
induction t ; try solve [right ; intros ; red ; intros ; discriminate].
left.
exists t1 ; exists t2 ; reflexivity.
Qed.

Lemma sum_sort_not_kind : forall t G T, G |- t : T -> 
  forall U V, t = Sum U V -> ~ (sum_sort t = Srt kind).
Proof.
induction t ; try solve [unfold sum_sort ; red ; intros ; try discriminate].
intros.
induction (sum_dec V).
induction a.
induction H1.
red ; intros.
rewrite H0 in H2.
simpl in H2.
injection H0.
intros.
rewrite H3 in IHt2.

induction H ; try discriminate.
injection H0.
intros.
rewrite H6 in H5.
apply (IHt2 _ _ H5 _ _ H1).
apply H2.

apply (IHtyp1 H0).

injection H0 ; intros.
rewrite H1 in IHt2.
induction H ; try discriminate.
injection H0 ; intros.
rewrite H4 in H3.

red ; intros.

simpl in H6.
rewrite H4 in H6.
induction V ; try solve [unfold sum_sort in H6 ; try discriminate].
pose (typ_not_kind H3).
contradiction.
apply (b V1 V2) ; auto.

apply IHtyp1 ; auto.
Qed.

Fixpoint subset_sort (t : term) : term :=
  match t with
  | Subset U V => subset_sort U
  | _ => t
  end.

Definition subset_dec : forall t, {exists U, exists V, t = Subset U V} + {forall U V, t <> Subset U V}.
Proof.
intros.
induction t ; try solve [right ; intros ; red ; intros ; discriminate].
left.
exists t1 ; exists t2 ; reflexivity.
Qed.

Lemma subset_sort_set : forall t G T, G |- t : T -> 
  forall U V, t = Subset U V -> forall s, subset_sort t <> Srt s.
Proof.
induction t ; try solve [unfold subset_sort ; try red ; intros ; try discriminate].

intros.
induction (subset_dec U).
induction a.
induction H1.
simpl.

injection H0 ; intros.
rewrite H3 in IHt1.
induction H ; try discriminate.
injection H0 ; intros.
rewrite H6 in H.
rewrite H3.
apply (IHt1 _ _ H _ _ H1).

apply (IHtyp1 H0).

simpl.
red ; intros.
injection H0 ; intros.
induction H ; try discriminate.
injection H0 ; intros.
rewrite H3 in IHt1.
rewrite <- H6 in IHt1.

rewrite H3 in H1.
induction U ; try solve [unfold subset_sort in H1 ; try discriminate].
simpl in H1.
rewrite H6 in H.
induction (@typ_sort _ _ _ H s) ; try discriminate ; auto.

elim (b U1 U2) ; auto.

apply IHtyp1 ; auto.
Qed.
*)
