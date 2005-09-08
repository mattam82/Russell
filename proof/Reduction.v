Require Import CCP.Calculus.
Require Import CCP.LiftSubst.
Require Import Coq.Arith.Arith.

Lemma one_step_red: forall t u, red1 t u -> red t u.
  intros.
  apply trans_red with t ; auto.
  constructor.
Save.

Hint Resolve one_step_red : CCP.

Lemma red1_red_ind: forall t, forall P : term -> Prop, P t -> 
  (forall u v, red1 u v -> red v t -> P v -> P u) ->
  forall u, red u t -> P u.
Proof.
  cut (forall u t, red u t -> forall P : term -> Prop, P t -> 
    (forall u v, red1 u v -> red v t -> P v -> P u) -> P u).
  intros.
  apply (H u t) ; auto.
  
  induction 1 ; intros ; auto.
  apply IHred.
  eapply H2.
  apply H0.
  constructor.
  assumption.
  intros.
  eapply H2.
  apply H3.
  apply (trans_red _ _ _ H4 H0).
  assumption.
Qed.

Lemma trans_red_red : forall t u v, t =Longrightarrow u -> u =Longrightarrow v -> t =Longrightarrow v.
Proof.
  intros.
  induction H0.
  assumption.
  apply (trans_red _ _ _ IHred H1).
Qed.

Lemma red_red_app : forall u u' v v', u =Longrightarrow u' -> v =Longrightarrow v' ->
  (app u v) =Longrightarrow (app u' v').
Proof.
  induction 1.
  induction 1.

  constructor.
  
  apply trans_red with (app u u0) ; auto.
  auto with CCP.

  intros.
  apply trans_red with (app u0 v') ; auto with CCP.
Qed.


Lemma red_red_abs : forall u u' v v', u =Longrightarrow u' -> v =Longrightarrow v' ->
  (lambda u v) =Longrightarrow (lambda u' v').
Proof.
  induction 1.
  induction 1.

  constructor.
  
  intros ; apply trans_red with (lambda u u0) ;  auto with CCP.

  intros ; apply trans_red with (lambda u0 v') ; auto with CCP.
Qed.
  
Lemma red_red_prod : forall u u' v v', u =Longrightarrow u' -> v =Longrightarrow v' ->
  (Pi u v) =Longrightarrow (Pi u' v').
Proof.
  induction 1.
  induction 1.

  constructor.
  
  intros ; apply trans_red with (Pi u u0) ;  auto with CCP.

  intros ; apply trans_red with (Pi u0 v') ; auto with CCP.
Qed.
  
Lemma red_red_sigma : forall u u' v v', u =Longrightarrow u' -> v =Longrightarrow v' ->
  (Sigma u v) =Longrightarrow (Sigma u' v').
Proof.
  induction 1.
  induction 1.

  constructor.
  
  intros ; apply trans_red with (Sigma u u0) ;  auto with CCP.

  intros ; apply trans_red with (Sigma u0 v') ; auto with CCP.
Qed.

Lemma red_red_subset : forall u u' v v', u =Longrightarrow u' -> v =Longrightarrow v' ->
  (Subset u v) =Longrightarrow (Subset u' v').
Proof.
  induction 1.
  induction 1.

  constructor.
  
  intros ; apply trans_red with (Subset u u0) ;  auto with CCP.

  intros ; apply trans_red with (Subset u0 v') ; auto with CCP.
Qed.

Lemma red_red_let_in : forall u u' v v', u =Longrightarrow u' -> v =Longrightarrow v' ->
  (let_in u v) =Longrightarrow (let_in u' v').
Proof.
  induction 1.
  induction 1.

  constructor.
  
  intros ; apply trans_red with (let_in u u0) ;  auto with CCP.

  intros ; apply trans_red with (let_in u0 v') ; auto with CCP.
Qed.

Lemma red_red_let_tuple : forall u u' v v', u =Longrightarrow u' -> v =Longrightarrow v' ->
  (let_tuple u v) =Longrightarrow (let_tuple u' v').
Proof.
  induction 1.
  induction 1.

  constructor.
  
  intros ; apply trans_red with (let_tuple u u0) ;  auto with CCP.

  intros ; apply trans_red with (let_tuple u0 v') ; auto with CCP.
Qed.

Lemma red_red_pair : forall u u' v v', u =Longrightarrow u' -> v =Longrightarrow v' ->
  (pair u v) =Longrightarrow (pair u' v').
Proof.
  induction 1.
  induction 1.

  constructor.
  
  intros ; apply trans_red with (pair u u0) ;  auto with CCP.

  intros ; apply trans_red with (pair u0 v') ; auto with CCP.
Qed.

Hint Resolve red_red_app red_red_abs red_red_prod red_red_sigma red_red_subset : CCP.
Hint Resolve red_red_let_in red_red_let_tuple red_red_pair : CCP.

Lemma red1_lift: forall u v, red1 u v ->
  forall n k, red1 (lift_rec n u k) (lift_rec n v k).
Proof.
  induction 1 ; simpl ; intros ; auto with CCP.
  rewrite distr_lift_subst ; auto with CCP.
Qed.

Hint Resolve red1_lift : CCP.

Lemma red1_subst_l : forall a t u k, red1 t u ->
  red (subst_rec t a k) (subst_rec u a k).
Proof.
  induction a ; simpl ; autoc.
  
  intros ; elim (lt_eq_lt_dec n k) ; autoc.
  intros a ; elim a ; intros ; autoc.
  
  unfold lift ; autoc.
Qed.

Lemma red1_subst_r: forall t u, red1 t u -> forall a k,
  red1 (subst_rec a t k) (subst_rec a u k).
Proof.
  induction 1 ; simpl ; intros ; autoc.

  rewrite distr_subst ; autoc.
Qed.

Hint Resolve red1_subst_l red1_subst_r : CCP.

Lemma red_prod_prod: forall u v t, red (Pi u v) t ->
  forall P : Prop, (forall a b, t = (Pi a b) -> red u a -> red v b -> P) -> P.
Proof.
  induction 1 ; intros. 

  apply (H u v) ; autoc.

  apply IHred ; intros.
  inversion_clear H2 in H0.
  inversion H0.
  apply (H1 u1 b) ; autoc.
  apply (trans_red _ _ _ H3 H7).

  apply (H1 a u2) ; autoc.
  apply (trans_red _ _ _ H4 H7).
Qed.

Lemma red_sort_sort: forall s t, red (sort s) t -> (~ t = sort s) -> False.
Proof.
  induction 1 ; intros ; autoc.
  apply IHred.
  
  unfold not ; intros.
  apply H1.
  rewrite H2 in H0.
  inversion H0.
Qed.

Lemma one_step_conv_exp : forall t u, red1 t u -> conv u t.
Proof.
  intros.
  apply trans_conv_exp with u ; autoc.
Qed.

Lemma red_conv : forall t u, red t u -> conv t u.
Proof.
  induction 1 ; autoc.
  apply trans_conv_red with u ; autoc.
Qed.

Hint Resolve one_step_conv_exp red_conv : CCP.


Lemma conv_left_exp : forall t u v, conv t u -> red v t -> conv v u.
Proof.
  induction 1 ; autoc.
  intros.
  eapply trans_conv_red with u ; autoc.
  intros.
  eapply trans_conv_exp with u ; autoc.
Qed.
(*
Lemma conv_left_red : forall t u v, conv t u -> red t v -> conv v u.
Proof.
  induction 1 ; autoc.
  intros.
  induction H ; autoc.
  pose (trans_conv_exp _ _ _ (refl_conv v) H0).
  
  Lemma conv_red_exp : forall t u, red t u -> conv u t.
  Proof.
    intros.
    induction H ; autoc.
    induction IHred ; autoc.
    apply trans_conv_red with u0 ; autoc.
    apply IHIHred.
    apply (trans_red_red _ _ _ (one_step_red _ _ H1) H).
    apply trans_conv_exp with u0 ; autoc.
    apply IHIHred.
    
    
    
  


  eapply trans_conv_red with u ; autoc.
  intros.
  eapply trans_conv_exp with u ; autoc.
Qed.
*)

Lemma trans_conv : forall t u v, conv t u -> conv u v -> conv t v.
Proof.
  intros.
  induction H0 ; autoc.
  apply trans_conv_red with u0 ; autoc.
  apply trans_conv_exp with u0 ; autoc.
Qed.
  
Lemma sym_conv : forall t u, conv t u -> conv u t.
Proof.
  induction 1 ; autoc.

  pose (one_step_conv_exp _ _ H0).
  apply (trans_conv _ _ _ c IHconv).

  pose (trans_conv_red _ _ _ (refl_conv v) H0).
  apply (trans_conv _ _ _ c IHconv).
Qed.
    
Hint Immediate sym_conv : CCP.

Lemma conv_conv_prod: forall a b c d, conv a b -> conv c d ->
  conv (Pi a c) (Pi b d).
Proof.
  intros.
  apply trans_conv with (Pi a d).
  elim H0 ; intros ; autoc.
  apply trans_conv_red with (Pi a u) ; autoc.

  apply trans_conv_exp with (Pi a u) ; autoc.

  elim H ; intros ; autoc.
  apply trans_conv_red with (Pi u d) ; autoc.
  apply trans_conv_exp with (Pi u d) ; autoc.
Qed.


Lemma conv_conv_lift: forall a b, forall n k, conv a b ->
  conv (lift_rec n a k) (lift_rec n b k).
Proof.
  intros.
  elim H ; intros ; autoc.
  
  apply trans_conv_red with (lift_rec n u k) ; autoc.

  apply trans_conv_exp with (lift_rec n u k) ; autoc.
Qed.

Lemma conv_conv_subst: forall a b c d, forall k, conv a b -> conv c d ->
  conv (subst_rec a c k) (subst_rec b d k).
Proof.
  intros.
  apply trans_conv with (subst_rec a d k).

  elim H0 ; intros ; autoc.
  apply trans_conv_red with (subst_rec a u k) ; autoc.
  apply trans_conv_exp with (subst_rec a u k) ; autoc.

  elim H ; intros ; autoc.
  apply trans_conv with (subst_rec u d k) ; autoc.
  
  apply trans_conv with (subst_rec u d k) ; autoc.
  apply sym_conv ; autoc.
Qed.

Hint Resolve conv_conv_prod conv_conv_lift conv_conv_subst.


(* 
 Local Variables:
 coq-prog-name: "coqtop.opt -emacs -R . CCP"
 End:
*)



  