Require Export Arith.
Require Export Compare_dec.
Require Export Relations.

Implicit Types i k m n p : nat.

Inductive sort : Set :=
    | kind : sort
    | prop : sort
    | set : sort.

Implicit Type s : sort.

Definition is_prop s := s = prop \/ s = set.

(* Scheme to split between kind and the lower level sorts *)
  Lemma sort_level_ind :
   forall P : sort -> Prop,
   P kind -> (forall s, is_prop s -> P s) -> forall s, P s.
Proof.
unfold is_prop in |- *.
simple destruct s; auto.
Qed.

  Inductive term : Set :=
    | Srt : sort -> term
    | Ref : nat -> term
    | Abs : term -> term -> term
    | App : term -> term -> term
    | Pair : term -> term -> term -> term
    | Prod : term -> term -> term
    | Sum : term -> term -> term
    | Subset : term -> term -> term
    | Pi1 : term -> term
    | Pi2 : term -> term.

  Implicit Types A B M N T t u v : term.

  Fixpoint lift_rec n t {struct t} : nat -> term :=
    fun k =>
      match t with
	| Srt s => Srt s
	| Ref i =>
          match le_gt_dec k i with
            | left _ => Ref (n + i)
            | right _ => Ref i
          end
	| Abs T M => Abs (lift_rec n T k) (lift_rec n M (S k))
	| App u v => App (lift_rec n u k) (lift_rec n v k)
	| Pair T A B => Pair (lift_rec n T k) (lift_rec n A k) (lift_rec n B k)
	| Prod A B => Prod (lift_rec n A k) (lift_rec n B (S k))
	| Sum A B => Sum (lift_rec n A k) (lift_rec n B (S k))
	| Subset A B => Subset (lift_rec n A k) (lift_rec n B (S k))
	| Pi1 A => Pi1 (lift_rec n A k)
	| Pi2 A => Pi2 (lift_rec n A k)
      end.

  Definition lift n t := lift_rec n t 0.

  Fixpoint subst_rec N M {struct M} : nat -> term :=
    fun k =>
      match M with
	| Srt s => Srt s
	| Ref i =>
          match lt_eq_lt_dec k i with
            | inleft C =>
              match C with
		| left _ => Ref (pred i)
		| right _ => lift k N
              end
            | inright _ => Ref i
          end
	| Abs A B => Abs (subst_rec N A k) (subst_rec N B (S k))
	| App u v => App (subst_rec N u k) (subst_rec N v k)
	| Pair T A B => Pair (subst_rec N T k) (subst_rec N A k) (subst_rec N B k)
	| Prod T U => Prod (subst_rec N T k) (subst_rec N U (S k))
	| Sum T U => Sum (subst_rec N T k) (subst_rec N U (S k))
	| Subset T U => Subset (subst_rec N T k) (subst_rec N U (S k))
	| Pi1 T => Pi1 (subst_rec N T k)
	| Pi2 T => Pi2 (subst_rec N T k)
    end.

  Definition subst N M := subst_rec N M 0.

  Inductive free_db : nat -> term -> Prop :=
    | db_srt : forall n s, free_db n (Srt s)
    | db_ref : forall k n, k > n -> free_db k (Ref n)
    | db_abs :
        forall k A M, free_db k A -> free_db (S k) M -> free_db k (Abs A M)
    | db_app :
        forall k u v, free_db k u -> free_db k v -> free_db k (App u v)
    | db_pair :
        forall k T u v, free_db k T -> free_db k u -> free_db k v -> free_db k (Pair T u v)
    | db_prod :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Prod A B) 
    | db_sum :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Sum A B)
    | db_subset :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Subset A B)
    | db_pi1 : forall k A, free_db k A -> free_db k (Pi1 A)
    | db_pi2 : forall k A, free_db k A -> free_db k (Pi2 A).


  Inductive subt_bind T M : term -> Prop :=
    | Bsbt_abs : subt_bind T M (Abs T M)
    | Bsbt_prod : subt_bind T M (Prod T M)
    | Bsbt_sum : subt_bind T M (Sum T M)
    | Bsbt_subset : subt_bind T M (Subset T M).

  Inductive subt_nobind (m : term) : term -> Prop :=
    | Nbsbt_abs : forall n : term, subt_nobind m (Abs m n)
    | Nbsbt_app_l : forall v, subt_nobind m (App m v)
    | Nbsbt_app_r : forall u, subt_nobind m (App u m)
    | Nbsbt_pair_T : forall u v, subt_nobind m (Pair m u v)
    | Nbsbt_pair_l : forall T v, subt_nobind m (Pair T m v)
    | Nbsbt_pair_r : forall T u, subt_nobind m (Pair T u m)
    | Nbsbt_prod : forall n : term, subt_nobind m (Prod m n)
    | Nbsbt_sum : forall n : term, subt_nobind m (Sum m n)
    | Nbsbt_subset : forall n : term, subt_nobind m (Subset m n)
    | Nbsbt_pi1 : subt_nobind m (Pi1 m)
    | Nbsbt_pi2 : subt_nobind m (Pi2 m).

  Inductive subterm (m n : term) : Prop :=
    | Sbtrm_bind : forall t, subt_bind t m n -> subterm m n
    | Sbtrm_nobind : subt_nobind m n -> subterm m n.

  Inductive mem_sort s : term -> Prop :=
    | mem_eq : mem_sort s (Srt s)
    | mem_prod_l : forall u v, mem_sort s u -> mem_sort s (Prod u v)
    | mem_prod_r : forall u v, mem_sort s v -> mem_sort s (Prod u v)
    | mem_abs_l : forall u v, mem_sort s u -> mem_sort s (Abs u v)
    | mem_abs_r : forall u v, mem_sort s v -> mem_sort s (Abs u v)
    | mem_app_l : forall u v, mem_sort s u -> mem_sort s (App u v)
    | mem_app_r : forall u v, mem_sort s v -> mem_sort s (App u v)
    | mem_pair_T : forall T u v, mem_sort s T -> mem_sort s (Pair T u v)
    | mem_pair_l : forall T u v, mem_sort s u -> mem_sort s (Pair T u v)
    | mem_pair_r : forall T u v, mem_sort s v -> mem_sort s (Pair T u v)
    | mem_sum_l : forall u v, mem_sort s u -> mem_sort s (Sum u v)
    | mem_sum_r : forall u v, mem_sort s v -> mem_sort s (Sum u v)
    | mem_subset_l : forall u v, mem_sort s u -> mem_sort s (Subset u v)
    | mem_subset_r : forall u v, mem_sort s v -> mem_sort s (Subset u v)
    | mem_pi1 : forall u, mem_sort s u -> mem_sort s (Pi1 u)
    | mem_pi2 : forall u, mem_sort s u -> mem_sort s (Pi2 u).

Hint Resolve db_srt db_ref db_abs db_app db_pair db_prod db_sum db_subset db_pi1 db_pi2 : coc.
Hint Resolve Bsbt_abs Bsbt_prod Bsbt_sum Bsbt_subset : coc.
Hint Resolve Nbsbt_abs Nbsbt_app_l Nbsbt_app_r Nbsbt_pair_T Nbsbt_pair_l
    Nbsbt_pair_r Nbsbt_pi1 Nbsbt_pi2 Nbsbt_prod Nbsbt_sum Nbsbt_subset : coc.
Hint Resolve Sbtrm_nobind: coc.
  
Hint Resolve mem_eq mem_prod_l mem_prod_r mem_abs_l mem_abs_r mem_app_l
  mem_app_r mem_pair_T mem_pair_l mem_pair_r : coc.
Hint Resolve mem_sum_l mem_sum_r mem_subset_l mem_subset_r mem_pi1 mem_pi2 : coc.


