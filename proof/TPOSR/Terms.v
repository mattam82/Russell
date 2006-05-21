Require Export Arith.
Require Export Compare_dec.
Require Export Relations.
Require Export Lambda.Terms.

Implicit Types i k m n p : nat.
Implicit Type s : sort.

  Inductive lterm : Set :=
    | Srt_l : sort -> lterm
    | Ref_l : nat -> lterm
    | Abs_l : lterm -> lterm -> lterm
    | App_l : lterm -> lterm -> lterm -> lterm
    | Pair_l : lterm -> lterm -> lterm -> lterm
    | Prod_l : lterm -> lterm -> lterm
    | Sum_l : lterm -> lterm -> lterm
    | Subset_l : lterm -> lterm -> lterm
    | Pi1_l : lterm -> lterm
    | Pi2_l : lterm -> lterm
    | Let_in_l : lterm -> lterm -> lterm.

  Implicit Types A B M N T t u v : lterm.

  Fixpoint llift_rec n t {struct t} : nat -> lterm :=
    fun k =>
      match t with
	| Srt_l s => Srt_l s
	| Ref_l i =>
          match le_gt_dec k i with
            | left _ => Ref_l (n + i)
            | right _ => Ref_l i
          end
	| Abs_l T M => Abs_l (llift_rec n T k) (llift_rec n M (S k))
	| App_l T u v => App_l  (llift_rec n T k) (llift_rec n u k) (llift_rec n v k)
	| Pair_l T A B => Pair_l (llift_rec n T k) (llift_rec n A k) (llift_rec n B k)
	| Prod_l A B => Prod_l (llift_rec n A k) (llift_rec n B (S k))
	| Sum_l A B => Sum_l (llift_rec n A k) (llift_rec n B (S k))
	| Subset_l A B => Subset_l (llift_rec n A k) (llift_rec n B (S k))
	| Pi1_l A => Pi1_l (llift_rec n A k)
	| Pi2_l A => Pi2_l (llift_rec n A k)
	| Let_in_l A B => Let_in_l (llift_rec n A k) (llift_rec n B (S k))
      end.

  Definition llift n t := llift_rec n t 0.

  Fixpoint lsubst_rec N M {struct M} : nat -> lterm :=
    fun k =>
      match M with
	| Srt_l s => Srt_l s
	| Ref_l i =>
          match lt_eq_lt_dec k i with
            | inleft C =>
              match C with
		| left _ => Ref_l (pred i)
		| right _ => llift k N
              end
            | inright _ => Ref_l i
          end
	| Abs_l A B => Abs_l (lsubst_rec N A k) (lsubst_rec N B (S k))
	| App_l T u v => App_l (lsubst_rec N T k) (lsubst_rec N u k) (lsubst_rec N v k)
	| Pair_l T A B => Pair_l (lsubst_rec N T k) (lsubst_rec N A k) (lsubst_rec N B k)
	| Prod_l T U => Prod_l (lsubst_rec N T k) (lsubst_rec N U (S k))
	| Sum_l T U => Sum_l (lsubst_rec N T k) (lsubst_rec N U (S k))
	| Subset_l T U => Subset_l (lsubst_rec N T k) (lsubst_rec N U (S k))
	| Pi1_l T => Pi1_l (lsubst_rec N T k)
	| Pi2_l T => Pi2_l (lsubst_rec N T k)
	| Let_in_l T U => Let_in_l (lsubst_rec N T k) (lsubst_rec N U (S k))
    end.

  Definition lsubst N M := lsubst_rec N M 0.

  Inductive free_db : nat -> lterm -> Prop :=
    | db_srt : forall n s, free_db n (Srt_l s)
    | db_ref : forall k n, k > n -> free_db k (Ref_l n)
    | db_abs :
        forall k A M, free_db k A -> free_db (S k) M -> free_db k (Abs_l A M)
    | db_app :
        forall k T u v, free_db k T -> free_db k u -> free_db k v -> free_db k (App_l T u v)
    | db_pair :
        forall k T u v, free_db k T -> free_db k u -> free_db k v -> free_db k (Pair_l T u v)
    | db_prod :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Prod_l A B) 
    | db_sum :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Sum_l A B)
    | db_subset :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Subset_l A B)
    | db_pi1 : forall k A, free_db k A -> free_db k (Pi1_l A)
    | db_pi2 : forall k A, free_db k A -> free_db k (Pi2_l A)
    | db_let_in :
        forall k A B, free_db k A -> free_db (S k) B -> free_db k (Let_in_l A B).


  Inductive subt_bind T M : lterm -> Prop :=
    | Bsbt_abs : subt_bind T M (Abs_l T M)
    | Bsbt_prod : subt_bind T M (Prod_l T M)
    | Bsbt_sum : subt_bind T M (Sum_l T M)
    | Bsbt_subset : subt_bind T M (Subset_l T M)
    | Bsbt_let_in : subt_bind T M (Let_in_l T M).

  Inductive subt_nobind (m : lterm) : lterm -> Prop :=
    | Nbsbt_abs : forall n : lterm, subt_nobind m (Abs_l m n)
    | Nbsbt_app_T : forall u v, subt_nobind m (App_l m u v)
    | Nbsbt_app_l : forall T v, subt_nobind m (App_l T m v)
    | Nbsbt_app_r : forall T u, subt_nobind m (App_l T u m)
    | Nbsbt_pair_T : forall u v, subt_nobind m (Pair_l m u v)
    | Nbsbt_pair_l : forall T v, subt_nobind m (Pair_l T m v)
    | Nbsbt_pair_r : forall T u, subt_nobind m (Pair_l T u m)
    | Nbsbt_prod : forall n : lterm, subt_nobind m (Prod_l m n)
    | Nbsbt_sum : forall n : lterm, subt_nobind m (Sum_l m n)
    | Nbsbt_subset : forall n : lterm, subt_nobind m (Subset_l m n)
    | Nbsbt_pi1 : subt_nobind m (Pi1_l m)
    | Nbsbt_pi2 : subt_nobind m (Pi2_l m)
    | Nbsbt_let_in : forall n : lterm, subt_nobind m (Let_in_l m n).

  Inductive sublterm (m n : lterm) : Prop :=
    | Sbtrm_bind : forall t, subt_bind t m n -> sublterm m n
    | Sbtrm_nobind : subt_nobind m n -> sublterm m n.

  Inductive mem_sort s : lterm -> Prop :=
    | mem_eq : mem_sort s (Srt_l s)
    | mem_prod_l : forall u v, mem_sort s u -> mem_sort s (Prod_l u v)
    | mem_prod_r : forall u v, mem_sort s v -> mem_sort s (Prod_l u v)
    | mem_abs_l : forall u v, mem_sort s u -> mem_sort s (Abs_l u v)
    | mem_abs_r : forall u v, mem_sort s v -> mem_sort s (Abs_l u v)
    | mem_app_T : forall T u v, mem_sort s T -> mem_sort s (App_l T u v)
    | mem_app_l : forall T u v, mem_sort s u -> mem_sort s (App_l T u v)
    | mem_app_r : forall T u v, mem_sort s v -> mem_sort s (App_l T u v)
    | mem_pair_T : forall T u v, mem_sort s T -> mem_sort s (Pair_l T u v)
    | mem_pair_l : forall T u v, mem_sort s u -> mem_sort s (Pair_l T u v)
    | mem_pair_r : forall T u v, mem_sort s v -> mem_sort s (Pair_l T u v)
    | mem_sum_l : forall u v, mem_sort s u -> mem_sort s (Sum_l u v)
    | mem_sum_r : forall u v, mem_sort s v -> mem_sort s (Sum_l u v)
    | mem_subset_l : forall u v, mem_sort s u -> mem_sort s (Subset_l u v)
    | mem_subset_r : forall u v, mem_sort s v -> mem_sort s (Subset_l u v)
    | mem_pi1 : forall u, mem_sort s u -> mem_sort s (Pi1_l u)
    | mem_pi2 : forall u, mem_sort s u -> mem_sort s (Pi2_l u)
    | mem_let_in_l : forall u v, mem_sort s u -> mem_sort s (Let_in_l u v)
    | mem_let_in_r : forall u v, mem_sort s v -> mem_sort s (Let_in_l u v).

Hint Resolve db_srt db_ref db_abs db_app db_pair db_prod db_sum db_subset db_let_in db_pi1 db_pi2 : coc.
Hint Resolve Bsbt_abs Bsbt_prod Bsbt_sum Bsbt_subset Bsbt_let_in : coc.
Hint Resolve Nbsbt_abs Nbsbt_app_T Nbsbt_app_l Nbsbt_app_r Nbsbt_pair_T Nbsbt_pair_l
    Nbsbt_pair_r Nbsbt_pi1 Nbsbt_pi2 Nbsbt_prod Nbsbt_sum Nbsbt_subset
    Nbsbt_let_in : coc.
Hint Resolve Sbtrm_nobind: coc.
  
Hint Resolve mem_eq mem_prod_l mem_prod_r mem_abs_l mem_abs_r mem_app_T mem_app_l
  mem_app_r mem_pair_T mem_pair_l mem_pair_r : coc.
Hint Resolve mem_sum_l mem_sum_r mem_subset_l mem_subset_r mem_pi1 mem_pi2
  mem_let_in_l mem_let_in_r : coc.


