Require Import Termes.
Require Import Reduction.
Require Import Conv.
Require Import LiftSubst.
Require Import Env.
Require Import CCPD.Types.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.
Implicit Types e f g : env.

Set Implicit Arguments.

Axiom inv_conv_prod_sort_l : forall e U V U' V' s, e |- Prod U V : Srt s -> e |- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> { s1 : sort | e |- U : Srt s1 /\ e |- U' : Srt s1 }. 

Axiom inv_conv_prod_sort_r : forall e U V U' V' s, e |- Prod U V : Srt s -> e |- Prod U' V' : Srt s ->
  conv (Prod U V) (Prod U' V') -> U' :: e |- V : Srt s /\ U' :: e |- V' : Srt s. 

Axiom inv_conv_sum_sort_l : forall e U V U' V' s, e |- Sum U V : Srt s -> e |- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> { s1 : sort | e |- U : Srt s1 /\ e |- U' : Srt s1 }. 

Axiom inv_conv_sum_sort_r : forall e U V U' V' s, e |- Sum U V : Srt s -> e |- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> U :: e |- V : Srt s /\ U :: e |- V' : Srt s.

Axiom inv_conv_sum_sort : forall e U V U' V' s, e |- Sum U V : Srt s -> e |- Sum U' V' : Srt s ->
  conv (Sum U V) (Sum U' V') -> 
  exists s1, exists s2, e |- U : Srt s1 /\ e |- U' : Srt s1 /\ U :: e |- V : Srt s2 /\ U :: e |- V' : Srt s2
  /\ sum_sort s1 s2 s.	        
