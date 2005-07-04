fun x : nat =>
nat_rec (fun x0 : nat => forall y : nat, {x0 <= y} + {y < x0})
  (fun y : nat =>
   match y as n return ({0 <= n} + {n < 0}) with
   | O => left (0 < 0) (le_n 0)
   | S y0 => left (S y0 < 0) (le_S 0 y0 (le_lt_dec_subproof1 y0))
   end)
  (fun (x0 : nat) (IHx : forall y : nat, {x0 <= y} + {y < x0}) (y : nat) =>
   match y as n return ({S x0 <= n} + {n < S x0}) with
   | O => right (S x0 <= 0) (le_lt_dec_subproof2 x0 IHx)
   | S y0 =>
       match IHx y0 with
       | left l => left (S y0 < S x0) (le_lt_dec_subproof3 x0 IHx y0 l)
       | right l => right (S x0 <= S y0) (le_lt_dec_subproof4 x0 IHx y0 l)
       end
   end) x
