
Require Import Terms.

(* unused *)
Definition tCaseNav t xv tv te :=
  let x := fresh (xv :: fv_tm tv ++ fv_tm te) in
  TLet x (tToSum t)
    (TMatch x xv tv te).

Definition tSumToNav t :=
  let x := 0 in
  tMatch t
    x (TVar x)
      (TMkNav x).

(* A different encoding from LThrow into LNaV, which is a bit closer
   to the standard 'error monad' *)

(* If t evaluates to res in LambdaThrow,
   the result of evaluating (encode t) in LambdaNaV is:
   if res = Suc (v@l) then V (Inl ((V v)@l))@bot
   if res = Throw e then (V (Inr (e@bot))@bot
   Invariant1: the sum always stores real values (not NaVs)
   Invariant2: even if the evaluation of (encode t) will always
   produce a sum variables from the original program are always real
   atoms (not NaVs) and are stored unboxed (without the useless
   Inl). *)

(* Instead of using defensive HasTag could also patch-it-all up after
   the fact by turning NaVs into Inrs (similarly to what we do for
   TBOp) -- but in the current shape things look closer to the
   exception monad. *)

Fixpoint encode (t : Tm) : Tm :=
  match t with
  | TVar x => tInl (TVar x)
  | TConst k => tInl (TConst k)
  | TLet x t1 t2 =>
      let y := fresh (x :: fv_tm t2) in
      tSBind (encode t1) x (encode t2)
  | TAbs x t => tInl (TAbs x (encode t))
  | TApp x y =>
      tHasTag TagFun (TVar x) (TApp x y)
  | TInx d x => tInl (TInx d x)
  | TMatch x x1 t1 t2 =>
      tHasTag TagSum (TVar x)
        (TMatch x x1 (encode t1) (encode t2))
  | TTag x => tInl (TTag x)
  | TBOp b x y =>
      let z := 0 in
      (* similar to ToSum, but it leaves things pc-labeled *)
      tCaseNav (TBOp b x y)
        z (TInx DLeft z)
          (TInx DRight z)
  | TBracket x t =>
      tHasTag TagLab (TVar x)
        (tInl (tToSum (TBracket x (tSumToNav (encode t)))))
  | TLabelOf x => tInl (TLabelOf x)
  | TGetPc => tInl TGetPc
  | TThrow x =>
      tHasTag TagExcp (TVar x) (TInx DRight x)
  | TCatch t1 x t2 =>
      tMatch (encode t1)
        x (TInx DLeft x)
          (encode t2)
  | TMkNav _ => tCUnit (* not part of LambdaThrow *)
  | TToSum _ => tCUnit (* not part of LambdaThrow *)
  end.
