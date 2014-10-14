
Require Import Terms.

Definition tCaseNav t x tv te :=
  let x' := fresh (x :: fv_tm tv ++ fv_tm te) in
  TLet x' (tToSum t)
    (TMatch x' x tv te).

Definition tNavBind t xk tk :=
  let z := 0 in
  tCaseNav t xk tk (tMkNav (TVar xk)).

Definition tNavMap f t :=
  let x := 0 in
  tCaseNav t
    x (f (TVar x)) (TMkNav x).

Definition tNavHasTag x T tk :=
  tIf (tEq (TTag x) (tCTag T))
    tk
    (tMkNav (tCExcp eType)).

Definition tBox := tInl.
Definition tUnbox t :=
  let z := 0 in
  tMatch t z (TVar z) (TVar z).

(* If t evaluates to res in LambdaThrow,
the result of evaluating (encode t) in LambdaNaV is:
if res = Suc (v@l) then V (box ((V v)@l))@bottom
if res = Throw e then (D e)@bottom
Invariant1: boxes always store real values (not NaVs)
Invariant2: even if the evaluation of (encode t) will always produce a box
variables from the original program are stored unboxed in rho. *)
Fixpoint encode (t : Tm) : Tm :=
  match t with
  | TVar x => tBox (TVar x)
  | TConst k => tBox (TConst k)
  | TLet x t1 t2 => 
      let y := fresh (x :: fv_tm t2) in
      tNavBind (encode t1) y
        (TLet x (tUnbox (TVar y)) (encode t2))
  | TAbs x t => tBox (TAbs x (encode t))
  | TApp x y => TApp x y
  | TInx d x => tBox (TInx d x)
  | TMatch x x1 t1 t2 =>
      TMatch x x1 (encode t1) (encode t2)
  | TTag x => tBox (TTag x)
  | TBOp b x y =>
      tNavMap tBox (TBOp b x y)
  | TBracket x t =>
      tNavHasTag x TagLab
        (tBox (tToSum (TBracket x (tNavMap tUnbox (encode t)))))
  | TLabelOf x => tBox (TLabelOf x)
  | TGetPc => tBox TGetPc
  | TThrow x => 
      (* using CaseNav to get valueOf? *)
      tCaseNav (TVar x)
        x (TMkNav x)
          (TMkNav x)
  | TCatch t1 x t2 =>
      tCaseNav (encode t1)
        x (TVar x)
          (encode t2)
  | TMkNav _ => tCUnit (* not part of LambdaThrow *)
  | TToSum _ => tCUnit (* not part of LambdaThrow *)
  end.
