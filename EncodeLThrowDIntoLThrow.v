
Require Import Terms.

Definition tForce (tsum : Tm) : Tm :=
  let x := 0 in
  tMatch tsum
    x (TVar x)
      (TThrow x).

Definition tForceTag (b : BOp) (t : Tm) : Tm :=
  let x := fresh (fv_tm t) in
  TLet x (tForce t)
    (match b with
     | BEq =>
       tIf (tEq (TTag x) (tCTag TagFun))
         (tThrow (tCExcp eType))
         (tIf (tEq (TTag x) (tCTag TagSum))
           (tThrow (tCExcp eType))
           (TVar x))
     | _ =>
       tIf (tEq (TTag x) (tCTag TagLab))
         (TVar x)
         (tThrow (tCExcp eType))
    end).

Fixpoint encode (t : Tm) : Tm :=
  match t with
  | TVar x => TVar x
  | TConst k => tInl (TConst k)
  | TLet x t1 t2 => 
      TLet x (encode t1) (encode t2)
  | TAbs x t => tInl (TAbs x (encode t))
  | TApp x y =>
      tApp (tForce (TVar x)) (TVar y)
  | TInx d x => tInl (TInx d x)
  | TMatch x x1 t1 t2 =>
      tMatch (tForce (TVar x)) x1 (encode t1) (encode t2)
  | TTag x =>
      tInl (tTag (tForce (TVar x)))
  (* The next 2 are so complicated (additional TMatch y z' ...)
     because the semantics of BOp in LThrow and LThrowD is not fully
     accurate (Q: why does it raise the pc by the label on the 2nd
     arg, before the 2nd arg was even introspected? Simplicity my ass! *)
  | TBOp BJoin x y =>
      let z' := fresh [x,y] in
      TMatch y
        z' (tInl (tBOp BJoin (tForceTag BJoin (TVar x))
                             (tForceTag BJoin (TVar y))))
           (tInl (tBOp BJoin (tForceTag BJoin (TVar x))
                             (tForceTag BJoin (TVar y))))
  (* additional massaging for BEq and BCmp *)
  (*    since they return booleans encoded as sums *)
  | TBOp b x y =>
      let z' := fresh [x,y] in
      let z := 0 in
      TMatch y
        z' (tInl (tMatch (tBOp b (tForceTag b (TVar x))
                                 (tForceTag b (TVar y)))
              z (tInl (TInx DLeft z))
                (tInr (TInx DLeft z))))
           (tInl (tMatch (tBOp b (tForceTag b (TVar x))
                                 (tForceTag b (TVar y)))
              z (tInl (TInx DLeft z))
                (tInr (TInx DLeft z))))
  | TBracket x t =>
      tBracket (tForce (TVar x)) (tForce (encode t))
  | TLabelOf x => tInl (TLabelOf x)
  | TGetPc => tInl TGetPc
  | TThrow x =>
      tThrow (tForce (TVar x))
  | TCatch t1 x t2 =>
      TCatch (encode t1) x (TLet x (TInx DLeft x) (encode t2))
  | TToSum x =>
      let y := 0 in
      (tBracket (TLabelOf x)
        (TMatch x
          y (tInl (TInx DLeft y))
            (tInr (TInx DLeft y))))
  | TMkNav _ => tCUnit (* not part of LambdaThrowD *)
  end.
