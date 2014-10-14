
Require Import Terms.

(* The only points where something interesting happens are:
   - for brackets, where we add a toSum around them
   - for TTag where we add a bracket around  *)
Fixpoint encode (t : Tm) : Tm :=
  match t with
  | TVar x => TVar x
  | TConst k => TConst k
  | TLet x t1 t2 => 
      TLet x (encode t1) (encode t2)
  | TAbs x t => TAbs x (encode t)
  | TApp x y => TApp x y
  | TInx d x => TInx d x
  | TMatch x x1 t1 t2 => TMatch x x1 (encode t1) (encode t2)
  | TTag x => tBracket (TLabelOf x) (TTag x)
  | TBOp b x y => TBOp b x y
  | TBracket x t => tToSum (TBracket x (encode t))
  | TLabelOf x => TLabelOf x
  | TGetPc => TGetPc
  | TThrow x => TThrow x
  | TCatch t1 x t2 =>
      TCatch (encode t1) x (encode t2)
  | TMkNav _ => tCUnit (* not part of LambdaThrow *)
  | TToSum x => tCUnit (* not part of LambdaThrow *)
  end.
