
Require Import Terms.

Definition tCheckClr (tl : Tm) (c : Var) (tk : Tm) : Tm :=
  tIf (tCmp tl (TVar c)) tk (tInr tCUnit).

Definition tClrBind := tSBind.

(* Unguarded checks need to add an extra clearance-inl when failing *)
Definition tHasTag' T (t tk : Tm) : Tm :=
  tIf (tEq (tTag t) (TConst (CTag T)))
    tk (tInl (tInr (TConst (CExcp eType)))).
Definition tSBind' tsum xk tk :=
  let x := 0 in
  tMatch tsum xk tk (tInl (TInx DRight xk)).

Definition tBOpCheckTag b (t tk : Tm) : Tm :=
  match b with
  | BEq =>
    (* only functions and sums are not comparable *)
    tIf (tEq (tTag t) (TConst (CTag TagFun)))
      (tInr (TConst (CExcp eType)))
      (tIf (tEq (tTag t) (TConst (CTag TagSum)))
        (tInr (TConst (CExcp eType)))
        tk)
  | _ => (* b_cmp and b_join work on labels*)
    tIf (tEq (tTag t) (TConst (CTag TagLab)))
      tk (tInr (TConst (CExcp eType)))
  end.

(* Here is how we map results:
   v@l               --> (Inl (Inl (v@bot))@l)@bot
   (D e)@l           --> (Inl (Inr (e@bot))@l)@bot
   clearance failure --> (Inr ())@bot
Note that, similarly to ET2N and ET2Np, the variables in the
environment won't need to store the outer option; but they
will need to store the inner option. *)

Fixpoint encode' (t : Tm) (c : Var) : Tm :=
  match t with
  | TVar x => tInl (TVar x)
  | TConst k => tInl (tInl (TConst k))
  | TLet x t1 t2 => 
      tClrBind (encode' t1 c) x (encode' t2 c)
  | TAbs x t => tInl (tInl (TAbs x (encode' t c)))
  | TApp x y =>
      let x' := fresh [x,y] in
      tCheckClr (TLabelOf x) c
        (tSBind' (TVar x) x'
          (tHasTag' TagFun (TVar x')
            (TApp x' y)))
  | TInx d x => tInl (tInl (TInx d x))
  | TMatch x x1 t1 t2 =>
      let x' := fresh (x :: x1 :: fv_tm t1 ++ fv_tm t2) in
      tCheckClr (TLabelOf x) c
        (tSBind' (TVar x) x'
          (tHasTag' TagSum (TVar x')
            (TMatch x' x1 (encode' t1 c) (encode' t2 c))))
  | TTag x =>
      let x' := fresh [x] in
      tInl (tBracket (TLabelOf x)
        (tSBind (TVar x) x'
          (tInl (TTag x'))))
  | TBOp b x y =>
      let x' := fresh [x,y] in
      let y' := fresh [x,y,x'] in
      tInl (tBracket (tJoin (TLabelOf x) (TLabelOf y))
        (tSBind (TVar x) x'
          (tBOpCheckTag b (TVar x')
            (tSBind (TVar y) y'
              (tBOpCheckTag b (TVar y')
                (tInl (match b with
                | BJoin => TBOp b x' y'
                | _ =>
                  (tMatch (TBOp b x' y')
                    0 (tInl (TInx DLeft 0))
                      (tInr (TInx DLeft 0)))
                end)))))))
  | TBracket x t =>
      let x' := fresh (x :: fv_tm t) in
      let y := fresh (x' :: x :: fv_tm t) in
      let c' := fresh (c :: x :: fv_tm t) in
      tCheckClr (TLabelOf x) c
        (tSBind' (TVar x) x'
          (tHasTag' TagLab (TVar x')
            (tInl (TBracket x'
              (TLet c' (tJoin (TVar x') TGetPc)
                (TLet y (encode' t c')
                  (TMatch y
                    y (tIf (tCmp (TLabelOf y) (TVar c'))
                        (TVar y)
                        (tInr (TConst (CExcp eBracket))))
                      (tInr (TConst (CExcp eBracket))))))))))
  | TLabelOf x => tInl (tInl (TLabelOf x))
  | TGetPc => tInl (tInl TGetPc)
  | TMkNav x =>
      let x' := fresh [x] in
      tInl (tBracket (TLabelOf x)
        (tSBind (TVar x) x'
          (tHasTag TagExcp (TVar x')
            (tInr (TVar x')))))
  | TToSum x =>
      let z := fresh [x] in
      tInl (tBracket (TLabelOf x)
        (tInl (TMatch x
          z (tInl (tInl (TVar z)))
            (tInr (tInl (TVar z))))))
  | TThrow _ => tCUnit (* not part of LambdaNav *)
  | TCatch _ _ _ => tCUnit (* not part of LambdaNav *)
  end.

Definition encode t :=
  (* Q: does x need to avoid all bound(!) variables in t? YES!
     otherwise there is a risk gets shadowed? YES!
     Is it enough to avoid bound vars in t?
     Don't we actually need to avoid bound vars in (encode' t ???)?
     Circular? *)
  (* let x := fresh (fv_tm t) in *)
  (* solution: keep the clearance variables disjoint from all
     the other variables; hack that achieves this for now: *)
  let x := 100 in
  TLet x (tCLab top) (encode' t x).
  (* could also use odd vs even variables *)
  (* if we had pairs we could have propagated c using state monad *)
