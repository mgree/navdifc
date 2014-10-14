Require Import Terms.
Require Import LNaVSyntax.
Require Import LThrowDBigStep. (* reusing helpers *)

(** * Continuations and partial configurations *)

Inductive Frame : Type :=
| RLet : Var -> Tm -> Frame
| RRet : Env -> Frame
| RBrk : Lab -> Lab -> Frame (* final label + original pc *)
| RCatch : Var -> Tm -> Frame.

Definition Cont := list Frame.

Definition PCfg := prod (prod Lab Env) Cont.

Inductive RCfg : Type :=
| CR : Tm -> RCfg    (* term to be reduced *)
| CA : Atom -> RCfg  (* return atom *)
| CT : Excp -> RCfg. (* thrown exception *)

Definition Cfg := prod PCfg RCfg.

Notation "v @ L" := (v,L) (at level 5).

Notation "<< pc , r , k , X >>" := (((pc, r), k), X) (at level 5).

Definition result_to_rcfg r :=
  match r with
  | Suc a => CA a
  | Throw e => CT e
  end.

(** * Small-step semantics defined as a total(!) function *)

Definition step (c : Cfg) : Cfg :=
  match c with
  (* s_var *)
  | << pc, rho, k, CR (TVar x) >> =>
    match get rho x with
    | Some a =>
      << pc, rho, k, CA a >>
    | None =>
      << pc, rho, k, CT eUnbound >>
    end
  (* s_const *)
  | << pc, rho, k, CR (TConst c) >> =>
    << pc, rho, k, CA (V (VConst c))@bot>>
  (* s_let_start *)
  | << pc, rho, k, CR (TLet x t1 t2) >> =>
    << pc, rho, RLet x t2 :: k, CR t1 >>
  (* s_let_bind *)
  | << pc, rho, RLet x t :: k, CA a >> =>
    << pc, (x,a) :: rho, RRet rho :: k, CR t >>
  (* s_let_unwind *)
  | << pc, rho, RLet x t :: k, CT e >> =>
    << pc, rho, k, CT e >>
  (* s_abs *)
  | << pc, rho, k, CR (TAbs x t) >> =>
    << pc, rho, k, CA (V (VClos rho x t))@bot >>
  (* s_app *)
  | << pc, rho, k, CR (TApp x1 x2) >> =>
    match get rho x1, get rho x2 with
    | Some ((V (VClos rho' x t))@L), Some a =>
      << pc\_/L, (x,a) :: rho', RRet rho :: k, CR t >>
    | Some (b,L), Some a =>
      << pc\_/L, rho, k, CT (propagate_d b) >>
    | _, _ => 
      << pc, rho, k, CT eUnbound >>
    end
  (* s_return *)
  | << pc, rho, RRet rho' :: k, CA a >> =>
    << pc, rho', k, CA a >>
  (* s_return_unwind *)
  | << pc, rho, RRet rho' :: k, CT e >> =>
    << pc, rho', k, CT e >>
  (* s_inx *)
  | << pc, rho, k, CR (TInx d x) >> =>
    match get rho x with
    | Some a =>
      << pc, rho, k, CA (V (VInx d a))@bot >>
    | _ =>
      << pc, rho, k, CT eUnbound >>
    end
  (* s_match *)
  | << pc, rho, k, CR (TMatch x x' t1 t2) >> =>
    match get rho x with
    | Some (V (VInx DLeft a), l) =>
      << pc\_/l, (x',a) :: rho, RRet rho :: k, CR t1 >>
    | Some (V (VInx DRight a), l) =>
      << pc\_/l, (x',a) :: rho, RRet rho :: k, CR t2 >>
    | Some (V _, l) =>
      << pc\_/l, rho, k, CT eType >>
    | Some (D e, l) =>
      << pc\_/l, rho, k, CT e >>
    | _ =>
      << pc, rho, k, CT eUnbound >>
    end
  (* s_tag *)
  | << pc, rho, k, CR (TTag x) >> =>
    match get rho x with
    | Some (b,l) =>
      << pc\_/l, rho, k, result_to_rcfg (tag_res b) >>
    | _ =>
      << pc, rho, k, CT eUnbound >>
    end
  (* s_bop *)
  | << pc, rho, k, CR (TBOp bo x' x'') >> =>
    match get rho x', get rho x'' with
    | Some (b', l0'), Some (b'', l0'') =>
      << pc\_/l0' \_/ l0'', rho, k, result_to_rcfg (bop_res bo b' b'') >>
    | _, _ =>
      << pc, rho, k, CT eUnbound >>
    end
  (* s_bracket_start *)
  | << pc, rho, k, CR (TBracket x t) >> =>
    match get rho x with
    | Some ((V (VConst (CLab L)))@L') =>
      << pc\_/L', rho, RBrk L (pc\_/L') :: k, CR t >>
    | Some (b,L') => 
      << pc\_/L', rho, k, CT (propagate_d b) >>
    | None =>
      << pc, rho, k, CT eUnbound >>
    end
  (* s_bracket_end *)
  | << pc, rho, RBrk L' pc' :: k, CA b@L >> =>
    << pc', rho, k, CA (bracket_box (Suc b@L) pc (L' \_/ pc'))@L' >>
  | << pc, rho, RBrk L' pc' :: k, CT e >> =>
    << pc', rho, k, CA (bracket_box (Throw e) pc (L' \_/ pc'))@L' >>
  (* s_label_of *)
  | << pc, rho, k, CR (TLabelOf x) >> =>
    match get rho x with
    | Some (_,l) =>
      << pc, rho, k, CA (V (VConst (CLab l)))@bot >>
    | _ =>
      << pc, rho, k, CT eUnbound >>
    end
  (* s_get_pc *)
  | << pc, rho, k, CR TGetPc >> =>
    << pc, rho, k, CA (V (VConst (CLab pc)))@bot >>
  (* s_throw *)
  | << pc, rho, k, CR (TThrow x) >> =>
    match get rho x with
    | Some (b,l) =>
      << pc\_/l, rho, k, CT (throw_excp b) >>
    | _ =>
      << pc, rho, k, CT eUnbound >>
    end
  (* s_catch *)
  | << pc, rho, k, CR (TCatch t x t') >> =>
    << pc, rho, RCatch x t' :: k, CR t >>
  (* s_catch_no_excp *)
  | << pc, rho, RCatch x t' :: k, CA a >> =>
    << pc, rho, k, CA a >>
  (* s_catch_excp *)
  | << pc, rho, RCatch x t' :: k, CT e >> =>
    << pc, (x,((V (vExcp e))@bot)) :: rho, RRet rho :: k, CR t' >>
  (* s_to_sum *)
  | << pc, rho, k, CR (TToSum x) >> =>
    match get rho x with
    | Some (b,l) =>
      << pc, rho, k, CA (to_sum_box b)@l >>
    | _ =>
      << pc, rho, k, CT eUnbound >>
    end
  (* stack underflow (you're already done?) *)
  | << pc, rho, nil, CA _ >> =>
      << pc, rho, nil, CT eStack >>
  | << pc, rho, nil, CT e >> =>
      << pc, rho, nil, CT e >>
  (* terms not from this language *)
  (* s_mk_nav *)
  | << pc, rho, k, CR (TMkNav _) >> =>
      << pc, rho, k, CT eLanguage >>
  end.

Definition final (c : Cfg) : bool :=
  match c with
  | << pc, rho, nil, CA _ >> => true
  | << pc, rho, nil, CT _ >> => true
  | _ => false
  end.

Fixpoint nstep (n : nat) (cm : Cfg*nat) : Cfg*nat :=
  match n with
  | S n' =>
    match cm with
    | (c,m) => if final c then (c,m) else nstep n' (step c, m+1)
    end
  | O => cm
  end.

Definition mstep (n : nat) (t : Tm) : Cfg*nat :=
  nstep n (<< bot, nil, nil, CR t >>, 0).

Definition sstep (n : nat) (t : Tm) : option ((Result*Lab)*nat) :=
  match mstep n t with
  | (<< pc, rho, nil, CA a >>, m) => Some ((Suc a,pc),m) 
  | (<< pc, rho, nil, CT e >>, m) => Some ((Throw e,pc),m)
  | _ => None (* looping or need more steps *)
  end.
