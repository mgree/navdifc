Require Import Terms.
Require Import LBracketSyntax.
Require Import LBracketBigStep.

(** * Continuations and partial configurations *)

Inductive Frame : Type :=
| RLet : Var -> Tm -> Frame
| RRet : Env -> Frame
| RBrk : Lab -> Lab -> Frame. (* final label + original pc *)

Definition Cont := list Frame.

Definition PCfg := prod (prod Lab Env) Cont.

Inductive RCfg : Type :=
| CR : Tm -> RCfg    (* term to be reduced *)
| CA : Atom -> RCfg.  (* return atom *)

Definition Cfg := prod PCfg RCfg.

Notation "v @ L" := (v,L) (at level 5).

Notation "<< pc , r , k , X >>" := (((pc, r), k), X) (at level 5).

(** * Small-step semantics defined as a function *)

Definition step (c : Cfg) : option Cfg :=
  match c with
  (* s_var *)
  | << pc, rho, k, CR (TVar x) >> =>
    match get rho x with
    | Some a => Some << pc, rho, k, CA a >>
    | None => None  (* this won't happen on closed programs *)
    end
  (* s_const *)
  | << pc, rho, k, CR (TConst c) >> =>
    Some << pc, rho, k, CA ((VConst c)@bot)>>
  (* s_let_start *)
  | << pc, rho, k, CR (TLet x t1 t2) >> =>
    Some << pc, rho, RLet x t2 :: k, CR t1 >>
  (* s_let_bind *)
  | << pc, rho, RLet x t :: k, CA a >> =>
    Some << pc, (x,a) :: rho, RRet rho :: k, CR t >>
  (* s_abs *)
  | << pc, rho, k, CR (TAbs x t) >> =>
    Some << pc, rho, k, CA ((VClos rho x t)@bot) >>
  (* s_app_call *)
  | << pc, rho, k, CR (TApp x1 x2) >> =>
    match get rho x1, get rho x2 with
    | Some ((VClos rho' x t)@L), Some a =>
      Some << pc\_/L, (x,a) :: rho', RRet rho :: k, CR t >>
    | _, _ => None
    end
  (* s_return *)
  | << pc, rho, RRet rho' :: k, CA a >> =>
    Some << pc, rho', k, CA a >>
  (* s_inx *)
  | << pc, rho, k, CR (TInx d x) >> =>
    match get rho x with
    | Some a =>
      Some << pc, rho, k, CA (VInx d a)@bot >>
    | _ => None
    end
  (* s_match *)
  | << pc, rho, k, CR (TMatch x x' t1 t2) >> =>
    match get rho x with
    | Some (VInx DLeft a, l) =>
      Some << pc\_/l, (x',a) :: rho, RRet rho :: k, CR t1 >>
    | Some (VInx DRight a, l) =>
      Some << pc\_/l, (x',a) :: rho, RRet rho :: k, CR t2 >>
    | _ => None
    end
  (* s_tag *)
  | << pc, rho, k, CR (TTag x) >> =>
    match get rho x with
    | Some (v,l) => Some << pc, rho, k, CA (vTag (tag_of v), l) >>
    | _ => None
    end
  (* s_bop *)
  | << pc, rho, k, CR (TBOp b x' x'') >> =>
    match get rho x', get rho x'' with
    | Some (v', l0'), Some (v'', l0'') =>
      if mem eq_tag_dec (tag_of v') (tags_args b) &&
         mem eq_tag_dec (tag_of v'') (tags_args b) then
        Some << pc, rho, k, CA (do_bop b v' v'', l0' \_/ l0'') >>
      else None
    | _, _ => None
    end
  (* s_bracket_start *)
  | << pc, rho, k, CR (TBracket x t) >> =>
    match get rho x with
    | Some (VConst (CLab L))@L' =>
      Some << pc\_/L', rho, RBrk L (pc\_/L') :: k, CR t >>
    | _ => None
    end
  (* s_bracket_success *)
  | << pc, rho, RBrk L' pc' :: k, CA (b@L) >> =>
    if flows_dec (L \_/ pc) (L' \_/ pc') then
      Some << pc', rho, k, CA (b@L')>>
    else None
  (* s_label_of *)
  | << pc, rho, k, CR (TLabelOf x) >> =>
    match get rho x with
    | Some (v,l) => Some << pc, rho, k, CA (vLab l, bot) >>
    | _ => None
    end
  (* s_get_pc *)
  | << pc, rho, k, CR TGetPc >> =>
    Some << pc, rho, k, CA (vLab pc, bot) >>
  | _ => None
  end.

Definition OCfg := option Cfg.

(* unused *)
Definition final (c : OCfg) : bool :=
  match c with
  | None => true
  | Some << pc, rho, nil, CA _ >> => true
  | _ => false
  end.

Fixpoint nstep (n : nat) (ocm : OCfg * nat) : OCfg*nat :=
  match n with
  | S n' =>
    match ocm with
    | (oc,m) => 
      (* had to inline final here *)
      match oc with
      | None => (oc,m)
      | Some << pc, rho, nil, CA _ >> => (oc,m)
      | Some c => nstep n' (step c, m+1)
      end
    end
  | O => ocm
  end.

Definition mstep (n : nat) (t : Tm) : OCfg*nat :=
  nstep n (Some << bot, nil, nil, CR t >>, 0).

Definition sstep (n : nat) (t : Tm) : option ((option (Atom*Lab))*nat) :=
  match mstep n t with
  | (Some << pc, rho, nil, CA a >>, m) => Some (Some (a,pc),m)
  | (None, m) => Some (None, m)
  | _ => None (* looping or need more steps *)
  end.
