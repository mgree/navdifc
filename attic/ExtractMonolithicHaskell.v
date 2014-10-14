Require Import FourPoints.
Require Import Terms.
Require Import LNaVSyntax.
Require Import LNaVSmallStep.
Require Import EncodeLNaVintoLThrow.

Extraction Language Haskell.

Extract Inductive unit => "()" [ "()" ].
Extract Inductive bool => "Prelude.Bool"
  [ "Prelude.True" "Prelude.False" ].

Extract Inductive nat =>
  "Prelude.Integer" [ "0" "(Prelude.+) 1" ] 
  "{- XXX if this appears you might want to optimize things -}
  (\fO fS n -> if (Prelude.==) n 0 then fO () else fS ((Prelude.-) n 1))".
Extract Constant eq_var_dec => "(Prelude.==)".
Extract Constant beq_nat => "(Prelude.==)".
Extract Constant max => "(\n m-> if (Prelude.<) n m then m else n)".
Extraction Inline eq_var_dec beq_nat.

Extract Inductive option => "Prelude.Maybe"
  ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sum => "Prelude.Either"
  ["Prelude.Left" "Prelude.Right"].
Extract Inductive sumbool => "Prelude.Bool"
  [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].

Extract Inductive prod => "(,)" [ "(,)" ].
Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".
Extraction Inline fst snd.

Extract Constant lab => FP.
Extract Constant bot => Low.
Extract Constant top => High.
Extract Constant join => fp_join.
Extract Constant flows_dec => fp_flows.

(* Extracting "top-level modules" doesn't work with "Extaction" 
Error: Extraction of file FourPoints.v as a module is asked.
Monolithic Extraction cannot deal with this situation.
Please extract some objects of this module or
use (Recursive) Extraction Library instead. *)

(* Extracting (non-top-level) modules with "Extaction" doesn't work
   for Haskell (does nothing) but it seems to work for OCaml
Module Mcrap.
Definition dumb := 42.
End Mcrap. *)

Extraction "Extracted.hs"
  FP fp_join fp_flows step final nstep mstep tstep sstep
  encode v_id t_true t_false beq_tm EType EBracket size_tm.
