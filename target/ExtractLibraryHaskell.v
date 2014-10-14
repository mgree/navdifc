(* More information about Coq extraction here:
http://coq.inria.fr/refman/Reference-Manual027.html
and in the code in <your-coq-dir>/plugins/extraction *)

Add LoadPath "..".

Require Import Basic.
Require FourPoints.
Require Terms.

Extraction Language Haskell.

Extract Inductive unit => "()" [ "()" ].
Extract Inductive bool => "Prelude.Bool"
  [ "Prelude.True" "Prelude.False" ].

Extract Inductive nat =>
  "Prelude.Integer" [ "0" "(Prelude.+) 1" ] 
  "{- XXX if this appears you might want to optimize things -}
  (\fO fS n -> if (Prelude.==) n 0 then fO () else fS ((Prelude.-) n 1))".
Extract Constant Terms.eq_var_dec => "(Prelude.==)".
Extract Constant beq_nat => "(Prelude.==)".
Extract Constant max => "(\n m-> if (Prelude.<) n m then m else n)".
Extract Constant Peano.plus => "(Prelude.+)".
Extraction Inline Terms.eq_var_dec beq_nat Peano.plus.

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

(* The trick with instantiating Lab by FourPoints when extracting
didn't work any more; so I use an additional trick: adding "import
FourPoints" to the generated Label.hs and prefixing everything with
"FourPoints." below *)
Extract Constant Labels.Lab => "FourPoints.FP".
Extract Constant Labels.bot => "FourPoints.Low".
Extract Constant Labels.top => "FourPoints.High".
Extract Constant Labels.join => "FourPoints.fp_join".
Extract Constant Labels.flows_dec => "FourPoints.fp_flows".

(* Recursive Extraction Library can only take _one_ module/file so I
   created an dummy module called Everything *)
Require Everything.

(* Problem: lots of things get a coq_ / Coq_ prefix
Manual says:
  In case of name clash, identifiers are here renamed using prefixes
  coq_ or Coq_ to ensure a session-independent renaming.
Solved by renaming all constructors and types to respect Haskell
conventions. *)

Recursive Extraction Library Everything.
