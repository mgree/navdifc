Inductive FP : Set :=
  Low | Med1 | Med2 | High.

Definition fp_join (l1 l2 : FP) : FP :=
  match l1, l2 with
  | High, _ => High
  | _, High => High
  | Med1, Med2 => High
  | Med2, Med1 => High
  | Med1, _ => Med1
  | Med2, _ => Med2
  | Low, _ => l2
  end.

Definition fp_flows (l1 l2 : FP) : bool :=
  match l1, l2 with
  | Low, _ => true
  | _, High => true
  | Med1, Med1 => true
  | Med2, Med2 => true
  | _, _ => false
  end.
