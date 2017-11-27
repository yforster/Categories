From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.
Require Import Setoid.

Local Open Scope morphism.

Ltac find_right G :=
  match G with
  | (?f ∘ ?g) => find_right g
  | ?f => constr:(f)
  end.
Ltac find_nth n G :=
  match n with
    0 => match G with ?h ∘ ?g => constr:(h) end
  | S ?n => match G with ?h ∘ ?g => find_nth n g end
  end.

Ltac rewrite_nth n :=
  match goal with
  | [ |- ?h = _ ] => let nth := find_nth n (h)
                   in rewrite <- (assoc _ _ nth)
  end.
Ltac rewrite_first := rewrite_nth 0.
Ltac rewrite2_nth n :=
  match goal with
  | [ |- ?h = _] => let nth := find_nth n h in
                  let r := find_right nth in
                  repeat rewrite (assoc r)
  end.
Ltac rewrite_second := rewrite2_nth 0.

Unset Ltac Debug.

Ltac a_rewrite_step n H :=
  tryif setoid_rewrite H then idtac else (rewrite_nth n; rewrite2_nth n; a_rewrite_step n H).

Ltac a_rewrite_first_step n H :=
  tryif setoid_rewrite H then idtac else tryif rewrite_nth n then (rewrite2_nth n; a_rewrite_step n H) else fail 1000 "rewrite failed".

Ltac a_rewrite_rec n H :=
  tryif a_rewrite_first_step n H then idtac else a_rewrite_rec (S n) H.

Tactic Notation "a_rewrite" open_constr(H) :=
  let x := fresh "E" in
  epose (x := H);
  repeat rewrite assoc in x;
  repeat rewrite assoc;
  a_rewrite_rec 0 x; clear x; repeat rewrite assoc.

Tactic Notation "a_rewrite" "<-" open_constr(H) :=
  let x := fresh "E" in
  epose (x := H);
  repeat rewrite assoc in x;
  symmetry in x;
  repeat rewrite assoc;
  a_rewrite_rec 0 x; clear x; repeat rewrite assoc.
