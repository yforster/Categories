From Categories Require Import Essentials.Notations.
(* From Categories Require Import Essentials.Types. *)
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.
From Categories Require Import Functor.

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

Ltac a_rewrite_step n tac x :=
  tryif tac x then idtac else (rewrite_nth n; rewrite2_nth n; a_rewrite_step n tac x).

Ltac a_rewrite_first_step n tac x :=
  tryif tac x then idtac else tryif rewrite_nth n then (rewrite2_nth n; a_rewrite_step n tac x) else fail 1 "rewrite failed".

Ltac a_rewrite_rec n tac x :=
  tryif a_rewrite_first_step n tac x then idtac else a_rewrite_rec (S n) tac x.
Tactic Notation "a_rewrite_rec" constr(n) tactic(tac) hyp(x) := a_rewrite_rec n tac x.

Ltac do_simpl :=
  repeat rewrite F_compose;  
  repeat rewrite F_id;
  simpl_ids; auto;
  repeat rewrite assoc.

Ltac do_simpl_in x :=
  cbn in x;
  repeat rewrite F_compose in x;
  repeat rewrite F_id in x;
  repeat rewrite assoc in x;
  simpl_ids in x.

Tactic Notation "a_rewrite'" open_constr(H) tactic(rewr)  :=
  let x := fresh "E" in
  epose (x := H);
  do_simpl_in x;
  do_simpl;
  rewr x; clear x; repeat rewrite assoc.

Ltac do_rewrite H := rewrite H.
                                     
Tactic Notation "a_rewrite" open_constr(H) :=
  match goal with
    | [ |- _ ∘ _ = _ ] => a_rewrite' H (fun x => a_rewrite_rec 0 (fun H => setoid_rewrite H) x)
    | [ |- _ = _ ∘ _ ] => symmetry; (a_rewrite' H (fun x => a_rewrite_rec 0 (fun H => setoid_rewrite H) x)); symmetry

    | _ => a_rewrite' H (fun H => setoid_rewrite H || rewrite H)
  end.

Tactic Notation "a_rewrite" open_constr(H) "in" hyp(H1) :=
  do_simpl_in H1; 
  match goal with
    | [ |- _ ∘ _ = _ ] => a_rewrite' H (fun x => a_rewrite_rec 0 (fun H => setoid_rewrite H in H1) x)
    | [ |- _ = _ ∘ _ ] => symmetry; (a_rewrite' H (fun x => a_rewrite_rec 0 (fun H => setoid_rewrite H in H1) x)); symmetry

    | _ => a_rewrite' H (fun H => setoid_rewrite H in H1 || rewrite H in H1)
  end.

Tactic Notation "a_rewrite" "<-" open_constr(H) "in" hyp(H1) :=
  do_simpl_in H1; 
  match goal with
    | [ |- _ ∘ _ = _ ] => a_rewrite' H (fun x => a_rewrite_rec 0 (fun H => setoid_rewrite <- H in H1) x)
    | [ |- _ = _ ∘ _ ] => symmetry; (a_rewrite' H (fun x => a_rewrite_rec 0 (fun H => setoid_rewrite <- H in H1) x)); symmetry

    | _ => a_rewrite' H (fun H => setoid_rewrite <- H in H1 || rewrite <- H in H1)
  end.

Tactic Notation "a_rewrite" "<-" open_constr(H) :=
  match goal with
    | [ |- _ ∘ _ = _ ] => a_rewrite' H (fun x => a_rewrite_rec 0 (fun H => setoid_rewrite <- H) x)
    | [ |- _ = _ ∘ _ ] => symmetry; (a_rewrite' H (fun x => a_rewrite_rec 0 (fun H => setoid_rewrite <- H) x)); symmetry

    | _ => a_rewrite' H (fun H => setoid_rewrite <- H || rewrite <- H)
  end.
