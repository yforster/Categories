From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Ext_Cons.Prod_Cat.Main.



(** The basic definition of a bicategory *)
Cumulative Class Bicategory : Type :=
{
  (** 0-cells *)
  Obj : Type;

  (** 1-cells *)
  Hom : Obj → Obj → Type
  where "a –≻ b" := (Hom a b);

  (** 2-cells **)
  Nat : forall {a b : Obj} (f g : a –≻ b), Type
  where "f =≻ g" := (Nat f g);

  (** 1-cell structure **)
  id : forall {a : Obj}, a –≻ a;
  compose : forall {a b c : Obj} (f : a –≻ b) (g : b –≻ c), a –≻ c
  where "g ∘ f" := (compose f g);

  (** 2-cell structure **)
  iid : forall {a b : Obj} {f : a –≻ b}, (f =≻ f);

  vcompose : forall {a b : Obj} {f g h : a –≻ b}
               (η : f =≻ g) (θ : g =≻ h),
               f =≻ h
  where "θ • η" := (vcompose η θ);
                 
  (** whiskering **)
  lwhisk : forall {a b c : Obj} {g h : b –≻ c}
             (f : a –≻ b) (η : g =≻ h),
             ( (g ∘ f) =≻ (h ∘ f)  )
  where "η ◃ f" := (lwhisk f η);

  rwhisk : forall {a b c : Obj} {f g : a –≻ b}
             (h : b –≻ c) (η : f =≻ g),
             ( (h ∘ f) =≻ (h ∘ g)  )
  where "h ▹ η" := (rwhisk h η);

  (** unitors **)
  ϕ : forall {a b : Obj} {f : a –≻ b},
      (f ∘ id) =≻ f;

  ρ : forall {a b : Obj} { f : a –≻ b },
      (id ∘ f) =≻ f;

  α : forall {a b c d: Obj} {f : a –≻ b} {g : b –≻ c} {h : c –≻ d},
        (h ∘ (g ∘ f)) =≻ (h ∘ g) ∘ f;

  (** axioms **)
  vleft_unit  : forall {a b : Obj} {f g : a –≻ b} {η : f =≻ g},
                   η • iid = η;

  vright_unit : forall {a b : Obj} {f g : a –≻ b} {η : f =≻ g},
                  iid • η = η;

  vassoc : forall {a b : Obj} {f g h i : a –≻ b}
             {η : f =≻ g} {θ : g =≻ h} {ι : h =≻ i},
             (ι • (θ • η)) = (ι • θ) • η;
  
  wleft_unit  : forall {a b c : Obj} {f : a –≻ b} {g : b –≻ c},
                 (@iid b c g) ◃ f = iid;

  wright_unit : forall {a b c : Obj} {f : a –≻ b} {g : b –≻ c},
                  g ▹ (@iid a b f) = iid;

  left_interchange : forall { a b c : Obj} {f : a –≻ b} { g h i : b –≻ c }
                        {η : g =≻ h} {θ : h =≻ i},
                       (θ ◃ f) • (η ◃ f) = (θ • η) ◃ f;

  right_interchange : forall { a b c : Obj} {f g h : a –≻ b} { i : b –≻ c }
                        {η : f =≻ g} {θ : g =≻ h},
                       (i ▹ θ) • (i ▹ η) = i ▹ (θ • η);

  
}.

Arguments Obj {_}, _.
Arguments Hom {_} _ _, _ _ _.
Arguments Nat {_} _ _, _ _ _.
Arguments id {_ _}, {_} _, _ _.
Arguments compose {_} {_ _ _} _ _, _ {_ _ _} _ _, _ _ _ _ _ _.
Arguments iid {_} {_ _} {_}, {_} _ _ _, _ _ _ _.
Arguments vcompose {_} {_ _} {_ _ _} _ _,
                    _  {_ _} {_ _ _} _ _,
                    _   _ _   _ _ _  _ _ .
Arguments lwhisk {_} {_ _ _} {_ _} _ _,
                  _  {_ _ _} {_ _} _ _,
                  _   _ _ _   _ _  _ _.
Arguments rwhisk {_} {_ _ _} {_ _} _ _,
                  _  {_ _ _} {_ _} _ _,
                  _   _ _ _   _ _  _ _.
Arguments ϕ {_} {_ _} {_},
             _  {_ _} {_},
             _   _ _   _.
Arguments ρ {_} {_ _} {_},
             _  {_ _} {_},
             _   _ _   _.
Arguments α {_} {_ _ _ _ } {_ _ _},
             _  {_ _ _ _ } {_ _ _},
             _   _ _ _ _    _ _ _.

Arguments assoc {_ _ _ _ _} _ _ _.
Arguments assoc_sym {_ _ _ _ _} _ _ _.

Notation "f ∘ g" := (compose g f) : morphism_scope.
Notation "a –≻ b" := (Hom a b) : morphism_scope.

Bind Scope category_scope with Category.

Bind Scope morphism_scope with Hom.

Bind Scope object_scope with Obj.

Coercion Obj : Category >-> Sortclass.

Hint Resolve id_unit_left id_unit_right.

(* basic tactics for categories *)

(** We can't write reveal_comp tactic more efficiently without a mechanism to match
with a pattern and get back also the matched term. This is currently impossible in Coq. *)
(**
#
<pre>
Ltac reveal_make_rightmost f term :=
  let rec RMR termx :=
      lazymatch termx with
        | (_ ∘ f)%morphism => apply (eq_refl termx)
        | (?A ∘ ?B)%morphism =>
          match type of $(RMR B)$ with
              _ = (?C ∘ f)%morphism =>
              exact (
                  eq_trans
                  (match $(RMR B)$ in _ = Y return termx = (A ∘ Y)%morphism with
                      eq_refl => eq_refl
                  end)
                    (assoc_sym f C A)
                )
          end
        | _ => fail
      end
  in
  RMR term.

Ltac reveal_make_leftmost f term :=
  let rec RML termx :=
      lazymatch termx with
        | (f ∘ _)%morphism => apply (eq_refl termx)
        | (?A ∘ ?B)%morphism =>
          match type of $(RML A)$ with
              _ = (f ∘ ?C)%morphism =>
              exact (
                  eq_trans
                  (match $(RML A)$ in _ = Y return termx = (Y ∘ B)%morphism with
                      eq_refl => eq_refl
                  end)
                    (assoc B C f)
                )
          end
        | _ => fail
      end
  in
  RML term.

Ltac reveal_prepare_equality_term f g A B term :=
  match type of $(reveal_make_rightmost f A)$ with
      _ = (?C ∘ f)%morphism =>
      match type of $(reveal_make_leftmost g B)$ with
          _ = (g ∘ ?D)%morphism =>
          exact (eq_trans
                   (match $(reveal_make_rightmost f A)$ in _ = X return term = (X ∘ _)%morphism with
                        eq_refl =>
                        match $(reveal_make_leftmost g B)$ in _ = Y return term = (_ ∘ Y)%morphism with
                            eq_refl => eq_refl
                        end
                    end)
                   (eq_trans
                       (assoc (g ∘ D) f C)
                       (match assoc_sym D g f in _ = Z return (C ∘ f ∘ g ∘ D = C ∘ Z)%morphism with
                            eq_refl => eq_refl
                        end)
                   )
                )
      end
  end
.

Ltac reveal_prepare_equality_term_left_explicit f g B term :=
  match type of $(reveal_make_leftmost g B)$ with
      _ = (g ∘ ?D)%morphism =>
      exact (eq_trans
               (
                 match $(reveal_make_leftmost g B)$ in _ = Y return term = (_ ∘ Y)%morphism with
                     eq_refl => eq_refl
                 end
               )
               (assoc_sym D g f)
            )
  end
.

Ltac reveal_prepare_equality_term_right_explicit f g A term :=
  match type of $(reveal_make_rightmost f A)$ with
      _ = (?C ∘ f)%morphism =>
      exact (eq_trans
               (
                 match $(reveal_make_rightmost f A)$ in _ = Y return term = (Y ∘ _)%morphism with
                     eq_refl => eq_refl
                 end
               )
               (assoc g f C)
            )
  end
.

Ltac reveal_comp_in_goal f g :=
  match goal with
    | [|- context[?term]] =>
      match term with
          context [f] =>
          match term with
              context [g] =>
              match term with
                | (f ∘ g)%morphism => idtac
                | (?A ∘ ?B)%morphism =>
                  match A with
                      context [f] =>
                      match B with
                          context [g] =>
                          rewrite $(reveal_prepare_equality_term f g A B term)$
                      end
                  end
                | (f ∘ ?B)%morphism =>
                  rewrite $(reveal_prepare_equality_term_left_explicit f g B term)$
                | (?A ∘ g)%morphism =>
                  rewrite $(reveal_prepare_equality_term_right_explicit f g A term)$
              end
          end
      end
    | _ => fail
  end.

Ltac reveal_comp_in_I f g I :=
  match type of I with
    | context[?term] =>
      match term with
          context [f] =>
          match term with
              context [g] =>
              match term with
                | (f ∘ g)%morphism => idtac
                | (?A ∘ ?B)%morphism =>
                  match A with
                      context [f] =>
                      match B with
                          context [g] =>
                          rewrite $(reveal_prepare_equality_term f g A B term)$ in I
                      end
                  end
                | (f ∘ ?B)%morphism =>
                  rewrite $(reveal_prepare_equality_term_left_explicit f g B term)$ in I
                | (?A ∘ g)%morphism =>
                  rewrite $(reveal_prepare_equality_term_right_explicit f g A term)$ in I
              end
          end
      end
    | _ => fail
  end.

Tactic Notation "reveal_comp" constr(f) constr(g) := reveal_comp_in_goal f g.

Tactic Notation "reveal_comp" constr(f) constr(g) "in" hyp(I) := reveal_comp_in_I f g I.

</pre>
#
 *)

Ltac simpl_ids :=
  let id_detected B :=
      let J := fresh "H" in
      cut (B = id); [intros J; rewrite J; clear J | trivial]
  in
  repeat(
      match goal with
        | [|- context[(?A ∘ id)%morphism] ] => rewrite id_unit_right
        | [|- context[(id ∘ ?A)%morphism] ] => rewrite id_unit_left
        | [|- (?A ∘ ?B)%morphism = ?A] => id_detected B
        | [|- (?A = ?A ∘ ?B) %morphism] => id_detected B
        | [|- (?B ∘ ?A = ?A)%morphism] => id_detected B
        | [|- (?A = ?B ∘ ?A)%morphism] => id_detected B
      end
    )
.

Ltac simpl_ids_in_I I :=
  repeat(
      match type of I with
        | context[(?A ∘ id)%morphism] => rewrite id_unit_right in I
        | context[(id ∘ ?A)%morphism] => rewrite id_unit_left in I
      end
    )
.

Tactic Notation "simpl_ids" := simpl_ids.

Tactic Notation "simpl_ids" "in" hyp(I) := simpl_ids_in_I I.

Hint Extern 1 => progress simpl_ids.

Hint Extern 3 => progress (dohyps (fun H => simpl_ids in H)).

Hint Extern 2 =>
match goal with
    [|- ?A = ?B :> Hom _ _ _] =>
    repeat rewrite assoc; trivial; fail
end.

Hint Extern 2 =>
match goal with
  [H : _ = _ :> Hom _ _ _ |- _ = _ :> Hom _ _ _] =>
  repeat rewrite assoc in H;
    repeat rewrite assoc;
    (idtac + symmetry); apply H
end.
