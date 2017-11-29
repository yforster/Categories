From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Basic_Cons.Equalizer.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Coq_Cats.Type_Cat.Equalizer.

Require Import Coq.Relations.Relations Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.ClassicalChoice Coq.Logic.ChoiceFacts.
Require Coq.Logic.ClassicalFacts.
Require Import Setoid.

Section CoEqualizer_using_normalizer.
  Context {A B : Type} (f g : A → B).

  Local Obligation Tactic := idtac.

  Definition CoEq_rel_base : relation B := fun x y => exists z, f z = x ∧ g z = y.

  Definition CoEq_rel : relation B := clos_refl_sym_trans _ CoEq_rel_base.

  Instance CoEq_rel_equiv : Equivalence CoEq_rel.
  Proof.
    repeat split.
    + exact (equiv_refl _ _ (clos_rst_is_equiv _ CoEq_rel_base)).
    + exact (equiv_sym _ _ (clos_rst_is_equiv _ CoEq_rel_base)).
    + exact (equiv_trans _ _ (clos_rst_is_equiv _ CoEq_rel_base)).
  Qed.

  Variable eta : B -> B.
  Hypothesis eta_rel : forall x y, CoEq_rel x y -> eta x = eta y.
  Hypothesis eta_inrel : forall x, CoEq_rel (eta x) x.

  Lemma eta_invol : forall x, eta (eta x) = eta x.
  Proof.
    intros. now eapply eta_rel.
  Qed.
  
  Definition CoEq_Type :=
    { x | eta x = x }.

  Program Definition Type_Cat_CoEq  : CoEqualizer Type_Cat f g :=
    {|
      equalizer := CoEq_Type
    |}.

  Next Obligation.
  Proof.  
    cbn in *.
    intros x.
    exists (eta x). eauto.
  Defined.

  Next Obligation.
  Proof.
    extensionality x. cbn.
    cbv. 
    eapply subset_eq_compat. eapply eta_rel.
    econstructor. now exists x.
  Qed.
    
    
  Next Obligation.
  Proof.
    intros T F H x. eapply F.
    destruct x. exact x.
  Defined.

  Next Obligation.
  Proof.
    intros T eqm H.
    unfold Type_Cat_CoEq_obligation_1, Type_Cat_CoEq_obligation_3.
    extensionality x.
    cbn in *.
    assert (CoEq_rel (eta x) x) by firstorder.
    eapply clos_rst_rstn1 in H0. induction H0.
    - now rewrite eta_invol.
    - destruct H0 as [H0 | H0]; pose H0 as HH; clearbody HH;
        destruct H0 as [ ? [] ].
      + subst.
        rewrite <- (equal_f H). 
        rewrite <- IHclos_refl_sym_trans_n1.
        erewrite eta_rel. reflexivity. symmetry. econstructor. eassumption.
      + subst.
        rewrite (equal_f H).
        rewrite <- IHclos_refl_sym_trans_n1.
        erewrite eta_rel. reflexivity. econstructor. eassumption.
  Qed.
  
  Next Obligation.
  Proof.
    intros T eqm H1 u u' H2 H3.
    destruct H3.
    extensionality x.
    destruct x.
    unfold Type_Cat_CoEq_obligation_1 in H2; cbn in *.
    apply equal_f with (x0 := x) in H2.
    match goal with
      [|- ?A = ?B] =>
      match type of H2 with
        ?C = ?D => cutrewrite (A = C); [cutrewrite (B = D)|]; trivial
      end
    end.
    {
      apply f_equal.
      eapply subset_eq_compat. congruence.
    }
    {
      apply f_equal.
      eapply subset_eq_compat. congruence.
    }
  Qed.

End CoEqualizer_using_normalizer.
