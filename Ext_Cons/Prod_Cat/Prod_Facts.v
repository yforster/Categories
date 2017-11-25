From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat.
From Categories Require Import Basic_Cons.Product.

Local Open Scope morphism_scope.
Local Open Scope object_scope.

Notation "a ⊠ b" := (×ᶠⁿᶜ _ _o (a,b))%functor
                              (at level 56, left associativity): object_scope.
Notation "f ⊠ g" := (×ᶠⁿᶜ _ @_a (_,_) (_,_) (f , g))%functor
                                                              (at level 56, left associativity): morphism_scope.
Notation "<< f , g >>" := (Prod_morph_ex _ _ f g) : morphism_scope.


Section Prod_Properties.
  Context {C : Category} {HP : Has_Products C}.
  
  Lemma Product_after_tuple : 
    forall {a b1 b2 c1 c2 : Obj}
      (f1 : a –≻ b1) 
      (f2 : a –≻ b2) 
      (g1 : b1 –≻ c1) 
      (g2 : b2 –≻ c2),
      (
        (g1 ⊠ g2) ∘ ( << f1 , f2 >> ) =
        << g1 ∘ f1 , g2 ∘ f2 >> 
      )%morphism.

  Proof.
    intros.
    eapply Prod_morph_unique.
    + rewrite <- assoc. cbn.
      now rewrite Prod_morph_com_1, assoc, Prod_morph_com_1.
    + rewrite <- assoc. cbn.
      now rewrite Prod_morph_com_2, assoc, Prod_morph_com_2.
    + now rewrite Prod_morph_com_1.
    + now rewrite Prod_morph_com_2.
  Qed.

  Lemma Product_precomposition : 
    forall {a b c1 c2 : Obj}
      (f  : a –≻ b)
      (g1 : b –≻ c1)
      (g2 : b –≻ c2),
      (
        << g1 , g2 >> ∘ f 
        =
        ( << g1 ∘ f, g2 ∘ f>>  :  _ –≻ (c1 ⊠ c2)%object)
      )%morphism.

  Proof.
    intros a b c1 c2 f g1 g2.
    eapply Prod_morph_unique.
    + now rewrite <- assoc, Prod_morph_com_1.
    + now rewrite <- assoc, Prod_morph_com_2.
    + now rewrite Prod_morph_com_1.
    + now rewrite Prod_morph_com_2.
  Qed.

End Prod_Properties.
