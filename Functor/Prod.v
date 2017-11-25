From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Basic_Cons.Product.
From Categories Require Import Prod_Cat.Prod_Cat.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Facts.
  

Section Product_Fun.

  Context {C D : Category}.
  Context {F G : Func_Cat C D}. (* Note: For reasons that I don't
                                   understand, this is not $-\succ$,
                                   but some fancy $\minus\succ$ that
                                   has to be copy-pasted 
                                 OK: the - is in fact an en dash – (u2013)
                                 *)

  Hypothesis HP : Has_Products D.

  (** The pointwise product presheaf. *)
  Program Definition pointwise_product : Func_Cat C D :=
    {|
        FO := fun c => ((F _o c)%functor ⊠ (G _o c)%functor)%object;

        FA := (fun a b (f : a –≻ b) =>
                 (F _a f) ⊠ (G _a f))%morphism
    |}.

  Next Obligation.
  Proof.
    rewrite !F_id.
    apply (F_id (Prod_Func D HP) ((F _o)%object c, ((G _o)%object c))).
  Qed.

  Next Obligation.
  Proof.
    rewrite !F_compose.
    apply (@F_compose _ _ (Prod_Func D HP)
                            (F _o a , G _o a)
                            (F _o b , G _o b)
                            (F _o c , G _o c)
                            ((F _a f, G _a f))
                            ((F _a g, G _a g)))%object%morphism.
  Qed.
    
  Program Definition Fun_Product : (F × G)%object :=
    {|
      product := pointwise_product; 
      Pi_1 :=
        {|
          Trans := fun c => Pi_1
        |};

      Pi_2 :=
        {|
          Trans := fun c => Pi_2
        |};

      Prod_morph_ex := fun H α1 α2 => 
        ({|
            Trans := fun c =>
                       << (Trans α1 c) , (Trans α2 c) >>                                               
        |})%morphism
    |}.

  Next Obligation.
  Proof.
    apply Prod_morph_com_1.
  Qed.

  Next Obligation.
  Proof.
    rewrite Prod_morph_com_1.
    reflexivity.  
  Qed.

  (* Now repeat for Pi_2. Would do in one fell swoop for arbitrary limits *)
  Next Obligation.
    apply Prod_morph_com_2.
  Qed.

  Next Obligation.
    rewrite Prod_morph_com_2.
    reflexivity.
  Qed.

  Next Obligation.
    apply ((Prod_morph_unique (HP (F _o c') (G _o c')) (H _o c) 
             ((Trans α1 c') ∘ (H _a h))
             ((Trans α2 c') ∘ (H _a h))
           )%object%morphism).
    + rewrite <- assoc .
      rewrite Prod_morph_com_1.
      reflexivity.
    (* Similarly for Pi_2: *)  
    + rewrite <- assoc .
      rewrite Prod_morph_com_2.
      reflexivity.
    + rewrite <- assoc .
      rewrite Prod_morph_com_1.
      rewrite assoc.
      rewrite Prod_morph_com_1.
      rewrite (Trans_com α1 h).
      reflexivity.
    (* Similarly for Pi_2: *)  
    + rewrite <- assoc .
      rewrite Prod_morph_com_2.
      rewrite assoc.
      rewrite Prod_morph_com_2.
      rewrite (Trans_com α2 h).
      reflexivity.
  Qed.

  Next Obligation.
    pose (Product_after_tuple (Trans α1 c)
                              (Trans α2 c)
                              (F _a h)
                              (G _a h)
         )%morphism as W.
    cbn in W.
    rewrite W.
    rewrite <- (Trans_com α1 h).
    rewrite <- (Trans_com α2 h).
    
    now rewrite (Product_precomposition
            (H _a h)
            (Trans α1 c')
            (Trans α2 c')
         )%morphism.
  Qed.

  Next Obligation.
    apply NatTrans_eq_simplify.
    extensionality x. cbn in *.
    rewrite Prod_morph_com_1.
    reflexivity.
  Qed.

  (* And similarly for Pi_2 *)
  Next Obligation.
    apply NatTrans_eq_simplify.
    extensionality x.
    cbn in *.
    rewrite Prod_morph_com_2.
    reflexivity.
  Qed.

  Next Obligation.
    apply NatTrans_eq_simplify.
    extensionality x.
    repeat match goal with
      [ H : _ = _ |- _ ] => apply (f_equal (fun y => Trans y x)) in H
    end.
    cbn in *.
    now apply (Prod_morph_unique _ _ (Trans r1 x)  (Trans r2 x)).
    (* YF: The goal is exactly an assumption. So the tactic "assumption" would have worked (instead of "rewrite H. reflexivity."). *)
    (* YF: now tactic. is the same as tactic; trivial. and trivial subsumes reflexivity and assumption *)
  Qed.
End Product_Fun.
      
                 
