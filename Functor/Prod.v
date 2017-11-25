From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Basic_Cons.Product.
From Categories Require Import Prod_Cat.Prod_Cat.

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
        FO := fun c => ((Prod_Func D HP) _o (F _o c, G _o c))%object;

        FA := fun a b (f : (a –≻ b)%morphism) =>
                (@FA (D × D) D (Prod_Func D HP)
                     ((F _o a, G _o a))%object
                     ((F _o b, G _o b))%object ((F _a f) , (G _a f)))%morphism
    |}.

  Next Obligation.
  Proof.
    rewrite F_id.
    rewrite F_id.
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
      product := pointwise_product; (* TODO *) 
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
            Trans := fun c => Prod_morph_ex ( HP (F _o c) (G _o c)) (H _o c)
                                         (Trans α1 c)
                                         (Trans α2 c)
        |})%object
    |}.

  Next Obligation.
  Proof.
    apply Prod_morph_com_1.
  Qed.

  Next Obligation.
  Proof.
    rewrite Prod_morph_com_1.
    reflexivity.  (* Qs: 1. When do I use apply and when rewrite?
                         2. Why did I need to use reflexivity? *) 
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

  From Categories Require Import Ext_Cons.Prod_Cat.Prod_Facts.
  
  Next Obligation.
    (* I want to use Product_after_tuple from Prod_Facts in the last
    import *)
    assert (Product_after_tuple).

  Qed.
End Product_Fun.
      
                 
