From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Basic_Cons.Product.

Section Product_Fun.

  Context {C D : Category}.
  Context {F G : Func_Cat C D}. (* Note: For reasons that I don't understand, this is not $-\succ$, but some fancy $\minus\succ$ that has to be copy-pasted *)

  Hypothesis HP : Has_Products D.

  (** The pointwise product presheaf. *)
  Program Definition pointwise_product : Func_Cat C D :=
    {|
        FO :=
      (* ; FA := *)
    |}.

  Program Definition Fun_Product : (F × G)%object :=
    {|
      product := (* TODO *) 
      (* ; Pi_1 := (* TODO *) ; *)
      (* Pi_2 := (* TODO *) ; *)
      (* Prod_morph_ex := *)
    |}.

End Product_Fun.
      
                 
