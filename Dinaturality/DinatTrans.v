From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor.
From Categories Require Import NatTrans.Main.
From Categories Require Import Cat.Cat.
From Categories Require Import Prod_Cat.Main.
From Categories Require Import Essentials.AssocRewrite.

Section DinatTrans.
  Context {C D : Category}.

(**
Let C, D be categories and F : C x C^op -> D, G : C x C^op -> D be
functors. A dinatural transformation N : F -> G is a family of arrows
'Trans N' in the co-domain category (here D) indexed by objects of the
domain category (here C), Trans N c : F _o (c,c) -> G _o (c,c), such
that for all arrows h : c → c' in C, the following diagram must
commute (Trans_com):

#
<pre>

       F_o(id, h)            Trans N c              G_o(h,id)
     ————————————> F_o(c,c) ——————————> G _o (c,c) ————————————
    |                                                          |  
    |                                                          ∨
F _o (c,c')                                               G _o (c',c)
    |                                                          ∧
    |                                                           |
     ———————————>F _o(c',c')—————————> G _o(c',c') ——————————————
      F_o(h, id)            Trans N c'              G _o (id, h)
</pre>
#
Trans_com_sym is the symmetric form of Trans_com.
*)
  Record DinatTrans (F G : ((C × C^op)%category –≻ D)%functor) :=
    {
      Trans (c : C) : ((F _o (c,c)) –≻ (G _o (c,c)))%object%morphism;

      Trans_com {c c' : C} (h : (c –≻ c')%morphism) :
        (
          (G @_a (c',c') (c', c) (id, h)) ∘ (Trans c') ∘ (F @_a (c,c') (c',c') (h, id C c'))
          =
          (G @_a (c ,c ) (c', c) (h, id)) ∘ (Trans c ) ∘ (F  @_a (c,c') (c ,c ) (id, h))
        )%morphism%functor;

      Trans_com_sym {c c' : C} (h : (c –≻ c')%morphism) :
        (
          (G @_a (c ,c ) (c', c) (h, id)) ∘ (Trans c ) ∘ (F  @_a (c,c') (c ,c ) (id, h))
          =
          (G @_a (c',c') (c', c) (id, h)) ∘ (Trans c') ∘ (F @_a (c,c') (c',c') (h, id C c'))
        )%morphism%functor;
    }.

  Notation "F –≻ G" := (DinatTrans F G) : dinattrans_scope.

  (** Two natural transformations are equal if their arrow families are.
      That is, commutative diagrams are assumed to be equal by
      proof irrelevance. *)
  Lemma DinatTrans_eq_simplify {F G : ((C×C^op) –≻ D)%category%functor}
        (N N' : (F –≻ G)%dinattrans) : (@Trans _ _ N) = (@Trans _ _ N') -> N = N'.
  Proof.
    destruct N; destruct N'.
    basic_simpl.
    ElimEq.
    PIR; trivial.
  Qed.
 
End DinatTrans.

Arguments Trans {_ _ _ _} _ _.
Arguments Trans_com {_ _ _ _} _ {_ _} _.
Arguments Trans_com_sym {_ _ _ _} _ {_ _} _.

Bind Scope dinattrans_scope with DinatTrans.

Notation "F –≻ G" := (DinatTrans F G) : dinattrans_scope.

Local Open Scope dinattrans_scope.

Section DinatTrans_Compose.
  (** Dinatural transformations are not closed under composition, but they are closed under composition with natural transformations. **)
  
  Context {C D : Category}.
  
  (** . Graphically:
#
<pre>
                   F                                  F            
       ———————————————————————            ———————————————————————  
      |           ||          |          |           ||          | 
      |           ||N         |          |           ||N         | 
      |           ||          |          |           ||          | 
      |           \/          v          |           ||          v 
   C x C^op ———————————————–> D       C x C^op       ||          D 
      |                       ^          |           ||          ^ 
      |           ||          |          |           ||          | 
      |           ||N'        |          |           ||N'        | 
      |           ||          |          |           ||          | 
      |           \/          |          |           \/          | 
       ————————————————————————           ———————————————————————— 
                   H                                  H            
</pre>

 
Is dinatural whenever either N natural and N' dinatural or N natural
and N' dinatural
#

This kind of composition is sometimes also called vertical composition of
natural transformations.
*)
  Program Definition DinatTrans_Compose {F G H K : (C×C^op –≻ D)%functor}
          (din : DinatTrans G H)
          (nt1 : (F–≻ G)%nattrans) (nt2 : (H –≻ K)%nattrans) : (F –≻ K)%dinattrans :=
    {|
      Trans := fun c : Obj => ((NatTrans.Trans nt2 (c,c)) ∘ (Trans din c) ∘ (NatTrans.Trans nt1 (c,c)))%morphism
    |}.

  Next Obligation. (* Trans_com*)
  
  Proof.
    a_rewrite (NatTrans.Trans_com nt1).
    a_rewrite <- (NatTrans.Trans_com nt2).
    a_rewrite (Trans_com din h).
    a_rewrite (NatTrans.Trans_com nt2).
    now a_rewrite <- (NatTrans.Trans_com nt1).
  Qed.
  
  Next Obligation. (* Trans_com_sym *)
  Proof.
    symmetry.
    apply DinatTrans_Compose_obligation_1.
  Qed.

    Program Definition DinatTrans_Compose_Nat {F G H: (C×C^op –≻ D)%functor}
          (din : DinatTrans G H)
          (nt : (F–≻ G)%nattrans) : (F –≻ H)%dinattrans :=
    DinatTrans_Compose din nt (NatTrans_id _).

    Program Definition Nat_Compose_DinatTrans {G H K: (C×C^op –≻ D)%functor}
          
          (nt : (H –≻ K)%nattrans)  (din : DinatTrans G H): (G –≻ K)%dinattrans :=
    DinatTrans_Compose din (NatTrans_id _) nt.
End DinatTrans_Compose.


