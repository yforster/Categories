From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Prod_Cat.Main.

(** A presheaf on C is a functor Cᵒᵖ –≻ Type_Cat. *)
Definition Bimodule (C D : Category) := Functor (C × D^op)%category Type_Cat.

