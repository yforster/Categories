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

  ϕ' : forall {a b : Obj} {f : a –≻ b},
      f =≻ (f ∘ id) ;

  ρ : forall {a b : Obj} { f : a –≻ b },
      (id ∘ f) =≻ f;

  ρ': forall {a b : Obj} { f : a –≻ b },
      f =≻ (id ∘ f);

  α : forall {a b c d: Obj} {f : a –≻ b} {g : b –≻ c} {h : c –≻ d},
      (h ∘ (g ∘ f)) =≻ (h ∘ g) ∘ f;

  α' : forall {a b c d: Obj} {f : a –≻ b} {g : b –≻ c} {h : c –≻ d},
      (h ∘ g) ∘ f =≻ (h ∘ (g ∘ f));

  (** axioms **)
  vleft_unit  :
    forall {a b : Obj} {f g : a –≻ b} {η : f =≻ g},
      η • iid = η;

  vright_unit :
    forall {a b : Obj} {f g : a –≻ b} {η : f =≻ g},
      iid • η = η;

  vassoc :
    forall {a b : Obj} {f g h i : a –≻ b}
       {η : f =≻ g} {θ : g =≻ h} {ι : h =≻ i},
      (ι • (θ • η)) = (ι • θ) • η;
  
  whiskering_left_unit  :
    forall {a b c : Obj} {f : a –≻ b} {g : b –≻ c},
      (@iid b c g) ◃ f = iid;

  whiskering_right_unit :
    forall {a b c : Obj} {f : a –≻ b} {g : b –≻ c},
      g ▹ (@iid a b f) = iid;
  
  left_interchange :
    forall {a b c : Obj} {f : a –≻ b} {g h i : b –≻ c}
       {η : g =≻ h} {θ : h =≻ i},
      (θ ◃ f) • (η ◃ f) = (θ • η) ◃ f;

  right_interchange :
    forall {a b c : Obj} {f g h : a –≻ b} {i : b –≻ c}
       {η : f =≻ g} {θ : g =≻ h},
      (i ▹ θ) • (i ▹ η) = i ▹ (θ • η);

  (* if you are following the n-lab definition, they introduced the
  following mixed interchange later *)
  mixed_interchange :
    forall {a b c : Obj} {f g : a –≻ b} {h i : b –≻ c}
       {η : f =≻ g} {θ : h =≻ i},
      (i ▹ η) • (θ ◃ f) = (θ ◃ g) • (h ▹ η);
  
  left_unitor_nat  :
    forall {a b : Obj} {f g : a –≻ b} 
       {η : f =≻ g},
      ϕ • (η ◃ id) = (η • ϕ);

  right_unitor_nat :
    forall {a b : Obj} {f g : a –≻ b} 
       {η : f =≻ g},
      ρ • (id ▹ η) = (η • ρ);

  left_whisker_functoriality :
    forall {a b c d : Obj}
       {f : a –≻ b} {g : b –≻ c} {h i : c –≻ d}
       {η : h =≻ i},
      α • (η ◃ (g ∘ f)) = ((η ◃ g) ◃ f) • α;

  mixed_whisker_funcoriality:
    forall {a b c d : Obj}
       {f : a –≻ b} {g h: b –≻ c} {i : c –≻ d}
       {η : g =≻ h},
      α • (i ▹ (η ◃ f)) = ((i ▹ η) ◃ f) • α;
    
  right_whisker_functoriality:
    forall {a b c d : Obj}
       {f g : a –≻ b} {h: b –≻ c} {i : c –≻ d}
       {η : f =≻ g},
      ((i ∘ h) ▹ η) • α = α • (i ▹ (h ▹ η));

  (* if you are following the n-lab definition, mixed interchange used
  to be here. *)

  left_unitor_right_inverse :
    forall {a b : Obj} {f : a –≻ b},
      ϕ • ϕ' = (iid : f =≻ f);

  left_unitor_left_inverse  :
    forall {a b : Obj} {f : a –≻ b},
      ϕ' • ϕ  = (iid : f ∘ id =≻ f ∘ id);

  right_unitor_right_inverse:
    forall {a b : Obj} {f : a –≻ b},
      ρ • ρ' = (iid : f =≻ f);

  right_unitor_left_inverse :
    forall {a b : Obj} {f : a –≻ b},
      ρ' • ρ  = (iid : id ∘ f =≻ id ∘ f);

  assoc_right_inverse:
    forall {a b c d : Obj} {f : a –≻ b} {g : b –≻ c} {h : c –≻ d},
      α • α' = (iid : (h ∘ g) ∘ f =≻ (h ∘ g) ∘ f);

  assoc_leftt_inverse :
    forall {a b c d : Obj} {f : a –≻ b} {g : b –≻ c} {h : c –≻ d},
      α' • α = (iid : h ∘ (g ∘ f) =≻ h ∘ (g ∘ f));

  unitor_whisk_assoc:
    forall {a b c : Obj} {f : a –≻ b} {g : b –≻ c},
      (ϕ ◃ f) • α = g ▹ ρ;
  
  assoc_whisk_assoc:
    forall {a b c d e : Obj}
       {f : a –≻ b} {g : b –≻ c} {h : c –≻ d} {i : d –≻ e},
      ((α ◃ f) • α) • (i ▹ α) = (α • α
                                 : i ∘ h ∘ g ∘ f =≻ ((i ∘ h) ∘ g) ∘ f);
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

Notation "a –≻ b" := (Hom a b)     : bicategory_scope.
Notation "f =≻ g" := (Nat f g)     : bicategory_scope.
Notation "f ∘ g"  := (compose g f) : bicategory_scope.
Notation "θ • η"  := (vcompose η θ): bicategory_scope.
Notation "h ▹ η"  := (rwhisk h η)  : bicategory_scope.

Bind Scope bicategory_scope with Bicategory.

Coercion Obj : Bicategory >-> Sortclass.

