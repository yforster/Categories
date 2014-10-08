Require Import Category.Core.

Class Equalizer `(C : Category Obj Hom) {a b : Obj} (f g : Hom a b) (e : Obj) : Type :=
{
  equalizer_morph : Hom e a;

  equalizer_morph_com : f ∘ equalizer_morph = g ∘ equalizer_morph;

  equalizer_morph_ex (e' : Obj) (eqm : Hom e' a) : f ∘ eqm = g ∘ eqm → Hom e' e;

  equalizer_morph_ex_com (e' : Obj) (eqm : Hom e' a) (eqmc : f ∘ eqm = g ∘ eqm) :
    equalizer_morph ∘ (equalizer_morph_ex e' eqm eqmc) = eqm;

  equalizer_morph_unique (e' : Obj) (eqm : Hom e' a) (com : f ∘ eqm = g ∘ eqm) (u u' : Hom e' e) : equalizer_morph ∘ u = eqm → equalizer_morph ∘ u' = eqm → u = u'
}.

Theorem Equalizer_iso `{C : Category Obj Hom} {a b : Obj} (f g : Hom a b) (e1 e2 : Obj) : Equalizer C f g e1 → Equalizer C f g e2 → e1 ≡ e2.
Proof.
  intros [eqm eqmc eqmex eqmec eqmu] [eqm' eqmc' eqmex' eqmec' eqmu'].
  exists (eqmex' e1 eqm eqmc); exists (eqmex e2 eqm' eqmc'); [eapply eqmu | eapply eqmu']; eauto 1.
  rewrite <- assoc; rewrite eqmec; rewrite eqmec'; trivial.
  rewrite <- assoc; rewrite eqmec'; rewrite eqmec; trivial.
Qed.
