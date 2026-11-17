/-
  PR-21 · `champ_declare_peut_mentir`
  ===================================

  **La cinquième forme de sur-revendication** — celle qui n'est pas dans
  les preuves mais dans les **schémas de champs**.

  NT-ARCH §8ter recense quatre façons d'affirmer plus qu'on ne prouve,
  toutes situées dans l'écriture d'un théorème. La sonde du 8 septembre
  sur la grammaire P-C-E-D-e-d en a exhibé une cinquième, ailleurs :

  > **Un champ déclaré qui double un contrôle calculable peut diverger
  > de lui.**

  Le cas trouvé est le champ `respect_R1` de la sous-couche
  C-MOUVEMENT-TYPE.T (NT-ARCH §8.5) :

      respect_R1 | Booléen | VRAI / FAUX | Vérification que
      (typage_primitive, typage_miroir) appartient à la table des
      compatibilités miroir.

  Le champ **enregistre le résultat d'un contrôle que la machine peut
  faire**. Rien n'oblige alors l'enregistrement à dire la vérité du
  contrôle.

  CE QUE CE FICHIER FAIT, ET POURQUOI IL EST GÉNÉRAL
  --------------------------------------------------
  Le défaut ne tient pas à P-C-E-D-e-d. Il tient à la **forme** du
  schéma, et l'énoncé est donc écrit sans aucune référence à la
  grammaire : pour *tout* contrôle calculable et *toute* donnée, il
  existe une fiche qui ment. Le cas `respect_R1` en est l'instance
  (§4).

  CE QU'IL NE DIT PAS
  -------------------
  Il ne dit **pas** qu'un champ déclaré est en soi un défaut. Un champ
  dont le contenu n'est pas dérivable des autres — la source d'un
  seuil, le porteur d'une déclaration — est légitime et nécessaire :
  c'est même ce que le MRC exige partout ailleurs. Le défaut est le
  **doublement** d'un calcul, pas la déclaration.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR21

/-! ## 1. Le schéma en défaut

Une fiche porte des **données** et un **champ déclaré** censé
enregistrer le résultat d'un contrôle sur ces données. -/

structure Fiche (α : Type) where
  /-- Les champs dont le contrôle dépend. -/
  donnees : α
  /-- Le champ qui **double** le contrôle. -/
  declare : Bool

/-- La fiche est cohérente quand le champ déclaré dit ce que le contrôle
    calcule. -/
def Coherente {α : Type} (controle : α → Bool) (f : Fiche α) : Prop :=
  f.declare = controle f.donnees

instance {α : Type} (controle : α → Bool) (f : Fiche α) :
    Decidable (Coherente controle f) := by
  unfold Coherente; infer_instance

/-! ## 2. Le théorème -/

/-- **PR-21.** Pour **tout** contrôle calculable et **toute** donnée,
    il existe une fiche portant cette donnée dont le champ déclaré
    contredit le contrôle.

    Aucune hypothèse : ni sur le contrôle, ni sur les données. Le défaut
    est dans la forme du schéma. -/
theorem champ_declare_peut_mentir {α : Type} (controle : α → Bool) (x : α) :
    ∃ f : Fiche α, f.donnees = x ∧ ¬ Coherente controle f := by
  refine ⟨⟨x, !controle x⟩, rfl, ?_⟩
  unfold Coherente
  simp only
  cases controle x <;> simp

/-- **Et le mensonge va dans les deux sens.** Là où le contrôle dit
    « conforme », la fiche peut déclarer « non conforme » ; là où il dit
    « non conforme », elle peut déclarer « conforme ». Le champ est
    **indépendant** de ce qu'il prétend enregistrer.

    Les deux hypothèses ne sont pas décoratives : elles disent que le
    contrôle **trie** — sans quoi l'un des deux mensonges serait vide. -/
theorem les_deux_mensonges_existent {α : Type} (controle : α → Bool)
    (x y : α) (hx : controle x = true) (hy : controle y = false) :
    (∃ f : Fiche α, f.declare = false ∧ controle f.donnees = true)
  ∧ (∃ f : Fiche α, f.declare = true ∧ controle f.donnees = false) :=
  ⟨⟨⟨x, false⟩, rfl, hx⟩, ⟨⟨y, true⟩, rfl, hy⟩⟩

/-! ## 3. Ce que le champ ajoute, et qui est exactement le défaut

C'est la formulation que je retiens pour justifier la correction : le
champ **double l'espace des états**, et la moitié de ce qu'il ajoute est
incohérente. -/

/-- **Le champ ajoute un degré de liberté que les données ne
    contraignent pas.** Pour toute donnée il existe deux fiches
    distinctes la portant — l'une cohérente, l'autre non.

    Un schéma sans ce champ n'aurait pas cet état supplémentaire à
    contrôler : il n'y aurait rien à quoi mentir. **C'est l'argument de
    la suppression**, et il est ici démontré plutôt que plaidé. -/
theorem le_champ_ajoute_un_degre_de_liberte {α : Type}
    (controle : α → Bool) (x : α) :
    ∃ f g : Fiche α,
      f.donnees = x ∧ g.donnees = x ∧ f ≠ g
      ∧ Coherente controle f ∧ ¬ Coherente controle g := by
  refine ⟨⟨x, controle x⟩, ⟨x, !controle x⟩, rfl, rfl, ?_, rfl, ?_⟩
  · intro h
    have : controle x = !controle x := congrArg Fiche.declare h
    cases hc : controle x <;> rw [hc] at this <;> simp at this
  · unfold Coherente
    simp only
    cases controle x <;> simp

/-! ## 4. L'instance : `respect_R1` de la fiche F8

Une table de compatibilité miroir réduite à ce qui suffit — deux
lignes de §8.5.2, l'une admise et l'autre non. Le contrôle est
calculable ; le champ le double. -/

inductive TypageF8 where
  | Cplus | Dplus | Pplus | eNeutre
  deriving DecidableEq, Repr

/-- Deux couples de §8.5.2 : `C+ ↦ D+` est admis (« symétrie stricte ») ;
    `d ↦ P+` ne figure nulle part. -/
def controleR1 : TypageF8 × TypageF8 → Bool
  | (TypageF8.Cplus, TypageF8.Dplus)   => true
  | (TypageF8.Dplus, TypageF8.Cplus)   => true
  | (TypageF8.Pplus, TypageF8.Dplus)   => true
  | (TypageF8.Pplus, TypageF8.eNeutre) => true
  | _                                  => false

/-- **Le contrôle trie** — sans quoi l'instance serait vide. -/
theorem controleR1_trie :
    controleR1 (TypageF8.Cplus, TypageF8.Dplus) = true
  ∧ controleR1 (TypageF8.eNeutre, TypageF8.Pplus) = false := by decide

/-- **`respect_R1` peut mentir dans les deux sens.** Instance directe du
    §2 sur la table de F8. C'est ce qui justifie la correction du
    schéma : le champ devient un **contrôle calculé**, non un champ
    déclaré. -/
theorem respect_R1_peut_mentir :
    (∃ f : Fiche (TypageF8 × TypageF8),
        f.declare = true ∧ controleR1 f.donnees = false)
  ∧ (∃ f : Fiche (TypageF8 × TypageF8),
        f.declare = false ∧ controleR1 f.donnees = true) :=
  ⟨⟨⟨(TypageF8.eNeutre, TypageF8.Pplus), true⟩, rfl, by decide⟩,
   ⟨⟨(TypageF8.Cplus, TypageF8.Dplus), false⟩, rfl, by decide⟩⟩

/-! ## 5. La forme corrigée

Le schéma corrigé ne porte pas de champ : le respect de R1 est une
**propriété des données**, obtenue par calcul. Il n'y a plus d'état à
contredire. -/

def FicheCorrigee (α : Type) := α

def respectCalcule {α : Type} (controle : α → Bool) (d : FicheCorrigee α) : Bool :=
  controle d

/-! [C-3 — RETIRÉ LE 28/09/2026, décision du porteur] Le théorème
    `la_forme_corrigee_n_a_pas_de_degre_de_liberte` rendait son hypothèse
    en conclusion (`FicheCorrigee α := α`, la preuve était `h`) : forme 3
    pure, patron `PR24_ne_conclut_pas_P1` (A-8). Le contenu — **la forme
    corrigée ne porte pas de champ déclaré, donc pas de degré de liberté** —
    est dans la définition de `FicheCorrigee` elle-même ; il n'a pas de
    théorème. Garde de non-régression déclarée : ne pas réintroduire ce
    théorème sous un autre nom. -/

/-! ## 6. Gardes -/

/-- **PR-21 ne condamne pas les champs déclarés.** Un champ dont le
    contenu n'est **pas** dérivable des autres est légitime — c'est même
    ce que le MRC exige partout : la source d'un seuil, le porteur d'une
    déclaration, le régime d'une écriture. On le montre en exhibant un
    « contrôle » qui ignore les données : aucune fiche ne peut alors le
    contredire en fonction de ce qu'elle porte, et le champ garde son
    sens propre. -/
theorem PR21_ne_condamne_pas_les_champs_declares {α : Type} (x : α) :
    ∃ f : Fiche α, Coherente (fun _ => true) f ∧ f.donnees = x :=
  ⟨⟨x, true⟩, rfl, rfl⟩

/-- **PR-21 ne juge pas le contrôle.** Que le champ puisse mentir ne dit
    rien de la justesse de la table de compatibilité : le théorème du §2
    vaut pour **tout** contrôle, juste ou faux. -/
theorem PR21_ne_juge_pas_le_controle {α : Type} (c₁ c₂ : α → Bool) (x : α) :
    (∃ f : Fiche α, f.donnees = x ∧ ¬ Coherente c₁ f)
  ∧ (∃ f : Fiche α, f.donnees = x ∧ ¬ Coherente c₂ f) :=
  ⟨champ_declare_peut_mentir c₁ x, champ_declare_peut_mentir c₂ x⟩

/-- **PR-21 ne dit pas que la fiche ment.** Il dit qu'elle **peut**
    mentir : la fiche cohérente existe aussi, et c'est le cas
    ordinaire. Le défaut est une possibilité ouverte par le schéma, non
    un fait sur les inscriptions. -/
theorem PR21_ne_dit_pas_que_la_fiche_ment {α : Type}
    (controle : α → Bool) (x : α) :
    ∃ f : Fiche α, f.donnees = x ∧ Coherente controle f :=
  ⟨⟨x, controle x⟩, rfl, rfl⟩

end ProfRegPR21
