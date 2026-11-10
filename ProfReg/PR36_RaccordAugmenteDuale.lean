/-
  PR-36 · Raccord du registre comptable augmenté (N3) et de l'écriture duale (N2)
  ===============================================================================

  Porteur : Pierre Musseau. Écrit le 29 septembre 2026, sur décision D-ED-8.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR35_EcritureDuale` et
  `ProfReg.LotL2_PR2_PR14`.

  CE QUE LE PORTEUR VEUT DÉMONTRER (CR 2026-S09 ; message du 29/09)
  ------------------------------------------------------------------
  Une entreprise A qui prend une responsabilité envers une entité B
  « augmente » son journal comptable d'un registre de communalité (N3), et
  l'écriture qu'elle y porte envers B s'écrit en symétrique dans le registre
  de communalité de B (N2). Ce fichier compose les deux.

  CE QUI MANQUAIT
  ---------------
  L2 (`RegistreComptableAugmente`) porte sur des relations GLOBALES
  `Actor → Actor → V` : aucun registre n'y a de teneur. PR-35 donne un
  teneur aux registres, mais ne connaît pas la double tenue. Le raccord
  exige donc un registre augmenté INDEXÉ PAR SON TENEUR (§1), dont on montre
  qu'il est bien une instance de L2 (§2), avant de le composer avec PR-35 (§3).

  LE RÉSULTAT (§3, `raccord_augmente_duale`)
  -------------------------------------------
  Si le registre augmenté de A est cohérent (N3) et si le registre de
  communalité de A est en écriture duale avec celui de B (N2), alors toute
  contrepartie que le livre financier de A inscrit envers B se lit, en
  miroir et avec le rôle opposé, dans le registre de communalité de B.

  GARDES (§4)
  -----------
  · Sans cohérence de A, pas de raccord (`sans_coherence_pas_de_raccord`).
  · Sans écriture duale avec B, pas de raccord (`sans_duale_pas_de_raccord`).
  · Le raccord porte sur l'existence et le sens, jamais sur la valeur
    (`le_raccord_ne_porte_pas_la_valeur`).

  Identités `Nat` ; pour la passerelle vers L2, un encodage `enc : Entite →
  Actor` quelconque. Aucune comparaison de chaînes par `decide`.
-/

import ProfReg.PR35_EcritureDuale
import ProfReg.LotL2_PR2_PR14

namespace ProfRegPR36

open ProfRegPR35
open ProfRegPR20 (TypageIA miroirIA roleDeTypage)
open ProfRegLot (Actor CompatibleExtension RegistreComptableAugmente
  registre_augmente_coherent)

/-! ## 0. Lemmes d'égalité booléenne, sans `Classical.choice`

L'instance `LawfulBEq Nat` de la bibliothèque tire `Classical.choice` ;
on passe par `of_decide_eq_true` et `decide_eq_true`. -/

theorem nat_beq_refl (n : Nat) : (n == n) = true := decide_eq_true rfl

theorem nat_eq_of_beq {a b : Nat} (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

/-! ## 1. Le registre augmenté indexé par son teneur -/

/-- Le registre de `R` porte au moins une ligne envers `b`. -/
def aUneLigneVers {V : Type} (R : Registre V) (b : Entite) : Bool :=
  R.lignes.any (fun l => l.contrepartie == b)

/-- **Registre comptable augmenté, tenu par une entité.** Un livre
    financier et un registre de communalité, tenus par le même teneur. -/
structure RegistreAugmenteTenu (Vf Vc : Type) where
  fin : Registre Vf
  com : Registre Vc
  meme_teneur : fin.teneur = com.teneur

/-- **Cohérence (N3), indexée par le teneur** : pour chaque contrepartie,
    le livre financier et le registre de communalité s'accordent sur
    l'existence d'une inscription. C'est la propriété de
    `registre_augmente_coherent`, lue ligne du teneur. -/
def Coherent {Vf Vc : Type} (A : RegistreAugmenteTenu Vf Vc) : Prop :=
  ∀ b, aUneLigneVers A.fin b = aUneLigneVers A.com b

/-! ## 2. Passerelle : un registre augmenté tenu et cohérent EST une instance de L2 -/

/-- La relation « le teneur a inscrit envers `y` », lue dans un registre,
    transportée dans l'espace des acteurs de L2 par un encodage `enc`. -/
def versActeur {V : Type} (enc : Entite → Actor) (R : Registre V) (y : Actor) : Bool :=
  R.lignes.any (fun l => enc l.contrepartie == y)

theorem versActeur_de_ligne {V : Type} (enc : Entite → Actor) (R : Registre V)
    (y : Actor) :
    versActeur enc R y = true ↔ ∃ l ∈ R.lignes, enc l.contrepartie = y := by
  unfold versActeur
  rw [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, beq_iff_eq.mp h⟩
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, beq_iff_eq.mpr h⟩

theorem aUneLigneVers_iff {V : Type} (R : Registre V) (b : Entite) :
    aUneLigneVers R b = true ↔ ∃ l ∈ R.lignes, l.contrepartie = b := by
  unfold aUneLigneVers
  rw [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, nat_eq_of_beq h⟩
  · rintro ⟨l, hl, h⟩; refine ⟨l, hl, ?_⟩; rw [h]; exact nat_beq_refl b

/-- La cohérence par contrepartie se transporte dans l'espace des acteurs. -/
theorem coherent_vers_acteur {Vf Vc : Type} (A : RegistreAugmenteTenu Vf Vc)
    (h : Coherent A) (enc : Entite → Actor) (y : Actor) :
    versActeur enc A.fin y = versActeur enc A.com y := by
  have imp : ∀ {V W : Type} (R : Registre V) (S : Registre W),
      (∀ b, aUneLigneVers R b = true → aUneLigneVers S b = true) →
      versActeur enc R y = true → versActeur enc S y = true := by
    intro V W R S hRS hR
    obtain ⟨l, hl, he⟩ := (versActeur_de_ligne enc R y).mp hR
    have hb : aUneLigneVers R l.contrepartie = true :=
      (aUneLigneVers_iff R _).mpr ⟨l, hl, rfl⟩
    obtain ⟨m, hm, hmc⟩ := (aUneLigneVers_iff S _).mp (hRS _ hb)
    exact (versActeur_de_ligne enc S y).mpr ⟨m, hm, by rw [hmc]; exact he⟩
  have h1 := imp A.fin A.com (fun b hb => by rw [← h b]; exact hb)
  have h2 := imp A.com A.fin (fun b hb => by rw [h b]; exact hb)
  cases hf : versActeur enc A.fin y <;> cases hc : versActeur enc A.com y
  · rfl
  · rw [hf] at h2; exact absurd (h2 hc) (by simp)
  · rw [hc] at h1; exact absurd (h1 hf) (by simp)
  · rfl

/-- **L'instance L2.** Un registre augmenté tenu et cohérent engendre un
    `RegistreComptableAugmente` au sens de L2 : le socle est le lien
    « le teneur a inscrit envers `y` ». -/
def versL2 {Vf Vc : Type} (A : RegistreAugmenteTenu Vf Vc) (h : Coherent A)
    (enc : Entite → Actor) : RegistreComptableAugmente Bool Bool :=
  { socle     := fun x y => (x == enc A.fin.teneur) && versActeur enc A.fin y
  , pFin      := fun x y => (x == enc A.fin.teneur) && versActeur enc A.fin y
  , pCom      := fun x y => (x == enc A.fin.teneur) && versActeur enc A.com y
  , pleinFin  := true
  , pleinCom  := true
  , compatFin := fun _ _ => Iff.rfl
  , compatCom := fun x y => by
      show ((x == enc A.fin.teneur) && versActeur enc A.com y) = true
        ↔ ((x == enc A.fin.teneur) && versActeur enc A.fin y) = true
      rw [coherent_vers_acteur A h enc y] }

/-- Et donc `registre_augmente_coherent` (L2) s'applique au registre tenu,
    sans être réécrit. -/
theorem le_registre_tenu_satisfait_L2 {Vf Vc : Type} (A : RegistreAugmenteTenu Vf Vc)
    (h : Coherent A) (enc : Entite → Actor) :
    ∀ x y, (versL2 A h enc).pFin x y = true ↔ (versL2 A h enc).pCom x y = true :=
  registre_augmente_coherent (versL2 A h enc)

/-! ## 3. Le raccord (théorème 4 de la note de désambiguïsation) -/

/-- **PR-36 — raccord N3 ↔ N2.** Si le registre augmenté de A est cohérent
    et si le registre de communalité de A est en écriture duale avec celui
    de B, toute contrepartie inscrite au livre financier de A envers B se lit
    dans le registre de communalité de B : une ligne de A envers B y a son
    miroir, qui nomme A et porte le rôle opposé. -/
theorem raccord_augmente_duale {Vf Vc : Type}
    (A : RegistreAugmenteTenu Vf Vc) (RB : Registre Vc)
    (hA : Coherent A) (hD : EcritureDuale A.com RB)
    (l : Ligne Vf) (hl : l ∈ A.fin.lignes) (hlB : l.contrepartie = RB.teneur) :
    ∃ c ∈ A.com.lignes, c.contrepartie = RB.teneur ∧
      ∃ m ∈ RB.lignes, m.contrepartie = A.com.teneur
        ∧ roleDeTypage m.typage ≠ roleDeTypage c.typage := by
  have hf : aUneLigneVers A.fin RB.teneur = true :=
    (aUneLigneVers_iff _ _).mpr ⟨l, hl, hlB⟩
  obtain ⟨c, hc, hcB⟩ := (aUneLigneVers_iff _ _).mp (by rw [← hA]; exact hf)
  refine ⟨c, hc, hcB, ?_⟩
  -- `c` n'est pas dans l'écart, puisque l'écart est vide
  have hmir : aSonMiroir A.com RB c = true := by
    cases h : aSonMiroir A.com RB c with
    | true => rfl
    | false =>
      have hin : c ∈ ecart A.com RB := by
        unfold ecart lignesVers
        rw [List.mem_filter, List.mem_filter]
        refine ⟨⟨hc, ?_⟩, by rw [h]; rfl⟩
        rw [hcB]; exact nat_beq_refl _
      rw [hD.1] at hin; exact absurd hin (by simp)
  unfold aSonMiroir at hmir
  obtain ⟨m, hm, hem⟩ := List.any_eq_true.mp hmir
  obtain ⟨h1, h2⟩ := la_ligne_miroir_est_de_role_oppose A.com.teneur c m hem
  exact ⟨m, hm, h1, h2⟩

/-! ## 4. Gardes et témoins -/

def entreprise : Entite := 2
def partenaire : Entite := 3

/-- Témoin : A inscrit une responsabilité de 50 envers B dans son livre
    financier et dans son registre de communalité ; B l'inscrit en miroir. -/
def A_ok : RegistreAugmenteTenu Nat Nat :=
  ⟨⟨entreprise, [⟨partenaire, .Dplus, 50⟩]⟩, ⟨entreprise, [⟨partenaire, .Dplus, 50⟩]⟩, rfl⟩
def B_ok : Registre Nat := ⟨partenaire, [⟨entreprise, .Cplus, 50⟩]⟩

theorem raccord_temoin :
    Coherent A_ok ∧ EcritureDuale A_ok.com B_ok := by
  refine ⟨fun b => rfl, by decide⟩

/-- **Garde — sans cohérence de A, pas de raccord.** A inscrit envers B au
    financier mais pas en communalité : l'écriture duale entre les registres
    de communalité tient (vide), et pourtant rien ne se lit chez B. C'est
    ce qui rend la double tenue (N3) nécessaire au raccord. -/
def A_incoherent : RegistreAugmenteTenu Nat Nat :=
  ⟨⟨entreprise, [⟨partenaire, .Dplus, 50⟩]⟩, ⟨entreprise, []⟩, rfl⟩
def B_vide : Registre Nat := ⟨partenaire, []⟩

theorem sans_coherence_pas_de_raccord :
    ¬ Coherent A_incoherent ∧ EcritureDuale A_incoherent.com B_vide
    ∧ B_vide.lignes = [] := by
  refine ⟨fun h => ?_, by decide, rfl⟩
  have := h partenaire
  exact absurd this (by decide)

/-- **Garde — sans écriture duale, pas de raccord.** A est cohérent, B n'a
    rien inscrit : l'écart est inscrit, il n'est pas comblé par la
    cohérence de A. -/
theorem sans_duale_pas_de_raccord :
    Coherent A_ok ∧ ¬ EcritureDuale A_ok.com B_vide := by
  refine ⟨fun b => rfl, by decide⟩

/-- **Garde — le raccord ne porte pas la valeur.** A cohérent, écriture
    duale avec B, montants différents entre le livre financier de A (50),
    son registre de communalité (1 : « reconnu », CONV-10) et B (7). -/
def A_valeurs : RegistreAugmenteTenu Nat Nat :=
  ⟨⟨entreprise, [⟨partenaire, .Dplus, 50⟩]⟩, ⟨entreprise, [⟨partenaire, .Dplus, 1⟩]⟩, rfl⟩
def B_valeurs : Registre Nat := ⟨partenaire, [⟨entreprise, .Cplus, 7⟩]⟩

theorem le_raccord_ne_porte_pas_la_valeur :
    Coherent A_valeurs ∧ EcritureDuale A_valeurs.com B_valeurs
    ∧ ¬ Concordante A_valeurs.com B_valeurs := by
  refine ⟨fun b => rfl, by decide, by decide⟩

/-- `Coherent` discrimine (règle R-7). -/
theorem coherent_temoin_discriminant :
    Coherent A_ok ∧ ¬ Coherent A_incoherent :=
  ⟨raccord_temoin.1, sans_coherence_pas_de_raccord.1⟩

end ProfRegPR36
