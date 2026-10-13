/-
  PR-13 · `non_equivalence_declaree`
  ==================================

  **Appui formel de CONV-12** (Annexe méthodologique §A.15.5), actée le
  8 septembre 2026 avec les décisions 13.1 à 13.4.

  D'OÙ VIENT CE NŒUD
  ------------------
  PR-13 a été retenu le 7 septembre **en substitution du nœud D** — la
  commutativité micro-macro CARE ↔ CENP, qui exigeait des *framed
  bicategories* hors Mathlib. L'argument principal du retrait est AX-3 :
  fermer le carré rendrait la répartition dérivable de l'agrégation, or
  c'est exactement le **recouplage** que AX-3 défait.

  L'ÉNONCÉ D'ORIGINE PORTAIT DEUX CHOSES DE NATURES DIFFÉRENTES
  -------------------------------------------------------------
  > « toute inscription mobilisant une obligation à deux niveaux
  >   distincts (entité / territoire) **déclare** le niveau de chacune
  >   et leur non-équivalence ; **aucune transition ne fusionne** deux
  >   obligations de niveaux différents. »

  **Décision 13.1** — la première moitié est une **obligation de
  déclaration** : elle ne se démontre pas, elle se déclare. Elle devient
  **CONV-12**. Motif de CONV-1 à CONV-4, CONV-9 et CONV-11 ; l'écrire
  comme théorème sous l'hypothèse « bien formée », sans témoins des deux
  côtés (NT-ARCH §8ter-bis, R-2), serait la **forme 3**
  de §8ter.

  **Décision 13.2, option A** — on déclare **les deux niveaux
  seulement**. La non-équivalence est un **contrôle calculé**, jamais un
  champ déclaré : deux niveaux sont non équivalents si et seulement si
  leurs valeurs diffèrent, et un champ qui doublerait ce calcul pourrait
  mentir. §5 le démontre en **réutilisant PR-21**, sans le réécrire.

  CE QUE CE FICHIER FAIT
  ----------------------
  Ce qui reste après la décision 13.1 : l'interdiction de fusion, qui se
  démontre — plus, sur le patron de PR-10 §7 et de PR-23, ce qui
  **motive** CONV-12 et ce qui la **borne**.

  · §3 L'INTERDICTION — aucune fusion entre niveaux distincts, et le
    niveau non déclaré ne vaut pas permission (patron PR-17).
  · §4 LE TROU ET LA MORSURE — aucun prédicat portant sur la charge ne
    contraint le niveau ; et **sans le niveau inscrit, l'interdiction
    elle-même est inapplicable**, deux situations de verdicts opposés
    étant indiscernables au registre.
  · §5 POURQUOI LA NON-ÉQUIVALENCE EST CALCULÉE — instance directe de
    `champ_declare_peut_mentir` (PR-21).

  `[RÉSERVE DE MODÈLE]` `ObligationN`, `fusionner` et `oublierNiveau`
  sont mes structures — réserve du §2quinquies du graphe.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR21_ChampDouble`.
-/

import ProfReg.PR21_ChampDouble

namespace ProfRegPR13

open ProfRegPR21

/-! ## 1. Le modèle

Deux niveaux, et une obligation qui déclare le sien — ou ne le déclare
pas. `none` **est** le cas que CONV-12 vient fermer ; il est donc dans
le type, sinon il n'y aurait rien à démontrer. -/

inductive Niveau where
  | entite
  | territoire
  deriving DecidableEq, Repr

structure ObligationN where
  /-- Le niveau déclaré. `none` = non déclaré — ce que CONV-12 interdit,
      et ce dont §4 montre le coût. -/
  niveau : Option Niveau
  /-- Ce que l'obligation porte. Aucun théorème ne le juge. -/
  charge : Nat
  deriving Repr

/-! ## 2. La non-équivalence est un contrôle, pas un champ

Décision 13.2, option A. Noter la valeur de retour : `Option Bool`. Le
contrôle **n'est pas évaluable** quand un niveau manque — il ne répond
pas « équivalentes », il ne répond pas. -/

def nonEquivalentes (o₁ o₂ : ObligationN) : Option Bool :=
  match o₁.niveau, o₂.niveau with
  | some n₁, some n₂ => some (!(n₁ == n₂))
  | _,       _       => none

/-- **Le contrôle est calculé, et il est total dès que les deux niveaux
    sont déclarés.** C'est ce que la décision 13.2 achète. -/
theorem la_non_equivalence_est_calculee (n₁ n₂ : Niveau) (c₁ c₂ : Nat) :
    nonEquivalentes ⟨some n₁, c₁⟩ ⟨some n₂, c₂⟩ = some (!(n₁ == n₂)) := rfl

/-- **Et il n'est pas évaluable sans les niveaux.** Le silence du
    registre ne se lit ni comme équivalence ni comme non-équivalence :
    il n'y a pas de verdict. Patron de `priorite_sans_assiette` (PR-23)
    et de `nonDeclare_ne_vaut_pas_permission` (PR-17). -/
theorem sans_niveau_declare_aucun_verdict (o : ObligationN) (c : Nat) :
    nonEquivalentes ⟨none, c⟩ o = none ∧ nonEquivalentes o ⟨none, c⟩ = none := by
  constructor
  · rfl
  · unfold nonEquivalentes; cases o.niveau <;> rfl

/-! ## 3. L'interdiction de fusion — la moitié qui se démontre

Contrainte de transition, du patron de `transition_valide` (V4) : les
interdictions sont encodées dans la définition, pas supposées. -/

/-- Fusionner deux obligations. `none` = refusé.

    **Deux refus, et ils n'ont pas la même raison** : les niveaux
    diffèrent (l'interdiction proprement dite), ou un niveau manque
    (le silence ne vaut pas permission). -/
def fusionner (o₁ o₂ : ObligationN) : Option ObligationN :=
  match o₁.niveau, o₂.niveau with
  | some n₁, some n₂ =>
      if n₁ = n₂ then some ⟨some n₁, o₁.charge + o₂.charge⟩ else none
  | _,       _       => none

/-- **PR-13 (1).** Aucune fusion entre niveaux distincts. C'est la
    seconde moitié de l'énoncé d'origine, et elle est vraie par
    construction de la transition. -/
theorem aucune_fusion_entre_niveaux_distincts (n₁ n₂ : Niveau) (c₁ c₂ : Nat)
    (h : n₁ ≠ n₂) :
    fusionner ⟨some n₁, c₁⟩ ⟨some n₂, c₂⟩ = none := by
  unfold fusionner
  simp only []
  rw [if_neg h]

/-- **PR-13 (2).** Un niveau non déclaré ne vaut pas permission de
    fusionner. Patron exact de `nonDeclare_ne_vaut_pas_permission`
    (PR-17) : le silence refuse, il n'autorise pas. -/
theorem niveau_non_declare_ne_vaut_pas_permission (c : Nat) (o : ObligationN) :
    fusionner ⟨none, c⟩ o = none := rfl

/-- Et des deux côtés, sans quoi l'interdiction aurait une porte. -/
theorem niveau_non_declare_a_droite_ne_vaut_pas_permission
    (o : ObligationN) (c : Nat) : fusionner o ⟨none, c⟩ = none := by
  unfold fusionner
  cases o.niveau <;> rfl

/-- **PR-13 (3).** Réciproquement, toute fusion admise l'a été **au même
    niveau, déclaré des deux côtés**. On lit le niveau sur le résultat,
    sans information extérieure — ce qui rend la transition contrôlable
    par un tiers. -/
theorem fusion_admise_seulement_au_meme_niveau
    (n₁ n₂ : Niveau) (c₁ c₂ : Nat) (o : ObligationN)
    (h : fusionner ⟨some n₁, c₁⟩ ⟨some n₂, c₂⟩ = some o) :
    n₁ = n₂ ∧ o.niveau = some n₁ := by
  unfold fusionner at h
  simp only [] at h
  by_cases hn : n₁ = n₂
  · rw [if_pos hn] at h
    exact ⟨hn, by rw [← Option.some.inj h]⟩
  · rw [if_neg hn] at h
    simp at h

/-! ## 4. Le trou, et la morsure

Ce qui **motive** CONV-12 plutôt que de la postuler. -/

/-- **PR-13 (4) — le trou, et il est général.** Aucune condition de
    bonne formation portant sur la **charge** ne contraint le niveau :
    pour tout prédicat sur la charge et toute charge qui le satisfait,
    il existe une obligation qui le satisfait et dont le niveau n'est
    pas déclaré.

    C'est plus fort que le patron de `BienFormee_ne_borne_pas_le_maintien`
    (PR-23), qui exhibait un seul cas : ici **aucun** prédicat de cette
    forme ne peut fermer le trou. Seule une obligation portant sur le
    niveau lui-même le ferme — c'est-à-dire CONV-12. -/
theorem aucun_predicat_sur_la_charge_ne_borne_le_niveau
    (P : Nat → Prop) (c : Nat) (h : P c) :
    ∃ o : ObligationN, o.charge = c ∧ P o.charge ∧ o.niveau = none :=
  ⟨⟨none, c⟩, rfl, h, rfl⟩

/-- Ce qu'un registre qui n'inscrirait pas le niveau donnerait à lire. -/
def oublierNiveau (o : ObligationN) : Nat := o.charge

/-- **PR-13 (5) — la morsure.** Sans le niveau inscrit, **l'interdiction
    de fusion est inapplicable** : il existe deux situations dont les
    images sont identiques une fois le niveau oublié, et dont les
    verdicts de fusion sont **opposés** — l'une admise, l'autre refusée.

    Ce n'est pas une perte de précision, c'est une
    **non-identifiabilité** : aucun tiers ne peut dire, sur la seule
    lecture des charges, si la fusion était licite. **C'est ce qui rend
    CONV-12 nécessaire et non ornementale**, et c'est le même résultat
    que `deux_dettes_distinctes_meme_ecriture` (PR-23) sur un autre
    objet. -/
theorem sans_le_niveau_l_interdiction_est_inapplicable :
    ∃ o₁ o₂ o₁' o₂' : ObligationN,
      oublierNiveau o₁ = oublierNiveau o₁'
      ∧ oublierNiveau o₂ = oublierNiveau o₂'
      ∧ fusionner o₁ o₂ ≠ none
      ∧ fusionner o₁' o₂' = none := by
  refine ⟨⟨some Niveau.entite, 1⟩, ⟨some Niveau.entite, 2⟩,
          ⟨some Niveau.entite, 1⟩, ⟨some Niveau.territoire, 2⟩,
          rfl, rfl, ?_, rfl⟩
  intro hcontra
  simp [fusionner] at hcontra

/-- **Et le niveau déclaré lève la non-identifiabilité.** Les deux
    situations du théorème précédent deviennent alors distinctes : c'est
    exactement ce que CONV-12 achète. -/
theorem le_niveau_declare_separe_les_situations :
    fusionner ⟨some Niveau.entite, 1⟩ ⟨some Niveau.entite, 2⟩
      ≠ fusionner ⟨some Niveau.entite, 1⟩ ⟨some Niveau.territoire, 2⟩ := by
  intro h
  simp [fusionner] at h

/-! ## 5. Pourquoi la non-équivalence est calculée et non déclarée

Décision 13.2, option A — et l'argument n'est pas réécrit : **PR-21 est
réutilisé**, comme PR-22 avait réutilisé PR-16. -/

/-- Le contrôle, sous la forme que PR-21 attend. -/
def controleNonEquivalence : Niveau × Niveau → Bool :=
  fun p => !(p.1 == p.2)

/-- **Le contrôle trie** — sans quoi l'instance serait vide. -/
theorem controleNonEquivalence_trie :
    controleNonEquivalence (Niveau.entite, Niveau.territoire) = true
  ∧ controleNonEquivalence (Niveau.entite, Niveau.entite) = false := by
  constructor <;> rfl

/-- **PR-13 (6).** Un champ « non-équivalence » **déclaré** doublerait
    un contrôle calculable, et pourrait donc mentir — pour toute paire
    de niveaux, il existe une fiche portant cette paire dont le champ
    contredit le contrôle.

    Ce n'est pas une analogie : c'est `champ_declare_peut_mentir`
    (PR-21), appliqué au couple de niveaux. **La décision 13.2 est ainsi
    fondée sur un théorème compilé, non sur une préférence de forme.** -/
theorem un_champ_non_equivalence_declare_pourrait_mentir (x : Niveau × Niveau) :
    ∃ f : Fiche (Niveau × Niveau),
      f.donnees = x ∧ ¬ Coherente controleNonEquivalence f :=
  champ_declare_peut_mentir controleNonEquivalence x

/-- **Et le mensonge irait dans les deux sens** — instance de
    `les_deux_mensonges_existent` sur les deux niveaux.
    [RENOMMÉ LE 12/10/2026 — ex-`le_mensonge_irait_dans_les_deux_sens`, nom court
    déjà porté par PR-12 (`ProfRegPR12`) : même énoncé, même preuve.] -/
theorem le_mensonge_sur_les_niveaux_irait_dans_les_deux_sens :
    (∃ f : Fiche (Niveau × Niveau),
        f.declare = false ∧ controleNonEquivalence f.donnees = true)
  ∧ (∃ f : Fiche (Niveau × Niveau),
        f.declare = true ∧ controleNonEquivalence f.donnees = false) :=
  les_deux_mensonges_existent controleNonEquivalence
    (Niveau.entite, Niveau.territoire) (Niveau.entite, Niveau.entite)
    rfl rfl

/-! ## 6. Gardes -/

/-- **PR-13 ne dit pas que les deux dettes sont bien décrites.** Deux
    obligations de charges quelconques au même niveau fusionnent : le
    fichier porte sur la **séparation des niveaux**, jamais sur la
    justesse de ce qu'ils contiennent. Le set le disait déjà en prose ;
    c'est ici un théorème.

    [C-9 — 28/09/2026] Renommé (ex-`PR13_ne_dit_pas_que_les_dettes_sont_bien_decrites`) :
    l'énoncé est une **lecture** de `fusionner` au même niveau, licite sous R-7 —
    témoin discriminant : `aucune_fusion_entre_niveaux_distincts` (autre valeur,
    `none`, pour deux niveaux distincts). -/
theorem la_fusion_au_meme_niveau_somme_les_charges (c₁ c₂ : Nat) :
    fusionner ⟨some Niveau.entite, c₁⟩ ⟨some Niveau.entite, c₂⟩
      = some ⟨some Niveau.entite, c₁ + c₂⟩ := rfl

/-- **PR-13 ne juge pas la pertinence des niveaux de référence.** Le
    contrôle est **symétrique** : il ne hiérarchise pas l'entité et le
    territoire, il constate qu'ils diffèrent. -/
theorem PR13_ne_hierarchise_pas_les_niveaux (n₁ n₂ : Niveau) (c₁ c₂ : Nat) :
    nonEquivalentes ⟨some n₁, c₁⟩ ⟨some n₂, c₂⟩
      = nonEquivalentes ⟨some n₂, c₂⟩ ⟨some n₁, c₁⟩ := by
  unfold nonEquivalentes
  simp only []
  cases n₁ <;> cases n₂ <;> rfl

/-- **PR-13 n'interdit pas d'avoir deux obligations au même niveau.**
    L'interdiction porte sur la **fusion entre niveaux distincts**, pas
    sur la coexistence. Sans cette garde, PR-13 se lirait comme une
    interdiction d'agréger, ce qu'il n'est pas. -/
theorem PR13_n_interdit_pas_le_meme_niveau (n : Niveau) (c₁ c₂ : Nat) :
    fusionner ⟨some n, c₁⟩ ⟨some n, c₂⟩ ≠ none := by
  simp [fusionner]

/-- **Une obligation d'entité et une obligation de territoire ne fusionnent pas**
    (instance de `aucune_fusion_entre_niveaux_distincts`). *Portée visée — déclarée, non établie par l'énoncé :* PR-13 ne remplace
    pas le nœud D. Il ne dit rien de la
    commutativité micro-macro : deux obligations de niveaux différents
    ne fusionnent pas, et le fichier n'en tire **aucune** conclusion sur
    la dérivabilité de l'une à partir de l'autre. C'est la garde qui
    empêche de lire la substitution comme une résolution. -/
-- [B-10, 28/09/2026 — RENOMMÉ, ex-`PR13_ne_remplace_pas_le_noeud_D`] Instance `rfl` de `aucune_fusion_entre_niveaux_distincts` ; le nœud D n'est pas dans l'énoncé.
theorem entite_et_territoire_ne_fusionnent_pas (c₁ c₂ : Nat) :
    fusionner ⟨some Niveau.entite, c₁⟩ ⟨some Niveau.territoire, c₂⟩ = none := rfl

end ProfRegPR13
