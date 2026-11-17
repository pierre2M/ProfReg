/-
  PR-12 · `non_confusion_dettes`
  ==============================

  Couplage **AX-2 ↔ AX-3**, décisions 12.1 à 12.3 du 8 septembre 2026.

  LA SOURCE A CHANGÉ, ET C'EST LA PREMIÈRE CHOSE À DIRE
  -----------------------------------------------------
  Le graphe donnait pour source du contenu « votre article 321-5 ».
  **Le porteur a écarté cette source le 8 septembre 2026 : l'article
  321-5 est une proposition produite par une IA à partir du MRC.** Ce
  n'est pas une source, c'est une sortie du modèle ; l'invoquer aurait
  été un `[RAISONNEMENT AUTORÉFÉRENTIEL]`.

  PR-12 est donc refondé sur les **axiomes eux-mêmes**, qui ont des
  sources externes :

  · **AX-2** — Stépanoff, *Attachements*, La Découverte, 2024. Les
    obligations envers ce qu'on ne maîtrise pas sont héritées,
    renouvelées à chaque cycle, et **ne peuvent être soldées par aucun
    transfert, faute d'un créancier apte à en donner quittance**.

  · **AX-3** — Demonsant, Levillain, Hatchuel & Segrestin, « Pour une
    action climatique équitable : penser le sauvetage commun », *Revue
    française de gestion*, 2026. La charge d'un sauvetage se répartit
    selon la règle des **avaries communes**, sous quatre conditions
    (péril commun, sacrifice volontaire, intérêt commun, **résultat
    utile**) — les quatre de la fiche au set (Annexe §A.18.2).

  · **AX-9** — Machiavel, *Discours* I, 34-35. [D-10, 28/09/2026 — décision
    de porteur, option (c).] Le **terme du mandat** n'est plus une
    cinquième condition de l'avarie : c'est une condition de bonne
    formation **du mandat du décideur** — son autorité est bornée dans le
    temps, et ce terme est fixé par le porteur de la règle, non par le
    décideur. Elle porte sur **qui a décidé**, non sur **la perte** : elle
    relève du découplage décideur / répartiteur (NT-ARCH §4.2ter) et de AX-9.

  CE QUE PR-12 ÉNONCE — DÉCISION 12.2, SÉPARATION DE TYPES
  ---------------------------------------------------------
  Non pas une commutation, mais :

  > **Aucune transition ne convertit une obligation AX-2 en charge AX-3, ni
  > l'inverse ; toute écriture qui les mélange lève
  > `[CONFUSION DES DEUX DETTES]`.**

  La lecture par commutation a été écartée : l'argument central de AX-3
  est que *« la taxe carbone est un dispositif commutatif »* et que
  *« la règle d'avarie commune est construite pour briser cette
  commutation »*. Demander à un carré de commuter aurait exigé de
  distinguer ce carré du carré micro × macro — ce que personne n'avait
  fait.

  DÉCISION 12.3 — LE SIGNAL EST CALCULÉ
  --------------------------------------
  `[CONFUSION DES DEUX DETTES]` est **décidable sur l'écriture** dès
  lors que AX-2 et AX-3 sont deux types. §4 le démontre, et §5 montre —
  en réutilisant PR-21 — ce qu'un champ déclaré aurait coûté.

  `[RÉSERVE DE MODÈLE]` `Dette`, `Traitement` et `appliquer` sont mes
  structures — réserve du §2quinquies du graphe.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR21_ChampDouble`.
-/

import ProfReg.PR21_ChampDouble

namespace ProfRegPR12

open ProfRegPR21

/-! ## 1. Deux régimes, et le risque est symétrique

> « **AX-2** régit ce qui **ne peut pas** être soldé […] **AX-3** régit ce
> qui **doit** l'être […] **Le risque est symétrique.** Traiter la dette
> envers le milieu comme une avarie commune la rend soldable — c'est
> l'erreur que AX-2 nomme. Traiter une dépense de sauvetage comme une
> dette inextinguible : personne ne paie, aucun sauvetage n'a lieu. »
> — fiche AX-3, §« Avec AX-2 » -/

/-- Le régime d'une dette. `nonDeclare` est dans le type parce que le
    silence existe dans les registres réels — et qu'il ne vaut pas
    permission (patron PR-17). -/
inductive Regime where
  | A2          -- obligation non soldable : pas de créancier apte à donner quittance
  | A3          -- charge d'avarie : soldable, répartie une fois, close par un résultat utile
  | nonDeclare
  deriving DecidableEq, Repr

/-- Les **quatre** conditions de qualification d'une avarie commune
    (RFG p. 93), reprises telles quelles au set (Annexe §A.18.2). **Hors de
    ces quatre conditions, AX-3 ne dit rien.**
    [D-10, 28/09/2026] La cinquième condition du 8/09 (`termeDuMandat`) est
    retirée d'ici et devient le champ `mandatBorne` de `Dette` : elle ne
    qualifie pas la perte, elle borne le décideur (AX-9). -/
structure ConditionsAvarie where
  perilCommun        : Bool
  sacrificeVolontaire : Bool
  interetCommun      : Bool
  /-- « quelque chose a effectivement été sauvé — la répartition ne
      s'applique qu'à cette condition ». -/
  resultatUtile      : Bool
  deriving DecidableEq, Repr

def avarieQualifiee (c : ConditionsAvarie) : Bool :=
  c.perilCommun && c.sacrificeVolontaire && c.interetCommun
    && c.resultatUtile

structure Dette where
  regime     : Regime
  conditions : ConditionsAvarie
  montant    : Nat
  /-- [D-10, 28/09/2026] Le mandat du décideur du sacrifice est **borné
      dans le temps, et son terme est fixé par le porteur de la règle, non
      par le décideur** (AX-9 ; Machiavel, *Discours* I, 34-35). Condition de
      bonne formation du **mandat**, non de l'avarie. -/
  mandatBorne : Bool
  deriving Repr

/-! ## 2. Le traitement appliqué, et la séparation

Un traitement est ce que le registre **fait** d'une dette. Les deux
traitements existent, et chacun n'est licite que sur son régime. -/

inductive Traitement where
  /-- Répartir la charge entre les intéressés — le traitement AX-3. -/
  | repartir
  /-- Renouveler l'obligation au cycle suivant — le traitement AX-2. -/
  | renouveler
  deriving DecidableEq, Repr

/-- Le régime que **suppose** un traitement. C'est ce couple — régime
    déclaré, régime supposé — dont la divergence est la confusion. -/
def regimeSuppose : Traitement → Regime
  | Traitement.repartir   => Regime.A3
  | Traitement.renouveler => Regime.A2

/-- **La transition.** `none` = refusé.

    Trois refus, et ils n'ont pas la même raison : le régime n'est pas
    déclaré ; le traitement suppose l'autre régime (la confusion) ; ou
    la répartition est demandée sur une avarie non qualifiée. -/
def appliquer (d : Dette) (t : Traitement) : Option Dette :=
  match d.regime with
  | Regime.nonDeclare => none
  | Regime.A2 =>
      match t with
      | Traitement.renouveler => some d
      | Traitement.repartir   => none
  | Regime.A3 =>
      match t with
      | Traitement.repartir   => if avarieQualifiee d.conditions && d.mandatBorne then some d else none
      | Traitement.renouveler => none

/-! ## 3. PR-12 — aucune conversion, et l'erreur est symétrique -/

/-- **PR-12 (1).** Une obligation AX-2 ne se répartit pas. C'est
    l'interdiction que AX-2 nomme : la répartition suppose un créancier
    apte à donner quittance, et AX-2 pose qu'il n'y en a pas. -/
theorem l_obligation_A2_ne_se_repartit_pas (d : Dette) (h : d.regime = Regime.A2) :
    appliquer d Traitement.repartir = none := by
  unfold appliquer; rw [h]

/-- **PR-12 (2).** Et une charge d'avarie ne se renouvelle pas. C'est
    l'erreur symétrique : *« personne ne paie, aucun sauvetage n'a
    lieu »*. -/
theorem la_charge_A3_ne_se_renouvelle_pas (d : Dette) (h : d.regime = Regime.A3) :
    appliquer d Traitement.renouveler = none := by
  unfold appliquer; rw [h]

/-- **PR-12 (3) — les deux erreurs, réunies.** Le risque est
    symétrique, et le set le disait en prose : c'est ici un théorème.
    Aucune des deux conversions n'est admise. -/
theorem les_deux_erreurs_sont_symetriques (d₂ d₃ : Dette)
    (h₂ : d₂.regime = Regime.A2) (h₃ : d₃.regime = Regime.A3) :
    appliquer d₂ Traitement.repartir = none
  ∧ appliquer d₃ Traitement.renouveler = none :=
  ⟨l_obligation_A2_ne_se_repartit_pas d₂ h₂,
   la_charge_A3_ne_se_renouvelle_pas d₃ h₃⟩

/-- **PR-12 (4).** Le régime non déclaré ne vaut pas permission : aucun
    traitement n'est admis. Patron de `nonDeclare_ne_vaut_pas_permission`
    (PR-17). -/
theorem regime_non_declare_ne_vaut_pas_permission (d : Dette)
    (h : d.regime = Regime.nonDeclare) (t : Traitement) :
    appliquer d t = none := by
  unfold appliquer; rw [h]

/-- **PR-12 (5).** Réciproquement, tout traitement admis l'a été **sur
    le régime qu'il suppose**. Le régime se lit sur l'écriture, sans
    information extérieure. -/
theorem traitement_admis_suppose_son_regime (d d' : Dette) (t : Traitement)
    (h : appliquer d t = some d') : d.regime = regimeSuppose t := by
  unfold appliquer at h
  cases hr : d.regime with
  | nonDeclare => rw [hr] at h; simp at h
  | A2 =>
      cases t with
      | renouveler => rfl
      | repartir => rw [hr] at h; simp at h
  | A3 =>
      cases t with
      | repartir => rfl
      | renouveler => rw [hr] at h; simp at h

/-- **PR-12 (6) — la quatrième condition mord.** Une charge AX-3 dont le
    **résultat utile** fait défaut ne se répartit pas : *« la
    répartition ne s'applique qu'à cette condition »* (RFG p. 93).

    C'est la condition qui distingue une avarie d'une perte, et c'est
    elle qui interdit de répartir une dépense qui n'a rien sauvé. -/
theorem sans_resultat_utile_aucune_repartition (d : Dette)
    (h : d.regime = Regime.A3) (hr : d.conditions.resultatUtile = false) :
    appliquer d Traitement.repartir = none := by
  unfold appliquer avarieQualifiee
  rw [h, hr]
  simp

/-- **PR-12 (6 bis) — la condition du mandat mord.** [D-10, 28/09/2026]
    Une charge AX-3 **qualifiée** — les quatre conditions réunies — ne se
    répartit pas si le mandat du décideur n'est pas borné par un terme
    fixé par un autre que lui. C'est la place que l'option (c) donne à la
    cinquième condition du 8/09 : elle ne dit rien de la perte, elle dit
    qui pouvait décider, et jusqu'à quand (AX-9). -/
theorem sans_mandat_borne_aucune_repartition (d : Dette)
    (h : d.regime = Regime.A3) (hm : d.mandatBorne = false) :
    appliquer d Traitement.repartir = none := by
  unfold appliquer
  rw [h, hm]
  simp

/-! ## 4. Le signal se calcule — décision 12.3 -/

/-- **`[CONFUSION DES DEUX DETTES]`, calculé.** Le signal se lit sur le
    couple (régime déclaré, traitement appliqué), sans autre
    information. -/
def confusionDesDeuxDettes (d : Dette) (t : Traitement) : Bool :=
  match d.regime with
  | Regime.nonDeclare => false          -- silence : refus, pas confusion
  | r                 => !(r == regimeSuppose t)

/-- **PR-12 (7).** Le signal est **exactement** ce qui distingue un
    refus par confusion d'un traitement admis : sur un régime déclaré,
    le traitement est refusé si et seulement si le signal se lève ou
    l'avarie n'est pas qualifiée. On l'écrit sur les deux cas de
    confusion, qui sont les seuls que le signal nomme. -/
theorem le_signal_se_leve_exactement_sur_la_confusion (d : Dette) (t : Traitement)
    (h : d.regime ≠ Regime.nonDeclare) :
    appliquer d t = none ↔
      (confusionDesDeuxDettes d t = true
        ∨ (d.regime = Regime.A3 ∧ t = Traitement.repartir
            ∧ (avarieQualifiee d.conditions && d.mandatBorne) = false)) := by
  -- [B-10, 28/09/2026] Reformulé : l'ancien énoncé donnait quatre valeurs du
  -- signal, sans lien avec `appliquer`, alors que la docstring annonce le
  -- « si et seulement si ». C'est maintenant l'énoncé.
  cases hr : d.regime with
  | nonDeclare => exact absurd hr h
  | A2 => cases t <;> simp [appliquer, confusionDesDeuxDettes, regimeSuppose, hr]
  | A3 =>
    cases t with
    | renouveler => simp [appliquer, confusionDesDeuxDettes, regimeSuppose, hr]
    | repartir =>
      cases hq : (avarieQualifiee d.conditions && d.mandatBorne) <;>
        simp [appliquer, confusionDesDeuxDettes, regimeSuppose, hr, hq]

/-- **Et le signal ne se lève pas sur le silence.** Un régime non
    déclaré est **refusé**, mais ce n'est pas une confusion : ce sont
    deux défauts distincts, et les confondre serait rejouer à l'échelle
    du signal l'erreur que PR-12 interdit à l'échelle des dettes. -/
theorem le_silence_n_est_pas_une_confusion (d : Dette) (t : Traitement)
    (h : d.regime = Regime.nonDeclare) :
    confusionDesDeuxDettes d t = false ∧ appliquer d t = none := by
  constructor
  · unfold confusionDesDeuxDettes; rw [h]
  · exact regime_non_declare_ne_vaut_pas_permission d h t

/-! ## 5. Pourquoi le signal n'est pas un champ déclaré

Décision 12.3, et l'argument est **réutilisé** de PR-21, non réécrit —
comme PR-13 §5 et PR-22 avant lui. -/

def controleConfusion : Regime × Traitement → Bool :=
  fun p =>
    match p.1 with
    | Regime.nonDeclare => false
    | r                 => !(r == regimeSuppose p.2)

theorem controleConfusion_trie :
    controleConfusion (Regime.A2, Traitement.repartir) = true
  ∧ controleConfusion (Regime.A2, Traitement.renouveler) = false := by
  constructor <;> rfl

/-- **PR-12 (8).** Un champ `[CONFUSION DES DEUX DETTES]` **déclaré**
    doublerait un contrôle calculable et pourrait donc mentir.
    Instance directe de `champ_declare_peut_mentir` (PR-21) : la
    décision 12.3 est fondée sur un théorème compilé, non sur une
    préférence de forme. -/
theorem un_signal_declare_pourrait_mentir (x : Regime × Traitement) :
    ∃ f : Fiche (Regime × Traitement),
      f.donnees = x ∧ ¬ Coherente controleConfusion f :=
  champ_declare_peut_mentir controleConfusion x

/-- Et dans les deux sens — instance de `les_deux_mensonges_existent`. -/
theorem le_mensonge_irait_dans_les_deux_sens :
    (∃ f : Fiche (Regime × Traitement),
        f.declare = false ∧ controleConfusion f.donnees = true)
  ∧ (∃ f : Fiche (Regime × Traitement),
        f.declare = true ∧ controleConfusion f.donnees = false) :=
  les_deux_mensonges_existent controleConfusion
    (Regime.A2, Traitement.repartir) (Regime.A2, Traitement.renouveler) rfl rfl

/-! ## 6. Gardes -/

/-- **PR-12 ne dit pas quelle dette est de quel régime.** Deux dettes
    de régimes opposés sont l'une et l'autre traitables, chacune par le
    sien : le fichier porte sur la **séparation**, jamais sur la
    qualification. Celle-ci est une décision de porteur, et AX-3 en donne
    les quatre conditions (le mandat borné relevant d'AX-9, D-10). -/
theorem PR12_ne_qualifie_aucune_dette (c : ConditionsAvarie) (m : Nat)
    (h : avarieQualifiee c = true) :
    appliquer ⟨Regime.A2, c, m, true⟩ Traitement.renouveler ≠ none
  ∧ appliquer ⟨Regime.A3, c, m, true⟩ Traitement.repartir ≠ none := by
  constructor
  · intro hc; simp [appliquer] at hc
  · intro hc; unfold appliquer at hc; simp [h] at hc

/-- **PR-12 ne juge pas le péril, ni le montant.** Le montant n'entre
    dans aucune condition : deux dettes de même régime et de montants
    différents se comportent identiquement. -/
theorem PR12_ne_juge_pas_le_montant (c : ConditionsAvarie) (m₁ m₂ : Nat)
    (b : Bool) (t : Traitement) :
    (appliquer ⟨Regime.A2, c, m₁, b⟩ t).isSome
      = (appliquer ⟨Regime.A2, c, m₂, b⟩ t).isSome := by
  cases t <;> rfl

/-- **PR-12 ne hiérarchise pas les deux régimes.** Chacun refuse le
    traitement de l'autre, symétriquement : aucun n'est le cas normal
    dont l'autre serait l'exception. -/
theorem PR12_ne_hierarchise_pas (c : ConditionsAvarie) (m : Nat) (b : Bool) :
    appliquer ⟨Regime.A2, c, m, b⟩ Traitement.repartir
      = appliquer ⟨Regime.A3, c, m, b⟩ Traitement.renouveler := rfl

/-- **Un traitement admis laisse la dette inchangée.** *Portée visée — déclarée, non établie par l'énoncé :* PR-12 ne prouve
    aucune commutativité, et n'en réfute aucune. Le
    fichier ne compose aucun carré : la lecture par commutation, écartée
    par la décision 12.2, n'est pas *réfutée* ici — elle est *hors
    sujet*. Sans cette garde, PR-12 se lirait comme un argument contre
    le nœud D, ce qu'il n'est pas. -/
-- [B-10, 28/09/2026 — RENOMMÉ, ex-`PR12_ne_compose_aucun_carre`] L'énoncé : un traitement admis rend la dette inchangée. Il ne porte sur aucun carré ; il révèle que « répartir » ne transforme rien dans le modèle.
theorem traitement_admis_laisse_la_dette_inchangee (d d' : Dette) (t : Traitement)
    (h : appliquer d t = some d') : d' = d := by
  unfold appliquer at h
  cases hr : d.regime with
  | nonDeclare => rw [hr] at h; simp at h
  | A2 =>
      cases t with
      | renouveler => rw [hr] at h; exact (Option.some.inj h).symm
      | repartir => rw [hr] at h; simp at h
  | A3 =>
      cases t with
      | repartir =>
          rw [hr] at h
          by_cases hq : (avarieQualifiee d.conditions && d.mandatBorne) = true
          · rw [if_pos hq] at h; exact (Option.some.inj h).symm
          · rw [if_neg hq] at h; simp at h
      | renouveler => rw [hr] at h; simp at h

/-- **Témoin discriminant direct** (R-7, 28/09/2026) de la lecture
    `le_silence_n_est_pas_une_confusion` : sur un régime déclaré mal appliqué
    (AX-2 que l'on répartit), `confusionDesDeuxDettes` rend l'**autre** valeur,
    `true`. Remplace le témoin indirect par caractérisation (table R-7, n° 13). -/
theorem confusion_temoin_discriminant (c : ConditionsAvarie) (m : Nat) (b : Bool) :
    confusionDesDeuxDettes ⟨Regime.A2, c, m, b⟩ Traitement.repartir = true := rfl

end ProfRegPR12
