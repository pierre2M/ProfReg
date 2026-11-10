/-
  ProfReg — Lot L2 / PR-2 / PR-14
  --------------------------------
  Porteur : Pierre Musseau.  Révision du 7 septembre 2026, seconde passe.

  Écrit en Lean 4 pur, sans Mathlib.

  RÉVISIONS DE CETTE PASSE, sur arbitrage du porteur :
  * PR-2 : la notion de « lot d'écritures », introduite faute de mieux et
    trop large pour être vraie sur un livre réel, est remplacée par la
    PAIRE D'ÉCRITURES MIROIR — l'unité de R1 (NT-ARCH §3bis : « toute
    écriture a une écriture miroir, Côté A (DÉBIT) <-> Côté B (CRÉDIT) »).
  * PR-1 : le théorème qui portait ce nom sanctionnait l'OPPOSABILITÉ,
    alors que la spécification (Annexe méth., tableau PR) demande un champ
    source obligatoire, et que la sanction est réservée à PR-3
    (attribution). Il est renommé PR-14 opposabilite_exige_statut_declare
    et versé comme ÉNONCÉ NOUVEAU, soumis en amendement.
    Son site de sanction est la clause téléologique (instrument D3 de
    I.3.6 §6.5), non le seuil (D1).
  * Ajout : fraction_exhibe_sa_source, qui rend VRAI ce que le set
    affirme déjà — l'obligation de déclaration comme invariant de typage —
    et que le théorème creux supprimé n'établissait pas.
-/

namespace ProfRegLot

abbrev Actor := String

/- ═══════════════════════════════════════════════════════════════════════
   L2 — REGISTRE COMPTABLE AUGMENTÉ (N3) : un même fait, deux registres

   [D-ED-2, 29/09/2026] RENOMMÉ, ex-« écriture duale entre registres » (`EcritureDuale`,
   `ecriture_duale_*`). L'objet est la DOUBLE TENUE d'un même fait par un même
   ensemble de relations (registre financier + registre de communalité) : c'est
   le registre comptable AUGMENTÉ. « Écriture duale » est réservé, depuis D-ED-1,
   à l'écriture miroir ENTRE DEUX TENEURS (N2) — voir `PR35_EcritureDuale.lean`.
   Aucune preuve n'est modifiée ; seuls les noms changent.
   Réf. : `MRC/Note_Desambiguisation_Ecriture_Duale_2026-09-29.md`.
   ═══════════════════════════════════════════════════════════════════════ -/

def R1_actoriel (p0 : Actor → Actor → Bool) : Prop :=
  ∀ a b, p0 a b = true → p0 b a = true

def CompatibleExtension {V : Type} (plein : V)
    (p0 : Actor → Actor → Bool) (p1 : Actor → Actor → V) : Prop :=
  ∀ a b, p1 a b = plein ↔ p0 a b = true

theorem R1_preserved_under_base_change {V : Type} (plein : V)
    (p0 : Actor → Actor → Bool) (p1 : Actor → Actor → V)
    (h_compat : CompatibleExtension plein p0 p1)
    (h_R1 : R1_actoriel p0) :
    ∀ a b, p1 a b = plein → p1 b a = plein := by
  intro a b hab
  exact (h_compat b a).mpr (h_R1 a b ((h_compat a b).mp hab))

structure RegistreComptableAugmente (Vfin Vcom : Type) where
  socle     : Actor → Actor → Bool
  pFin      : Actor → Actor → Vfin
  pCom      : Actor → Actor → Vcom
  pleinFin  : Vfin
  pleinCom  : Vcom
  compatFin : CompatibleExtension pleinFin socle pFin
  compatCom : CompatibleExtension pleinCom socle pCom

variable {Vfin Vcom : Type}

theorem registre_augmente_preserve_R1 (e : RegistreComptableAugmente Vfin Vcom)
    (h_R1 : R1_actoriel e.socle) :
    (∀ a b, e.pFin a b = e.pleinFin → e.pFin b a = e.pleinFin)
    ∧ (∀ a b, e.pCom a b = e.pleinCom → e.pCom b a = e.pleinCom) :=
  ⟨R1_preserved_under_base_change e.pleinFin e.socle e.pFin e.compatFin h_R1,
   R1_preserved_under_base_change e.pleinCom e.socle e.pCom e.compatCom h_R1⟩

theorem registre_augmente_coherent (e : RegistreComptableAugmente Vfin Vcom) :
    ∀ a b, e.pFin a b = e.pleinFin ↔ e.pCom a b = e.pleinCom := by
  intro a b
  constructor
  · intro h; exact (e.compatCom a b).mpr ((e.compatFin a b).mp h)
  · intro h; exact (e.compatFin a b).mpr ((e.compatCom a b).mp h)

theorem registre_augmente_non_equivalence :
    ∃ (e : RegistreComptableAugmente Bool Nat) (a b c d : Actor),
      e.socle a b = true ∧ e.pFin a b = e.pleinFin ∧ e.pCom a b = e.pleinCom
      ∧ e.socle c d = false ∧ e.pFin c d ≠ e.pleinFin ∧ e.pCom c d ≠ e.pleinCom := by
  -- [B-9, 28/09/2026] Témoin refait : le socle était VIDE (forme 6). Le nouveau
  -- porte un lien (A, B), où les deux registres sont pleins, et une absence de
  -- lien (C, D), où ni l'un ni l'autre ne l'est — sur la même écriture.
  refine ⟨{ socle := fun x _ => x == "A"
          , pFin := fun x _ => x == "A"
          , pCom := fun x _ => if x == "A" then 1 else 0
          , pleinFin := true
          , pleinCom := 1
          , compatFin := fun _ _ => Iff.rfl
          , compatCom := by intro x _; by_cases hx : (x == "A") = true <;> simp [hx] },
         "A", "B", "C", "D", by decide, by decide, by decide, by decide, by decide, by decide⟩

/- ═══════════════════════════════════════════════════════════════════════
   PR-2 — regime_declared_per_ecriture, SUR LA PAIRE MIROIR
   ═══════════════════════════════════════════════════════════════════════

   Spécification (Annexe méthodologique, tableau PR) :
   « Aucune écriture R1 de fiche n'est inscriptible sans regimeobligation
     déclaré (typage par construction). »

   L'unité est l'ÉCRITURE R1, c'est-à-dire la paire Côté A / Côté B.
-/

inductive RegimeObligation where
  | actoriel   : RegimeObligation
  | systemique : RegimeObligation
  | hybride    : RegimeObligation
  deriving DecidableEq, Repr

/-- Un côté d'écriture. Le champ `regime` est obligatoire : c'est la partie
    « typage par construction » de PR-2, qui est une CONVENTION et non un
    théorème (voir CONV-3). -/
structure Cote where
  reference : String
  regime    : RegimeObligation
  deriving Repr

/-- L'écriture R1 : deux côtés portant la même référence — le DÉBIT et son
    miroir au CRÉDIT (NT-ARCH §3bis). -/
structure PaireR1 where
  coteA  : Cote
  coteB  : Cote
  miroir : coteA.reference = coteB.reference

/-- Une paire est homogène quand ses deux côtés déclarent le même régime
    d'obligation. Extension naturelle de la vérification `respect_R1`, qui
    contrôle déjà la compatibilité du couple (typage, miroir). -/
def PaireHomogene (p : PaireR1) : Prop :=
  p.coteA.regime = p.coteB.regime

/-- **PR-2 — pas de glissement de régime à l'intérieur d'une écriture.**
    Les deux côtés d'une même écriture ne peuvent pas relever, l'un du
    régime actoriel, l'autre du régime systémique. L'interdiction est
    encodée comme `False` littéral (règle de travail n°6 du projet). -/
theorem regime_declared_per_ecriture (p : PaireR1) (h : PaireHomogene p)
    (h_act : p.coteA.regime = RegimeObligation.actoriel)
    (h_sys : p.coteB.regime = RegimeObligation.systemique) : False := by
  have heq : p.coteA.regime = p.coteB.regime := h
  rw [h_act, h_sys] at heq
  exact RegimeObligation.noConfusion heq

/-- Corollaire opératoire : un DÉBIT actoriel interdit un CRÉDIT systémique
    sur la même écriture. -/
theorem debit_actoriel_exclut_credit_systemique (p : PaireR1)
    (h : PaireHomogene p) (h_act : p.coteA.regime = RegimeObligation.actoriel) :
    p.coteB.regime ≠ RegimeObligation.systemique := by
  intro h_sys
  exact regime_declared_per_ecriture p h h_act h_sys

/-- Une transformation qui ne touche pas au régime le préserve —
    patron de `V4c_regime_unchanged`. -/
def retiqueter (c : Cote) (r : String) : Cote :=
  { c with reference := r }

-- [C-10 — 28/09/2026] Forme 1 déclarée : invariance d'un champ que `retiqueter`
-- ne touche pas (`{ c with reference := r }`). Illustration du patron, jamais appui.
theorem retiqueter_regime_unchanged (c : Cote) (r : String) :
    (retiqueter c r).regime = c.regime := rfl

/- ═══════════════════════════════════════════════════════════════════════
   RÉPARATION — fractionactorielle comme invariant de typage
   ═══════════════════════════════════════════════════════════════════════

   Le set (NT-ARCH §52, correction C1) affirme que l'obligation de
   déclarer `fractionactorielle` est « établie comme invariant de typage
   (fractionactorielle_must_be_declared) ». Or le théorème portant ce nom
   avait `True` pour conclusion : il n'établissait rien.

   Ce qui suit rend l'affirmation du set VRAIE, au lieu de la retirer :
   le type ne comporte aucun constructeur « calculée ».
-/

/-- Une fraction actorielle n'existe que déclarée : source et valeur, sans
    constructeur de calcul. La non-calculabilité est dans le type. -/
inductive FractionActorielle where
  | declaree (source : String) (valeur : String) : FractionActorielle
  deriving Repr

/-- **Invariant de typage — toute fraction exhibe sa source.**
    C'est ce que le set affirmait sans le prouver. -/
theorem fraction_exhibe_sa_source (f : FractionActorielle) :
    ∃ s v, f = FractionActorielle.declaree s v := by
  cases f with
  | declaree s v => exact ⟨s, v, rfl⟩

/- ═══════════════════════════════════════════════════════════════════════
   PR-14 — opposabilite_exige_statut_declare        (ÉNONCÉ NOUVEAU)
   ═══════════════════════════════════════════════════════════════════════

   Ce n'est PAS PR-1. PR-1 exige un champ source (DID) sur les valorimètres
   de F8 — c'est une convention de typage (CONV-4). Le théorème ci-dessous
   ajoute une SANCTION, que la spécification ne prévoyait pas.

   Site de sanction : instrument D3 de I.3.6 §6.5, la clause téléologique,
   dont le mode propre est l'INOPPOSABILITÉ — « une prétention conforme à
   la lettre mais contraire à la finalité devient inopposable ».
   Il ne concurrence donc ni D1 (seuil → PR-1, PR-3) ni D2
   (inaliénabilité → NC / PR-11).
-/

inductive RegimeUsage where
  | normatif           : RegimeUsage
  | descriptifSuspendu : RegimeUsage
  deriving DecidableEq, Repr

/-- **Ce que l'agrégat sert à établir** — cinquième terme du statut du
    seuil, versé le 8 septembre 2026 (option D).

    Axe **orthogonal** à `RegimeUsage` : celui-ci dit si le seuil
    déclenche une règle, celui-là dit si une somme sert à établir que
    le seuil est franchi. Les quatre combinaisons existent — voir
    `orthogonalite_usage_agregat_regime_usage` dans `PR10_StatutSeuil`.

    Ancrage : André, M. & Gosseries, A., *La Justice climatique*, PUF
    « Que sais-je ? », 2024, ch. I §II — l'approche par les droits
    fondamentaux « rejette l'agrégation des intérêts qui prévaut dans
    l'analyse coût-bénéfice », et « n'empêche pas, une fois le seuil de
    dignité atteint pour tous, de chercher ensuite à maximiser le
    bien-être agrégé ». L'agrégation est exclue pour CONSTATER le
    franchissement, permise AU-DESSUS.

    ⚠️ **Aucune valeur par défaut.** `nonDeclare` doit être écrit à la
    main. Un champ à valeur par défaut ferait acquérir silencieusement
    à toute inscription existante une déclaration que personne n'a
    faite — `[CHANGEMENT DE BASE NON TRACÉ]` à l'échelle du set. Les
    erreurs de compilation que ce champ produit sont le dispositif,
    pas la nuisance : elles forcent à déclarer.

    ⚠️ **Ce n'est pas ce que traite PR-19.** PR-19 additionne des
    ÉCRITURES dans une SÉRIE ; ce champ porte sur l'agrégation de
    DIMENSIONS à un INSTANT. Aucun des deux ne couvre l'autre. -/
inductive UsageAgregat where
  /-- Une somme ou une moyenne sert à établir que le seuil est franchi. -/
  | constatation : UsageAgregat
  /-- Le franchissement est établi cas par cas ; l'agrégat n'opère
      qu'au-dessus du seuil (répartir, budgéter, comparer). -/
  | auDela       : UsageAgregat
  /-- Aucun agrégat n'intervient : contrôle unité par unité. -/
  | sansAgregat  : UsageAgregat
  /-- Non déclaré. **Refuse, n'autorise pas** — homologue de
      `RegimeDispositif.nonDeclare` (PR-17). -/
  | nonDeclare   : UsageAgregat
  deriving DecidableEq, Repr

/-- Quintuplet « statut du seuil » (règle R0-bis, Annexe §A.14).
    Quadruplet jusqu'au 8 septembre 2026 ; le cinquième terme est
    `usageAgregat`. Objet de PR-10, non de PR-1. -/
structure StatutSeuil where
  source             : String
  conventionMesure   : String
  regimeUsage        : RegimeUsage
  porteurDeclaration : String
  usageAgregat       : UsageAgregat
  deriving Repr

structure Valuemetre where
  nom    : String
  statut : Option StatutSeuil

structure Obligation where
  valuemetre : Valuemetre
  porteur    : Option Actor
  opposable  : Bool

def BienFormee (o : Obligation) : Prop :=
  o.opposable = true → o.valuemetre.statut ≠ none

/-- **PR-14 — pas d'opposabilité sans statut déclaré.** -/
theorem opposabilite_exige_statut_declare (o : Obligation)
    (h_bf : BienFormee o) (h_none : o.valuemetre.statut = none) :
    o.opposable = false := by
  cases h_op : o.opposable with
  | false => rfl
  | true  => exact absurd h_none (h_bf h_op)

/-- La déclaration est contrôlable, non seulement exigée. -/
theorem opposabilite_exhibe_statut (o : Obligation)
    (h_bf : BienFormee o) (h_op : o.opposable = true) :
    ∃ s : StatutSeuil, o.valuemetre.statut = some s := by
  cases h : o.valuemetre.statut with
  | none   => exact absurd h (h_bf h_op)
  | some s => exact ⟨s, rfl⟩

/-- **Délimitation — PR-14 ne borne pas l'attribution.**
    Une obligation peut être attribuée à un porteur nommé sur un seuil sans
    statut, sans violer PR-14. C'est le trou que PR-3 doit fermer, et il
    est ici prouvé plutôt que supposé. -/
theorem PR14_ne_borne_pas_l_attribution :
    ∃ o : Obligation, BienFormee o ∧ o.valuemetre.statut = none
      ∧ o.porteur ≠ none := by
  refine ⟨{ valuemetre := { nom := "seuil non sourcé", statut := none }
          , porteur := some "A"
          , opposable := false }, ?_, rfl, ?_⟩
  · intro h; exact absurd h (by simp)
  · simp

/-! ## Témoins D-13 (règle NT-ARCH §8ter-bis, R-2) — versés le 28/09/2026

Les dépliages `opposabilite_exige_statut_declare`, `opposabilite_exhibe_statut`
(PR-14), `regime_declared_per_ecriture` et `debit_actoriel_exclut_credit_systemique`
(PR-2) sont des **lectures** de `BienFormee` et de `PaireHomogene` (R-3). Ils sont
licites parce que les deux prédicats discriminent : témoin bien formé
`PR14_ne_borne_pas_l_attribution`, témoins ci-dessous. -/

/-- Témoin mal formé de `BienFormee` (PR-14) : opposable sans statut. -/
theorem PR14_temoin_mal_forme :
    ∃ o : Obligation, o.opposable = true ∧ o.valuemetre.statut = none
      ∧ ¬ BienFormee o :=
  ⟨{ valuemetre := { nom := "v", statut := none }, porteur := none, opposable := true },
   rfl, rfl, fun h => h rfl rfl⟩

/-- `PaireHomogene` (PR-2) discrimine : une paire homogène, une paire
    actoriel/systémique qui ne l'est pas. -/
theorem PR2_PaireHomogene_discrimine :
    (∃ p : PaireR1, PaireHomogene p) ∧
    (∃ p : PaireR1, p.coteA.regime = .actoriel
        ∧ p.coteB.regime = .systemique ∧ ¬ PaireHomogene p) :=
  ⟨⟨⟨⟨"r", .actoriel⟩, ⟨"r", .actoriel⟩, rfl⟩, rfl⟩,
   ⟨⟨⟨"r", .actoriel⟩, ⟨"r", .systemique⟩, rfl⟩, rfl, rfl,
    fun h => RegimeObligation.noConfusion h⟩⟩

end ProfRegLot
