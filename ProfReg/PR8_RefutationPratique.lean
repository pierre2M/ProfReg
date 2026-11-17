/-
  PR-8 · `representation_pratique_refutation`
  ===========================================

  Spécification d'origine (MRC v5.6) :
    · `MRC_v5.6_Annexe_Methodologique.md`, tableau PR —
      « legitimiterepresentant = PRATIQUE → conditionrefutation
        obligatoire (extension du cas planétaire V10c au cas
        PRATIQUE) » ; renvoi NT-ARCH §5.2
    · `MRC_v5.6_NT-ARCH_Architecture_Couches0-3.md` §5.2
      (REPRESENTATION-PROSPECTIVE, B3) :
        legitimiterepresentant ∈ { PRATIQUE (défaut) / DELIBERATIVE /
                                   JURIDIQUE / planetaireNonDesignee }
        conditionrefutation — OBLIGATOIRE si legitimiterepresentant
                              = PRATIQUE ou planetaireNonDesignee
      et le cas AM-ARCH-01 : horizon PLANETAIRE + porteur
      structurellement absent → legitimite = planetaireNonDesignee
      et conditionrefutation OBLIGATOIRE, « invariant de Couche 1,
      non bonne pratique ».

  ⚠️ AVERTISSEMENT — ce fichier N'EST PAS l'extension directe de
  V10c annoncée par la note de bilan du 11 juin 2026.

  Les deux théorèmes V10c de `V10Verification.lean` sont défectueux,
  et les étendre aurait propagé le défaut :

  · `V10c_representation_prospective_obligatoire` prend
    `h_cond : condRefutationRenseignee c` EN HYPOTHÈSE et la restitue
    dans sa conclusion. Il démontre donc « si la condition de
    réfutation est renseignée, alors elle est renseignée ».
    L'obligation — qu'elle DOIVE l'être — n'y est jamais établie.
    [RAISONNEMENT AUTORÉFÉRENTIEL]

  · `V10c_sans_refutation_bloque` n'utilise pas son hypothèse
    `h_no_cond` (la preuve est `intro h_neg; exact h_neg ⟨h_horizon,
    h_absent⟩`). Son énoncé se réduit à `exigeRepresentationProspective
    c`, déjà donné par les deux autres hypothèses. Rien n'y est
    « bloqué » : le nom sur-revendique.
    [ENGAGEMENT SANS SYMÉTRIE]

  Ce fichier écrit donc l'obligation comme une CONDITION DE BONNE
  FORMATION de l'inscription — le patron de PR-14, PR-15 et PR-3 —
  et non comme une hypothèse. Il couvre au passage le cas planétaire
  correctement énoncé (§4), ce qui rend les deux V10c remplaçables.

  DÉDUPLIQUÉ le 7 septembre 2026 au soir (tâche 3quinquies).
  Les types venaient d'une COPIE de `V10Verification.lean`, qui
  importe Mathlib transitivement et n'était donc pas importable ici.
  La copie avait déjà dérivé : son `ContexteProspectif` avait quatre
  champs au lieu de cinq — `statutDette` manquait. Les types viennent
  désormais de `ProfReg.Primitives`, sans Mathlib, où ils sont
  déclarés une seule fois pour tout le set.

  Porteur : Pierre Musseau. Écrit le 7 septembre 2026.
  Lean 4 pur, sans Mathlib.
-/

import ProfReg.Primitives

namespace ProfRegPR8

/-! ## 1. Les primitives du set (NT-ARCH §5.2)

Elles ne sont plus recopiées : `LegitimiteRepresentant`,
`HorizonTemporel`, `PorteurDID` et `ContexteProspectif` viennent de
`ProfReg.Primitives`.

`pratique` y est **la valeur par défaut** — le texte de §5.2 le dit
entre parenthèses, et c'est un fait architectural, pas une commodité
de rédaction (§5). -/

open V10

/-! ## 2. L'obligation, écrite comme condition de bonne formation

§5.2 : « conditionrefutation — OBLIGATOIRE si legitimiterepresentant
= PRATIQUE ou planetaireNonDesignee ». La disjonction est celle du
texte ; elle n'est pas élargie. -/

def RefutationObligatoire (c : ContexteProspectif) : Prop :=
  c.legitimite = LegitimiteRepresentant.pratique ∨
  c.legitimite = LegitimiteRepresentant.planetaireNonDesignee

def BienFormee (c : ContexteProspectif) : Prop :=
  RefutationObligatoire c → c.condRefutation ≠ none

/-! ## 3. PR-8 -/

/-- **PR-8 — `representation_pratique_refutation`.** Une inscription
    bien formée dont la légitimité du représentant est PRATIQUE
    exhibe une condition de réfutation.

    C'est le cas que la spécification voulait ajouter au cas
    planétaire — et c'est le cas **par défaut**, donc le plus
    fréquent (§5). -/
theorem representation_pratique_refutation
    (c : ContexteProspectif) (h_bf : BienFormee c)
    (h_prat : c.legitimite = LegitimiteRepresentant.pratique) :
    ∃ t, c.condRefutation = some t := by
  have h : c.condRefutation ≠ none := h_bf (Or.inl h_prat)
  cases hc : c.condRefutation with
  | none => exact absurd hc h
  | some t => exact ⟨t, rfl⟩

/-- **Le cas planétaire, correctement énoncé.** Même théorème, autre
    disjoint. C'est ce que `V10c_representation_prospective_obligatoire`
    prétendait établir sans y parvenir : ici la condition de
    réfutation est **conclue**, non supposée. -/
theorem representation_planetaire_refutation
    (c : ContexteProspectif) (h_bf : BienFormee c)
    (h_pl : c.legitimite = LegitimiteRepresentant.planetaireNonDesignee) :
    ∃ t, c.condRefutation = some t := by
  have h : c.condRefutation ≠ none := h_bf (Or.inr h_pl)
  cases hc : c.condRefutation with
  | none => exact absurd hc h
  | some t => exact ⟨t, rfl⟩

/-- **Une inscription bien formée sans condition de réfutation n'est pas
    obligée.** Contraposée : une inscription bien formée sans condition de
    réfutation ne peut relever ni de PRATIQUE ni de planetaireNonDesignee.

    [CONV-7 — 28/09/2026, décision du porteur : le marqueur plutôt que le
    refus] Renommé (ex-`PR8_sans_refutation_bloque`) : rien n'est « bloqué ».
    Une inscription **obligée** sans condition n'est pas bien formée ; elle est
    inscrite avec le marqueur `[CONDITION DE RÉFUTATION ABSENTE]`
    (`marqueurRefutationAbsente`, ci-dessous), non refusée. -/
theorem bien_formee_sans_refutation_n_est_pas_obligee
    (c : ContexteProspectif) (h_bf : BienFormee c)
    (h_none : c.condRefutation = none) :
    ¬ RefutationObligatoire c := by
  intro h_obl
  exact h_bf h_obl h_none

/-! ## 4. Le cas AM-ARCH-01, chaîné

§5.2 : « Lorsque HorizonTemporel = PLANETAIRE et que le porteur est
structurellement absent, legitimiterepresentant prend la valeur
planetaireNonDesignee et conditionrefutation devient OBLIGATOIRE —
invariant de Couche 1, non bonne pratique. »

Deux règles enchaînées, et non une : la première fixe la légitimité,
la seconde en tire l'obligation. On les écrit comme telles. -/

/-- Première règle de AM-ARCH-01 : la légitimité est **forcée** par
    la conjonction horizon planétaire / porteur absent. -/
def RegleAM_ARCH_01 (c : ContexteProspectif) : Prop :=
  c.horizon = HorizonTemporel.planetaire →
  c.porteurDID = none →
  c.legitimite = LegitimiteRepresentant.planetaireNonDesignee

/-- **AM-ARCH-01 en entier.** Horizon planétaire et porteur absent
    entraînent une condition de réfutation renseignée — en passant
    par la légitimité, jamais en la court-circuitant.

    C'est le théorème que V10c visait. Il tient parce que
    l'obligation est une condition de bonne formation et non une
    hypothèse. -/
theorem planetaire_sans_porteur_exige_refutation
    (c : ContexteProspectif)
    (h_am : RegleAM_ARCH_01 c) (h_bf : BienFormee c)
    (h_horizon : c.horizon = HorizonTemporel.planetaire)
    (h_absent : c.porteurDID = none) :
    ∃ t, c.condRefutation = some t :=
  representation_planetaire_refutation c h_bf (h_am h_horizon h_absent)

/-! ## 5. Le défaut n'exempte pas

§5.2 écrit « PRATIQUE (défaut) ». Ce parenthésage porte un résultat
d'architecture : la valeur qu'une inscription prend quand personne
n'a tranché est **celle qui oblige**. Le silence ne dispense pas —
il engage. -/

def legitimiteParDefaut : LegitimiteRepresentant :=
  LegitimiteRepresentant.pratique

/-- **La valeur par défaut est du côté de l'obligation.** Une
    inscription qui n'a pas décidé de la légitimité de son
    représentant doit néanmoins une condition de réfutation.

    C'est le bon sens de la règle : on ne s'exonère pas en
    s'abstenant de qualifier. -/
theorem le_defaut_exige_la_refutation
    (c : ContexteProspectif) (h_bf : BienFormee c)
    (h_def : c.legitimite = legitimiteParDefaut) :
    ∃ t, c.condRefutation = some t :=
  representation_pratique_refutation c h_bf h_def

/-! ## 6. PR-8 trie — et on le démontre

Le test oxygène/allumette : une règle qui obligerait toute
inscription n'expliquerait rien. Les deux légitimités procédurales
— DELIBERATIVE et JURIDIQUE — sont exemptées, parce qu'une
procédure a déjà été suivie qui rend le représentant contestable
autrement. -/

/-- **Exactement deux régimes obligent** : l'obligation de réfutation tient
    si et seulement si la légitimité n'est pas procédurale (DELIBERATIVE ou
    JURIDIQUE).

    [D-15 — 28/09/2026, décision du porteur, option (a), nom conservé] L'ancien
    énoncé énumérait les quatre constructeurs en deux paires, sans mentionner
    `RefutationObligatoire` : vrai de tout `l` (forme 1), il n'établissait pas
    ce que son nom annonce. Reformulé en caractérisation, il couvre désormais
    l'exemption JURIDIQUE, qu'aucun théorème ne portait. Lecture de
    `RefutationObligatoire` (R-7) : témoins `representation_pratique_refutation`
    (valeur vraie) et `PR8_ne_vaut_pas_pour_les_legitimites_procedurales`
    (valeur fausse). -/
theorem exactement_deux_regimes_obliges (c : ContexteProspectif) :
    RefutationObligatoire c ↔
      ¬ (c.legitimite = LegitimiteRepresentant.deliberative ∨
         c.legitimite = LegitimiteRepresentant.juridique) := by
  unfold RefutationObligatoire
  generalize c.legitimite = l
  cases l <;> decide

/-- **PR-8 ne vaut pas partout.** Une inscription bien formée à
    légitimité DELIBERATIVE peut n'avoir aucune condition de
    réfutation. Sans ce contre-exemple, PR-8 serait indiscernable
    d'une obligation universelle, et la distinction des quatre
    légitimités serait décorative. -/
theorem PR8_ne_vaut_pas_pour_les_legitimites_procedurales :
    ∃ c : ContexteProspectif, BienFormee c ∧ c.condRefutation = none := by
  refine ⟨{ statutDette := ProfReg.StatutDette.attribuee
          , horizon := HorizonTemporel.intergenerationnel
          , porteurDID := some "did:mrc:assemblée-délibérative"
          , legitimite := LegitimiteRepresentant.deliberative
          , condRefutation := none }, ?_, rfl⟩
  intro h_obl
  cases h_obl with
  | inl h => exact LegitimiteRepresentant.noConfusion h
  | inr h => exact LegitimiteRepresentant.noConfusion h

/-! ## 7. Ce que PR-8 ne fait pas -/

/-- **PR-8 exige qu'une condition de réfutation soit inscrite ; il
    ne juge pas si elle est praticable.** On exhibe une inscription
    bien formée dont la condition, textuellement présente, n'est
    manifestement réfutable par personne.

    C'est la limite exacte de la règle, et elle désigne un maillon
    encore sans appui du programme : **L3 — réfutabilité ⟹
    inspectabilité par des tiers**. Tant que L3 n'est pas établi,
    PR-8 garantit une inscription, pas une possibilité effective de
    contester. Le palier PAL-4 (open source) est ce qui devrait
    combler l'écart ; il ne peut pas s'appuyer sur PR-8 seul pour
    le faire. -/
theorem PR8_ne_juge_pas_la_praticabilite :
    ∃ c : ContexteProspectif,
      BienFormee c ∧ c.legitimite = LegitimiteRepresentant.pratique ∧
      c.condRefutation = some "réfutable par le seul porteur, à huis clos" := by
  refine ⟨{ statutDette := ProfReg.StatutDette.nonAttribuee
          , horizon := HorizonTemporel.intergenerationnel
          , porteurDID := none
          , legitimite := LegitimiteRepresentant.pratique
          , condRefutation :=
              some "réfutable par le seul porteur, à huis clos" }, ?_, rfl, rfl⟩
  intro _
  simp

/-! ## Témoins D-13 (règle NT-ARCH §8ter-bis, R-2) — versés le 28/09/2026

`representation_pratique_refutation`, `representation_planetaire_refutation`,
`PR8_sans_refutation_bloque`, `le_defaut_exige_la_refutation` et
`planetaire_sans_porteur_exige_refutation` **lisent** l'obligation déclarée dans
`BienFormee` (et `RegleAM_ARCH_01`) ; ils ne la démontrent pas (R-3). Ce qui est
démontré est que ces définitions discriminent : témoins bien formés
`PR8_ne_vaut_pas_pour_les_legitimites_procedurales`, `PR8_ne_juge_pas_la_praticabilite` ;
témoins ci-dessous. -/

/-- Témoin mal formé de `BienFormee` : légitimité pratique, sans condition
    de réfutation. -/
theorem PR8_temoin_mal_forme :
    ∃ c : ContexteProspectif, c.legitimite = .pratique
      ∧ c.condRefutation = none ∧ ¬ BienFormee c :=
  ⟨{ statutDette := .nonAttribuee, horizon := .intergenerationnel,
     porteurDID := none, legitimite := .pratique, condRefutation := none },
   rfl, rfl, fun h => h (Or.inl rfl) rfl⟩

/-- `RegleAM_ARCH_01` discrimine : satisfaite par un contexte planétaire sans
    porteur à légitimité non désignée, violée si la légitimité y est pratique. -/
theorem PR8_RegleAM_discrimine :
    (∃ c : ContexteProspectif, c.horizon = .planetaire ∧ c.porteurDID = none
        ∧ RegleAM_ARCH_01 c) ∧
    (∃ c : ContexteProspectif, c.horizon = .planetaire ∧ c.porteurDID = none
        ∧ ¬ RegleAM_ARCH_01 c) :=
  ⟨⟨{ statutDette := .nonAttribuee, horizon := .planetaire, porteurDID := none,
      legitimite := .planetaireNonDesignee, condRefutation := none },
     rfl, rfl, fun _ _ => rfl⟩,
   ⟨{ statutDette := .nonAttribuee, horizon := .planetaire, porteurDID := none,
      legitimite := .pratique, condRefutation := none },
     rfl, rfl, (fun h => nomatch (h rfl rfl))⟩⟩

/-! ## CONV-7 — le marqueur plutôt que le refus (28/09/2026)

Décision du porteur, sur le patron de CONV-15 : une inscription dont la
condition de réfutation est obligatoire et absente est **inscrite, avec un
marqueur** ; elle n'est pas refusée. Ce qui est refusé (RSO-8) est l'**effet**
— l'inscription marquée n'est pas bien formée, donc pas opposable comme
telle —, non l'inscription. -/

/-- Le marqueur `[CONDITION DE RÉFUTATION ABSENTE]`. -/
def marqueurRefutationAbsente (c : ContexteProspectif) : Bool :=
  match c.legitimite, c.condRefutation with
  | LegitimiteRepresentant.pratique, none => true
  | LegitimiteRepresentant.planetaireNonDesignee, none => true
  | _, _ => false

/-- **Le marqueur se lève exactement sur le défaut de bonne formation** :
    la réfutation est obligatoire et la condition est absente. Caractérisation,
    patron `V1_commute_ssi_coherence` (CONV-15). -/
theorem le_marqueur_se_leve_exactement_sur_le_defaut (c : ContexteProspectif) :
    marqueurRefutationAbsente c = true ↔
      (RefutationObligatoire c ∧ c.condRefutation = none) := by
  cases c with
  | mk sd hz p l cr =>
    cases l <;> cases cr <;>
      simp [marqueurRefutationAbsente, RefutationObligatoire]

end ProfRegPR8
