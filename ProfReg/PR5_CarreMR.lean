/-
  PR-5 · carré M↔R — `carre_mimetique_responsabilite`
  ===================================================

  NT-G8 §10.1 — couplage **G-MIMETIQUE ↔ G-RESPONSABILITE** (amendement A5 des grammaires — non l'axiome AX-5 « non-fermeture des chaînes » ;
  collision de numérotation corrigée au set le 8/09, Annexe §A.15.1 ; reportée ici le 27/09, A-9).

  · **Sens M→R.** Condition : `focalisation_victimaire = VRAI` (niveau
    LEVÉ, post-crise) ET `meconnaissance_fondatrice = VRAI`. Action :
    R-MECONNAISSANCE inscrit `principe_precaution_asymetrique = VRAI`.
  · **Sens R→M.** Condition : `regimeobligation = SYSTEMIQUE` ET une
    obligation relationnelle signale un acteur exclu dans la genèse.
    Action : alerte — vérifier `meconnaissance_fondatrice = VRAI` ET
    `voix_victime_inscrite = FAUX`. Si les deux : R-MECONNAISSANCE.
  · **Persistance** (§10.2) : `principe_precaution_asymetrique = VRAI`
    **jusqu'à** `voix_victime_inscrite = VRAI` **ET** audit
    `tracabilite_genese = COMPLET`.

  LE SET ATTENDAIT UN CARRÉ COMMUTATIF ; CE N'EN EST PAS UN
  ---------------------------------------------------------
  §C-II.2 demande « carré M↔R commutatif (sens M→R et R→M) », et §C-II.4
  déclare un **risque de bascule en lacune hors Mathlib** (framed
  bicategories). **Le risque ne se réalise pas, et la demande non
  plus** : §2 démontre que le carré **ne commute pas**, et §3 que ce qui
  le ferme est un **acte** — l'inscription de la voix de la victime et
  un audit complet — exactement comme VJE
  (`VJE_carre_ne_commute_pas_sans_revision`,
  `VJE_ferme_apres_revision_externe`).

  > **PR-5 n'a donc besoin d'aucune 2-cellule.** C'est une machine
  > d'états, comme VJE. La bascule hors Mathlib annoncée depuis le plan
  > v6 n'a pas lieu.

  `[RÉSERVE DE MODÈLE]` `EtatMR`, `sensMR`, `sensRM` sont mes
  structures — réserve du §2quinquies du graphe.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR5

/-! ## 1. Le modèle -/

structure EtatMR where
  /-- G-MIMETIQUE, niveau LEVÉ post-crise. -/
  focalisationVictimaire : Bool
  /-- G-MIMETIQUE. -/
  meconnaissanceFondatrice : Bool
  /-- G-RESPONSABILITE : le régime est systémique. -/
  regimeSystemique : Bool
  /-- G-RESPONSABILITE : une obligation relationnelle signale un acteur
      exclu dans la genèse. -/
  acteurExcluSignale : Bool
  /-- L'acte qui ferme — et il n'est produit par aucun des deux sens. -/
  voixVictimeInscrite : Bool
  /-- L'audit qui ferme, avec l'acte. -/
  tracabiliteGeneseComplete : Bool
  /-- Le champ inscrit par R-MECONNAISSANCE (§10.2). -/
  precautionAsymetrique : Bool
  deriving DecidableEq, Repr

/-- **Sens M→R.** Inscrit la précaution asymétrique sous ses deux
    conditions. -/
def sensMR (e : EtatMR) : EtatMR :=
  { e with precautionAsymetrique :=
      e.precautionAsymetrique
        || (e.focalisationVictimaire && e.meconnaissanceFondatrice) }

/-- **Sens R→M.** L'alerte : si le régime est systémique et un acteur
    exclu est signalé, on vérifie la méconnaissance fondatrice **et**
    l'absence de voix inscrite ; si les deux, R-MECONNAISSANCE est
    déclenché — donc la focalisation victimaire est levée en
    G-MIMETIQUE. -/
def sensRM (e : EtatMR) : EtatMR :=
  { e with focalisationVictimaire :=
      e.focalisationVictimaire
        || (e.regimeSystemique && e.acteurExcluSignale
            && e.meconnaissanceFondatrice && !e.voixVictimeInscrite) }

/-- **La levée du principe** (§10.2, persistance) : elle exige les deux
    actes ensemble, et **aucun des deux sens ne les produit**. -/
def lever (e : EtatMR) : EtatMR :=
  if e.voixVictimeInscrite && e.tracabiliteGeneseComplete
  then { e with precautionAsymetrique := false }
  else e

/-! ## 2. Le carré ne commute pas -/

/-- **PR-5 (1).** Il existe un état sur lequel `M→R` puis `R→M` diffère
    de `R→M` puis `M→R`.

    La raison est structurelle et non accidentelle : `sensRM` **écrit**
    `focalisationVictimaire`, que `sensMR` **lit**. L'ordre importe donc
    nécessairement. -/
theorem le_carre_MR_ne_commute_pas :
    ∃ e : EtatMR, sensRM (sensMR e) ≠ sensMR (sensRM e) := by
  refine ⟨⟨false, true, true, true, false, false, false⟩, ?_⟩
  intro h
  have := congrArg EtatMR.precautionAsymetrique h
  simp [sensMR, sensRM] at this

/-- **PR-5 (2) — et l'écart a un sens précis.** Sur ce même état, le
    chemin `R→M` puis `M→R` inscrit la précaution asymétrique, tandis
    que l'ordre inverse ne l'inscrit pas.

    Ce n'est donc pas une divergence technique : **c'est l'alerte de
    G-RESPONSABILITE qui rend la focalisation lisible par
    G-MIMETIQUE.** Traiter le carré comme commutatif aurait effacé
    exactement cela. -/
theorem l_ordre_RM_puis_MR_inscrit_seul :
    (sensMR (sensRM ⟨false, true, true, true, false, false, false⟩)).precautionAsymetrique = true
  ∧ (sensRM (sensMR ⟨false, true, true, true, false, false, false⟩)).precautionAsymetrique = false := by
  constructor <;> rfl

/-! ## 3. Ce qui ferme le carré est un acte, non un calcul -/

/-- **PR-5 (3).** Aucun des deux sens ne produit `voixVictimeInscrite` :
    ni `sensMR` ni `sensRM` ne le modifient. Le champ traverse les deux
    canaux inchangé.

    C'est l'homologue exact de `sensJE_ne_produit_pas_la_revision`
    (VJE) : **le carré ne peut pas se fermer de lui-même.** -/
theorem aucun_sens_ne_produit_la_voix (e : EtatMR) :
    (sensMR e).voixVictimeInscrite = e.voixVictimeInscrite
  ∧ (sensRM e).voixVictimeInscrite = e.voixVictimeInscrite :=
  ⟨rfl, rfl⟩

/-- **Ni l'audit de traçabilité.** Les deux conditions de la levée sont
    hors du calcul. -/
theorem aucun_sens_ne_produit_l_audit (e : EtatMR) :
    (sensMR e).tracabiliteGeneseComplete = e.tracabiliteGeneseComplete
  ∧ (sensRM e).tracabiliteGeneseComplete = e.tracabiliteGeneseComplete :=
  ⟨rfl, rfl⟩

/-- **PR-5 (4) — le carré ferme après l'acte extérieur.** Une fois la
    voix inscrite **et** l'audit complet, la précaution asymétrique est
    levée. Homologue de `VJE_ferme_apres_revision_externe`.

    Noter ce que l'énoncé ne contient pas : ni `sensMR`, ni `sensRM`.
    **L'acte est une prémisse, non un produit du carré** — et c'est la
    leçon que le retrait de `VJE_commutatif` avait inscrite la veille. -/
theorem le_carre_ferme_apres_l_acte (e : EtatMR)
    (hv : e.voixVictimeInscrite = true) (ha : e.tracabiliteGeneseComplete = true) :
    (lever e).precautionAsymetrique = false := by
  unfold lever
  rw [hv, ha]
  simp

/-- **Et il ne ferme pas avec un seul des deux.** La conjonction du
    §10.2 n'est pas décorative : la voix inscrite sans audit complet ne
    lève rien. -/
theorem un_seul_des_deux_actes_ne_ferme_pas :
    (lever ⟨true, true, true, true, true, false, true⟩).precautionAsymetrique = true := rfl

/-! ## 4. Gardes -/

/-- **PR-5 ne réfute pas l'amendement A5** (non l'axiome AX-5). Le couplage existe dans les deux sens —
    c'est ce que §10.1 établit, et le fichier s'en sert. Ce qui est
    réfuté est la **commutativité**, qui était une demande du programme
    de preuve, non un énoncé de la grammaire. -/
theorem PR5_ne_refute_pas_le_couplage (e : EtatMR)
    (hf : e.focalisationVictimaire = true) (hm : e.meconnaissanceFondatrice = true) :
    (sensMR e).precautionAsymetrique = true := by
  unfold sensMR
  simp only []
  rw [hf, hm]
  simp

/-- **PR-5 ne juge pas la méconnaissance.** Les deux sens sont des
    règles de déclenchement : ils ne disent pas qu'une méconnaissance
    fondatrice a eu lieu, seulement ce qui suit si elle est déclarée. -/
theorem PR5_ne_juge_pas_la_meconnaissance (e : EtatMR)
    (hm : e.meconnaissanceFondatrice = false) :
    (sensMR e).precautionAsymetrique = e.precautionAsymetrique := by
  unfold sensMR
  simp only []
  rw [hm]
  simp

/-! [C-7 — RETIRÉ LE 28/09/2026, décision du porteur] `PR5_est_une_machine_d_etats`
    énonçait `∃ e₁ e₂, sensRM (sensMR e) = e₁ ∧ sensMR (sensRM e) = e₂` : vrai de
    toutes fonctions (forme 1). Le constat qu'il visait — **PR-5 ne demande aucune
    2-cellule** : le fichier est une machine d'états sur des booléens, sans
    structure catégorielle — est un fait d'**imports** (aucun module
    `CategoryTheory` n'est importé), vérifiable sur l'en-tête, non un théorème. Garde de non-régression déclarée : ne pas réintroduire ce théorème sous un autre nom. -/

end ProfRegPR5
