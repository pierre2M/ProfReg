/-
  PR-24 · `portee_finie_exclut_toujours`
  ======================================

  **Premier appui formel du palier PAL-1** — nécessité du registre.

  D'OÙ IL VIENT
  -------------
  Le maillon **L1** (« l'externalisation de la mémoire ») était, depuis
  le 6 septembre 2026, *« le seul chemin non circulaire vers PAL-1 »* et
  *« à écrire : ni prouvé, ni listé »*. Le bilan du 8 septembre a
  remarqué que son argument a **exactement la forme** de
  `liste_close_exclut_toujours` (PR-16) : une borne de ressource qui
  laisse toujours quelque chose dehors.

  ~~L'argument de L1, dans les termes du graphe : « L'attention est une
  ressource finie et non stockable […] »~~ [D-11, 28/09/2026 — rattachement
  corrigé, décision de porteur, option (a).] Cette formulation était celle de
  **AX-1 v1**, que la fiche AX-1 v2 (Stépanoff, 7/09) écarte : « la finitude de
  l'attention est de l'oxygène ». L1 est énoncé dans
  `L1_repris_Campo_2026-09-07.md` §5, et c'est cet énoncé que le fichier sert :

  > « Soit un collectif dont les relations métaboliques ont été déplacées
  >   hors du champ où s'exercent ses liens de connaissance et de soin (AX-1),
  >   et dont l'attention est située, sélective et organisée par des
  >   dispositifs de pertinence (AX-10). Alors […] leur soin exige une
  >   médiation de reprise extérieure à toute présence. »

  Une **portée** se lit donc comme **les liens de connaissance et de soin
  d'un collectif à un instant**, non comme l'attention d'un individu.

  CE QUE CE FICHIER ÉTABLIT, ET CE QU'IL N'ÉTABLIT PAS
  -----------------------------------------------------
  Il **ne démontre pas** que les dépendances d'un collectif échappent à ses
  liens de soin : c'est **AX-1 v2** (Stépanoff, *Attachements*, 2024, p. 11-13,
  554-555), un axiome de **recouvrement**, non de cardinalité. Ni que sa
  portée est sélective et organisée par des dispositifs : c'est **AX-10**
  (Campo 2026). **La chaîne reste axiomes + théorème, jamais théorème seul.**

  · §2 Toute portée finie **exclut** — `liste_close_exclut_toujours`
    (PR-16) réutilisé, non réécrit. Sous l'hypothèse `NonEnumerable`, qui est
    **cardinale** : c'est une condition suffisante de modèle, plus forte que
    ce que pose AX-1 v2, et **le résultat central (§3) n'en dépend pas**.
  · §3 **Ce que la présence perd, l'inscription le garde.** C'est le
    pas propre de L1, et il porte sur la **non-stockabilité**, non sur
    la finitude.
  · §4 **L'inscription ne résout pas l'exclusion** — elle supprime la
    perte. Garde essentielle : sans elle, PR-24 se lirait comme une
    preuve que le registre suffit.

  `[RÉSERVE DE MODÈLE]` `Portee` et `couvertureInscrite` sont mes
  structures — réserve du §2quinquies du graphe.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR16_RefutationTiers`.
-/

import ProfReg.PR16_RefutationTiers

namespace ProfRegPR24

open ProfRegPR16

/-! ## 1. Le modèle

Une **portée** est ce qu'un dispositif tient à un moment donné : une
liste finie de relations. C'est tout ce que le modèle retient de
l'attention — et c'est déjà assez. -/

/-- Ce qu'un dispositif tient à l'instant `t`. Le type des relations est
    un **paramètre** : rien ici ne suppose qu'elles soient énumérables,
    ni combien il y en a. -/
def Portee (R : Type) := Nat → List R

variable {R : Type}

/-- **La présence** : à l'instant `t`, un dispositif en présence couvre
    ce qu'il tient à cet instant, et rien d'autre. C'est la
    **non-stockabilité**. -/
def couvertureEnPresence (p : Portee R) (t : Nat) : List R := p t

/-- **L'inscription** : elle accumule. À l'instant `t`, elle couvre tout
    ce qui a été tenu jusque-là. C'est la seule différence entre les
    deux dispositifs, et c'est celle que L1 nomme. -/
def couvertureInscrite (p : Portee R) : Nat → List R
  | 0     => p 0
  | n + 1 => couvertureInscrite p n ++ p (n + 1)

/-! ## 2. Toute portée finie exclut — PR-16 réutilisé

On ne réécrit pas l'argument : on l'importe. Même procédé que
PR-22 → PR-16 et PR-13 → PR-21. -/

/-- **PR-24 (1).** Si les relations ne sont pas énumérables par une
    liste finie, alors **à tout instant, un dispositif en présence en
    laisse une dehors**.

    C'est `NonEnumerable` de PR-16, appliqué à la portée au lieu de la
    liste des réfutants. -/
theorem la_presence_exclut_toujours (h_ne : NonEnumerable R)
    (p : Portee R) (t : Nat) :
    ∃ r : R, r ∉ couvertureEnPresence p t :=
  h_ne (p t)

/-- **Et l'inscription aussi.** À tout instant fini, la couverture
    accumulée est encore une liste finie : elle exclut donc également.

    **C'est la garde du §4 énoncée d'emblée** — l'inscription ne lève
    pas la finitude. -/
theorem l_inscription_exclut_aussi (h_ne : NonEnumerable R)
    (p : Portee R) (t : Nat) :
    ∃ r : R, r ∉ couvertureInscrite p t :=
  h_ne (couvertureInscrite p t)

-- **Non-énumérabilité des relations — hypothèse de modélisation, déclarée.** Les
-- relations sont indexées par `Nat` ; que la population des relations ne soit pas
-- énumérable est la *portée visée*, non établie par un énoncé. L'instance sur `Nat`
-- est `ProfRegPR16.nat_non_enumerable`, comme pour les tiers de PR-16 : c'est elle
-- qui satisfait l'hypothèse `h_ne` des théorèmes ci-dessus.
-- [11/10/2026 — RETIRÉ, doublon d'énoncé sans usage : `les_relations_indexees_par_Nat_ne_sont_pas_enumerables`
--  (`NonEnumerable Nat`, preuve `nat_non_enumerable`) ; nommé par aucun fichier du set MRC v5.7, cité par
--  aucune preuve ni par `R7_Controle.lean`.]

/-! ## 3. Le pas propre de L1 : ce que la présence perd, l'inscription
le garde

La finitude ne distingue pas les deux dispositifs (§2). **C'est la
non-stockabilité qui les distingue**, et c'est elle que ce paragraphe
établit. -/

/-- **PR-24 (2) — l'inscription est monotone.** Ce qui est couvert à
    l'instant `t` l'est encore à l'instant `t+1`. -/
theorem l_inscription_est_monotone (p : Portee R) (t : Nat) (r : R)
    (h : r ∈ couvertureInscrite p t) : r ∈ couvertureInscrite p (t + 1) := by
  unfold couvertureInscrite
  exact List.mem_append_left _ h

/-- **PR-24 (3) — le résultat central.** Il existe une portée et une
    relation **tenue à un instant, lâchée au suivant** : la présence l'a
    perdue, l'inscription la garde.

    C'est exactement le pas de L1, et il ne suit **pas** de la finitude :
    §2 vaut pour les deux dispositifs. **Ce qui les sépare est la
    stockabilité, non la portée.** -/
theorem la_presence_perd_ce_que_l_inscription_garde :
    ∃ (p : Portee Nat) (r : Nat),
      r ∈ couvertureEnPresence p 0
      ∧ r ∉ couvertureEnPresence p 1
      ∧ r ∈ couvertureInscrite p 1 := by
  refine ⟨fun t => if t = 0 then [7] else [], 7, ?_, ?_, ?_⟩
  · simp [couvertureEnPresence]
  · simp [couvertureEnPresence]
  · simp [couvertureInscrite]

/-- **Et le soin porte sur ce qui est couvert.** Formulé sans détour :
    un dispositif ne peut pas prendre soin d'une relation qu'il ne
    couvre pas. C'est une définition, pas un théorème — elle est écrite
    ici pour que la chaîne de L1 soit lisible, et elle est **le point
    où les axiomes entrent** (AX-1 v2, AX-10). -/
def PrendSoinDe (couverture : List R) (r : R) : Prop := r ∈ couverture

/-- **PR-24 (4) — la conclusion de L1, sous sa forme exacte.** Une
    relation lâchée par la présence cesse d'en être l'objet de soin,
    tandis qu'elle reste celui de l'inscription.

    **Voilà tout ce que la formalisation donne à PAL-1**, et c'est déjà ce
    que le graphe cherchait depuis le 6 septembre. Le reste — que les
    dépendances d'un collectif *échappent* à ses liens de soin (AX-1 v2), et
    que sa portée *soit* sélective et organisée par des dispositifs (AX-10) —
    se déclare. -/
theorem le_soin_en_presence_se_perd :
    ∃ (p : Portee Nat) (r : Nat),
      PrendSoinDe (couvertureEnPresence p 0) r
      ∧ ¬ PrendSoinDe (couvertureEnPresence p 1) r
      ∧ PrendSoinDe (couvertureInscrite p 1) r :=
  la_presence_perd_ce_que_l_inscription_garde

/-- **Le recouvrement d'AX-1 v2, en termes du modèle.** Une dépendance
    *échappe* à une couverture si elle est une dépendance du collectif et
    qu'elle n'est pas couverte : c'est `M(C) \ K(C) ≠ ∅`, colonne B de la
    fiche AX-1 v2. [D-11, 28/09/2026] -/
def Echappe (M : R → Prop) (couverture : List R) : Prop :=
  ∃ r : R, M r ∧ r ∉ couverture

/-- **PR-24 (5) — la présence produit l'échappement ; l'inscription
    l'évite.** Il existe un collectif dont les dépendances sont toutes
    couvertes à l'instant 0, dont une échappe à la présence à l'instant 1,
    et dont aucune n'échappe à l'inscription à l'instant 1.

    C'est le pas de L1 dans les termes mêmes d'AX-1 v2 — un argument de
    **recouvrement**, non de cardinalité : aucune hypothèse `NonEnumerable`
    n'est requise. Il ne dit pas que le déplacement hors du champ du soin
    **a** lieu (c'est AX-1 v2, qui le date et le rend réversible) ; il dit
    que, s'il a lieu par défaut de présence, l'inscription le compense.
    [D-11, 28/09/2026 — proposition] -/
theorem la_presence_produit_l_echappement :
    ∃ (p : Portee Nat) (M : Nat → Prop),
      ¬ Echappe M (couvertureEnPresence p 0)
      ∧ Echappe M (couvertureEnPresence p 1)
      ∧ ¬ Echappe M (couvertureInscrite p 1) := by
  refine ⟨fun t => if t = 0 then [7] else [], fun r => r = 7, ?_, ?_, ?_⟩
  · rintro ⟨r, hr, hn⟩
    subst hr
    exact hn (by simp [couvertureEnPresence])
  · exact ⟨7, rfl, by simp [couvertureEnPresence]⟩
  · rintro ⟨r, hr, hn⟩
    subst hr
    exact hn (by simp [couvertureInscrite])

/-! ## 4. Gardes — et la première est la plus importante -/

/-- **PR-24 ne démontre pas que le registre suffit.** L'inscription
    exclut, elle aussi (§2) : elle ne lève pas l'exclusion, **elle
    supprime la perte**. Un objecteur qui lirait PAL-1 comme « le registre
    résout le problème de l'attention » serait démenti par ce
    théorème-ci, du fichier même qui soutient PAL-1. -/
theorem PR24_ne_dit_pas_que_le_registre_suffit (h_ne : NonEnumerable R)
    (p : Portee R) (t : Nat) :
    (∃ r : R, r ∉ couvertureEnPresence p t)
  ∧ (∃ r : R, r ∉ couvertureInscrite p t) :=
  ⟨la_presence_exclut_toujours h_ne p t, l_inscription_exclut_aussi h_ne p t⟩

/-- **PR-24 ne démontre pas que les relations excèdent la portée.** C'est une
    donnée posée hors du fichier, jamais prouvée pour un type quelconque. On
    l'inscrit en montrant que **sans** l'hypothèse `NonEnumerable`, la conclusion
    du §2 tombe : sur un type énumérable, une portée finie peut tout couvrir.

    [A-8 — APPLIQUÉ LE 27/09] Remplace l'énoncé `couvertureEnPresence p t = p t`
    (vrai par définition — forme 1). [D-11 — 28/09] Renommé : ex-`PR24_ne_prouve_pas_A1`.
    Ce que le fichier ne prouve pas n'est pas « AX-1 » au sens d'une attention finie
    (AX-1 v1, écarté) : c'est l'excès des dépendances sur les liens de soin, qui
    relève d'AX-1 v2 et d'AX-10. -/
theorem PR24_l_exclusion_est_conditionnelle :
    ∃ (p : Portee Bool) (t : Nat), ∀ r : Bool, r ∈ couvertureEnPresence p t :=
  ⟨fun _ => [true, false], 0, fun r => by cases r <;> simp [couvertureEnPresence]⟩

/-- **Deux portées de même présence peuvent avoir des inscriptions
    différentes.** *Portée visée — déclarée, non établie par l'énoncé :* PR-24 ne dit pas que ce qui est inscrit est
    vrai, ni qu'on s'en occupe. La couverture est une condition d'accès, pas une
    performance : deux portées peuvent couvrir la même relation et n'en
    rien faire. Le fichier porte sur ce qui **peut** être objet de soin,
    jamais sur ce qui l'est. -/
-- [B-10, 28/09/2026 — RENOMMÉ, ex-`PR24_ne_juge_pas_le_soin`] L'énoncé : deux portées de même présence à 0 et d'inscription différente à 1. Le « soin » n'y est pas jugé parce qu'il n'y figure pas.
theorem meme_presence_inscriptions_differentes :
    ∃ p q : Portee Nat,
      couvertureEnPresence p 0 = couvertureEnPresence q 0
      ∧ couvertureInscrite p 1 ≠ couvertureInscrite q 1 := by
  refine ⟨fun _ => [7], fun t => if t = 0 then [7] else [], ?_, ?_⟩
  · rfl
  · simp [couvertureInscrite]

/-! **PR-24 ne rend pas PAL-1 démontré.** Il fournit **un maillon** — le plus
    disputé, celui que le graphe cherchait — dans une chaîne qui reste
    **axiome + théorème**. PAL-1 demeure un palier **procédural**, et l'écrire
    autrement serait un `[DÉCOUPLAGE DE RÉGIMES]`.

    [A-8 — RETIRÉ LE 27/09] Le théorème `PR24_ne_conclut_pas_P1`
    rendait son hypothèse en conclusion (`PrendSoinDe … r` est par définition
    `r ∈ …`) : forme 3, celle qui a fait retirer les deux V10c le 7/09. Une garde
    qui ne peut pas s'énoncer formellement se déclare ; elle ne se « prouve » pas. -/

end ProfRegPR24
