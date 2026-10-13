/-
  PR-18 · `porteur_du_seuil_exhibe_sa_population`
  ===============================================

  Nœud L6 du graphe : **le porteur de la déclaration du seuil.**

  CE QU'IL ÉTABLIT
  ----------------
  Une déclaration de seuil exhibe deux choses distinctes — QUI déclare
  et À QUI le seuil s'applique — et leur non-identité est un SIGNAL,
  jamais une interdiction.

  POURQUOI C'EST NOUVEAU
  ----------------------
  PR-10 exige le quadruplet {source ; convention de mesure ; régime
  d'usage ; porteur de la déclaration}. Il exige que le porteur soit
  NOMMÉ ; il ne dit rien de QUI PEUT L'ÊTRE. Or dans toute la
  littérature suffisantiste lue les 7 et 8 septembre 2026 — Frankfurt,
  Crisp, Casal, Benbaji, Arneson, Meyer & Roser, Gosseries 2011,
  Widerquist 2010, André & Gosseries 2024 — **le porteur de la
  déclaration n'est jamais une variable**. On y discute le niveau du
  seuil, sa métrique, sa combinaison, sa continuité ; jamais qui le
  fixe. De Schutter (A/HRC/56/61) non plus : il connaît l'universalité
  d'ACCÈS, pas celle de DÉCISION.

  ANCRAGE EMPIRIQUE (axiome AX-7, constat daté)
  -------------------------------------------
  · SSA / caisses communes de l'alimentation : « Au-delà de
    l'universalité d'accès, la SSA vise aussi une universalité de la
    PRISE DE DÉCISION : chacun·e doit pouvoir décider, quelle que soit
    sa classe sociale » (*À fond les caisses*, CIVAM, p. 26-27).
    [VÉRIFIÉ]
  · TZCLD : « exhaustivité volontaire », critères de qualité du
    travail (dossier ATD Quart Monde 2015 ; note de juin 2017).
  · Contre-épreuve : la normalisation fait glisser les personnes « du
    statut d'acteurs du projet à celui de publics cibles » (Fretel,
    Higelé, Jany-Catrice, Tantot, *L'Économie politique* 2026/2
    n° 110). [VÉRIFIÉ]

  ⚠️ CE QUE PR-18 NE FAIT PAS
  ---------------------------
  Il **ne prescrit pas** que le seuil soit déclaré par les concernés.
  AX-7 n'établit qu'une POSSIBILITÉ — deux dispositifs — et prescrire à
  partir d'un constat de possibilité serait un [ENGAGEMENT SANS
  SYMÉTRIE]. PR-18 rend la question inscrite et contrôlable, ce que le
  MRC fait partout ailleurs, et rien de plus.

  ⚠️ LA GARDE VIENT DE PR-16, ET ELLE N'A PAS ÉTÉ ÉCRITE POUR CELA
  ----------------------------------------------------------------
  L'objection immédiate à L6 : si le collectif bénéficiaire fixe le
  seuil, qu'est-ce qui l'empêche de se valider lui-même ?
  `autorefutation_n_est_pas_refutation` (PR-16, compilé le 7 septembre)
  rend mal formée l'inscription dont les réfutants admis sont ses
  propres porteurs. Le §4 ci-dessous transpose cette garde au seuil.

  Porteur : Pierre Musseau. Écrit le 8 septembre 2026.
  Lean 4 pur, sans Mathlib, sans import.
-/

namespace ProfRegPR18

/-! ## 1. La déclaration de seuil

Le type des acteurs est laissé **abstrait**, comme dans PR-16 : la
population visée par un seuil de suffisance n'a pas de raison d'être
énumérable, et cette propriété doit pouvoir être déclarée sur le type
plutôt que supposée du modèle. -/

/-- Une déclaration de seuil exhibe, par construction du type, son
    porteur **et** la population à laquelle le seuil s'applique.
    C'est l'invariant de typage — patron de `fraction_exhibe_sa_source`. -/
structure DeclarationDeSeuil (A : Type) where
  enonce : String
  /-- Qui déclare le seuil. Quatrième terme du quadruplet PR-10. -/
  porteurDeLaDeclaration : A
  /-- À qui le seuil s'applique. **Ce champ n'existe pas dans PR-10** :
      c'est l'ajout de PR-18. -/
  populationVisee : List A

/-- Le seuil est déclaré par un membre de la population qu'il vise. -/
def DeclareParLesConcernes {A : Type} (d : DeclarationDeSeuil A) : Prop :=
  d.porteurDeLaDeclaration ∈ d.populationVisee

/-- Le signal — **pas un interdit**. Un seuil déclaré par un tiers
    reste licite ; il est signalé. -/
def SignalTiersDeclarant {A : Type} (d : DeclarationDeSeuil A) : Prop :=
  ¬ DeclareParLesConcernes d

/-- La relation porteur / population est **décidable** dès que les
    acteurs le sont : c'est ce qui rend la question tranchable sur la
    seule inscription. -/
instance instDecidableDeclareParLesConcernes {A : Type} [DecidableEq A]
    (d : DeclarationDeSeuil A) : Decidable (DeclareParLesConcernes d) := by
  unfold DeclareParLesConcernes; infer_instance

instance instDecidableSignalTiersDeclarant {A : Type} [DecidableEq A]
    (d : DeclarationDeSeuil A) : Decidable (SignalTiersDeclarant d) := by
  unfold SignalTiersDeclarant; infer_instance

/-! ## 2. La question est toujours tranchable sur la seule inscription

C'est le contenu réel de PR-18 : non pas que le porteur existe — le
typage le donne — mais que **la relation entre le porteur et la
population est décidée par l'inscription elle-même**, sans recours à
une information extérieure. C'est ce qui la rend contrôlable par un
tiers, donc compatible avec L3. -/

theorem porteur_du_seuil_exhibe_sa_population {A : Type} [DecidableEq A] :
    ∃ f : DeclarationDeSeuil A → Bool,
      ∀ d, f d = true ↔ DeclareParLesConcernes d :=
  -- [B-2, 28/09/2026] Reformulé : l'ancien énoncé `DeclareParLesConcernes d ∨
  -- SignalTiersDeclarant d` était le tiers exclu (forme 2). Le contenu de PR-18 est
  -- la **décidabilité** : une procédure booléenne, fonction de la seule inscription,
  -- tranche la relation porteur / population.
  ⟨fun d => decide (DeclareParLesConcernes d), fun _ => decide_eq_true_iff⟩

/-! [C-4 — RETIRÉ LE 28/09/2026, décision du porteur] `les_deux_cas_s_excluent`
    énonçait ¬(P ∧ ¬P) : `SignalTiersDeclarant d` est défini comme
    `¬ DeclareParLesConcernes d`. Tautologie (forme 1) — sa docstring prétendait
    au contraire éviter une tautologie. L'exclusion des deux cas est dans la
    **définition** du signal ; le tri est porté par l'éponyme reformulé (B-2) et
    par les témoins du §3. Garde de non-régression déclarée : ne pas réintroduire ce théorème sous un autre nom. -/

/-! ## 3. Test de non-vacuité — les deux cas sont peuplés

Un signal qui se déclencherait toujours, ou jamais, ne trierait rien.
On exhibe les deux. -/

/-- Le Comité Citoyen arrête les critères de qualité de l'alimentation
    qui le concernent. -/
def seuilArreteParLesConcernes : DeclarationDeSeuil String :=
  { enonce := "sept critères de qualité de l'alimentation"
  , porteurDeLaDeclaration := "comite-citoyen"
  , populationVisee := ["comite-citoyen", "adherents"] }

/-- Un seuil d'éligibilité posé par une administration sur une
    population dont elle ne fait pas partie. -/
def seuilArreteParUnTiers : DeclarationDeSeuil String :=
  { enonce := "critère d'éligibilité au dispositif"
  , porteurDeLaDeclaration := "administration"
  , populationVisee := ["allocataires"] }

/-- **Témoin de non-vacuité du signal (PR-18) ; un axiome ne se prouve pas.**
    [X-5 — 28/09/2026, décision du porteur] Ce théorème établit que le type
    admet une déclaration arrêtée par les concernés, sur une valeur construite
    par l'auteur. Il n'est **pas** l'ancrage compilé de l'axiome AX-7 : AX-7 est un
    constat daté sur des dispositifs réels (fiche AX-7 du 11/09), qu'aucun témoin
    construit ne peut établir `[RAISONNEMENT AUTORÉFÉRENTIEL évité]`. -/
theorem cas_concernes : DeclareParLesConcernes seuilArreteParLesConcernes := by
  decide

theorem cas_tiers : SignalTiersDeclarant seuilArreteParUnTiers := by
  decide

/-! ## 4. La garde — le déclarant ne peut pas être la liste close des
réfutants

Transposition de `autorefutation_n_est_pas_refutation` (PR-16) au
seuil. C'est ce qui empêche L6 de s'effondrer en auto-validation :
déclarer un seuil est un acte **situé**, le réfuter ne peut pas
l'être. PAL-4 porte sur le second, L6 sur le premier. -/

structure InscriptionDeSeuil (A : Type) where
  declaration : DeclarationDeSeuil A
  /-- `none` = non restreint ; `some l` = liste close des réfutants
      admis. Même convention que PR-16. -/
  refutantsAdmis : Option (List A)

/-- Condition de bonne formation : si la liste des réfutants est close,
    elle ne peut pas être exactement la population qui a déclaré le
    seuil. -/
def BienFormee {A : Type} (i : InscriptionDeSeuil A) : Prop :=
  ∀ l, i.refutantsAdmis = some l → l ≠ i.declaration.populationVisee

/-- **La garde.** Une inscription dont les seuls réfutants admis sont
    la population qui a déclaré le seuil est **mal formée**. -/
theorem declarant_seul_refutant_est_mal_formee {A : Type}
    (i : InscriptionDeSeuil A)
    (h : i.refutantsAdmis = some i.declaration.populationVisee) :
    ¬ BienFormee i := by
  intro hbf
  exact hbf i.declaration.populationVisee h rfl

/-- Et la garde n'interdit pas la déclaration par les concernés : elle
    exige seulement que la réfutation leur échappe. L'inscription
    ci-dessous déclare son seuil par les concernés **et** est bien
    formée, parce que sa réfutation est non restreinte. -/
def inscriptionAdmissible : InscriptionDeSeuil String :=
  { declaration := seuilArreteParLesConcernes
  , refutantsAdmis := none }

theorem declarer_par_les_concernes_reste_admissible :
    DeclareParLesConcernes inscriptionAdmissible.declaration
    ∧ BienFormee inscriptionAdmissible := by
  refine ⟨cas_concernes, ?_⟩
  intro l hl
  simp [inscriptionAdmissible] at hl

/-! ## 5. Gardes -/

/-- **PR-18 ne prescrit pas qui déclare.** Une inscription dont le
    seuil est posé par un tiers peut être bien formée : le signal
    n'emporte aucune sanction. -/
def inscriptionTiersBienFormee : InscriptionDeSeuil String :=
  { declaration := seuilArreteParUnTiers
  , refutantsAdmis := none }

theorem PR18_n_impose_pas_qui_declare :
    SignalTiersDeclarant inscriptionTiersBienFormee.declaration
    ∧ BienFormee inscriptionTiersBienFormee := by
  refine ⟨cas_tiers, ?_⟩
  intro l hl
  simp [inscriptionTiersBienFormee] at hl

/-- **PR-18 ne juge pas le contenu du seuil.** Deux déclarations de
    contenus différents peuvent porter le même statut au regard du
    signal ; le signal porte sur la relation porteur/population, pas
    sur ce qui est déclaré. -/
def memePorteurAutreEnonce : DeclarationDeSeuil String :=
  { seuilArreteParLesConcernes with enonce := "tout autre contenu" }

theorem PR18_ne_juge_pas_le_contenu :
    DeclareParLesConcernes memePorteurAutreEnonce
    ∧ memePorteurAutreEnonce.enonce ≠ seuilArreteParLesConcernes.enonce := by
  exact ⟨by decide, by decide⟩

/-! ## Témoins D-13 (règle NT-ARCH §8ter-bis, R-2) — versés le 28/09/2026

`declarant_seul_refutant_est_mal_formee` est une lecture de `BienFormee`
(R-3). Son hypothèse n'était montrée satisfiable nulle part. Témoin bien formé :
`declarer_par_les_concernes_reste_admissible`. -/

/-- Une inscription concrète dont les seuls réfutants admis sont la population
    déclarante, donc mal formée. -/
theorem PR18_temoin_mal_forme :
    ∃ i : InscriptionDeSeuil String,
      i.refutantsAdmis = some i.declaration.populationVisee
      ∧ ¬ BienFormee i :=
  ⟨{ declaration := seuilArreteParLesConcernes,
     refutantsAdmis := some seuilArreteParLesConcernes.populationVisee },
   rfl, declarant_seul_refutant_est_mal_formee _ rfl⟩

end ProfRegPR18
