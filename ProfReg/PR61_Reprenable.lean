import ProfReg.PR16_RefutationTiers
/-
  PR-61 · Le reprenable (AX-4, quatrième état)
  ============================================
  Porteur : Pierre Musseau. Écrit le 17 novembre 2026, sur décision du
  porteur du même jour (fichier d'état, décision n° 65), à la suite de la
  décision n° 64 qui aligne AX-4 sur la définition stricte du reprenable
  (Annexe méthodologique §A.15.0 ; fiche AX-4, colonne A).
  Lean 4 pur, sans Mathlib. Importe `ProfReg.PR16_RefutationTiers`, pour
  l'homonymie seulement (ci-dessous).
  Modifié le 17 novembre 2026, sur décision n° 69 du porteur : la garde de
  la décision n° 66 contre le rétrécissement du périmètre après coup est
  codée (`perimetreAvant`) ; la version précédente est conservée dans
  l'instantané `ProfReg_Lean_2026-11-17_623thm`.
  Modifié le 17 novembre 2026, sur décision n° 70 du porteur : la
  contestabilité du périmètre déclaré est codée (`perimetreContestable`,
  quatre éléments) et entre dans la condition (1) ; la version précédente
  est conservée dans l'instantané `ProfReg_Lean_2026-11-17_625thm`.

  LA DÉFINITION (AX-4 amendé)
  ---------------------------
  Est reprenable une inscription dont ceux qu'elle concerne obtiennent, ou
  peuvent obtenir, eux-mêmes ou par un représentant institué, la révision
  de l'inscription ou de l'instrument qui l'a produite (catégorie, critère,
  seuil), sous quatre conditions cumulatives :
    (1) tous les concernés du périmètre déclaré sont parties à la
        révision, le périmètre étant déclaré avant la demande et
        contestable ;
    (2) le porteur ne décide pas seul ;
    (3) la procédure de révision est inscrite à l'avance ;
    (4) la révision peut changer les termes de l'instrument et laisse une
        trace.
  Ne sont pas des reprises : la révision par le normalisateur ou par le
  porteur seul ; la consultation, où les concernés sont entendus mais où le
  porteur tranche ; la correction d'une erreur dans les termes.

  CE QUE LE FICHIER ÉTABLIT
  -------------------------
  La FORME de la définition : chacune des quatre conditions est nécessaire,
  et les trois cas exclus par l'énoncé échouent. Les conditions (1) et (2)
  ont leur pendant dans PR-57 pour le constat d'enquête
  (`sans_les_concernes_pas_de_constat`, `le_porteur_ne_s_atteste_pas`) ;
  les conditions (3) et (4) n'avaient aucun théorème. La condition (1) est
  la conjonction de trois tests : `perimetreAvant` (décision n° 69),
  `perimetreContestable` (décision n° 70) et `concernesParties`.

  PORTÉE DE LA DATE DU PÉRIMÈTRE (décision n° 69)
  -----------------------------------------------
  La date protège contre un rétrécissement APRÈS la demande, et contre lui
  seulement : un porteur qui déclare d'avance un périmètre étroit satisfait
  `perimetreAvant`. Ce cas relève de la contestabilité du périmètre.

  CONTESTABILITÉ DU PÉRIMÈTRE (décision n° 70)
  --------------------------------------------
  Un périmètre déclaré est contestable s'il réunit quatre éléments,
  homologues des trois clauses de PR-16 (tiers, lieu, reprise), auxquelles
  s'ajoute un critère de recevabilité :
    (a) une voie exerçable par un exclu concerné, ou par un tiers habilité
        à agir pour lui (`voieExercable`) ;
    (b) un lieu de dépôt hors du contrôle de celui qui a tracé le
        périmètre et du porteur (`lieuHorsControle`) ;
    (c) un critère de recevabilité rattaché à l'objet déclaré de
        l'inscription (`recevabiliteObjet`) ;
    (d) un effet possible sur l'écriture du périmètre (`effetEcriture`).
  La contestabilité arrête la régression du « périmètre du périmètre » :
  on ne demande pas que le périmètre soit lui-même reprenable, mais qu'un
  exclu, ou un tiers habilité pour lui, puisse le contester ailleurs que
  devant celui qui l'a tracé, au nom de l'objet déclaré. Le critère (c)
  fixe QUI peut contester parmi des exclus non énumérables (PR-16) : celui
  qui se rattache à l'objet. La contestation du périmètre ne rouvre pas
  l'objet lui-même, qui relève d'une autre procédure (non codée ici).
  Le tiers habilité (a) couvre les exclus qui ne peuvent pas déposer
  eux-mêmes (milieux, entités naturelles, générations à venir) : il agit
  pour eux sans en être ni créancier ni représentant institué.
  Lecture conservatrice de (b) : un lieu dont le traceur ou le porteur
  est l'un des teneurs n'est pas hors de leur contrôle.

  HOMONYMIE AVEC PR-16
  --------------------
  `refutation_exige_une_reprise` (PR-16) porte sur la « reprise » au sens
  de Longino (troisième condition : une objection reçue produit un effet
  sur l'écriture, champ `repriseInscrite`). Ce n'est PAS le quatrième état
  d'AX-4 : une contestation qui produit un effet sur l'écriture sans
  réviser les termes de l'instrument relève du convocable ou de
  l'opposable. Le nom compilé de PR-16 est conservé ; le raccord d'AX-4
  passe désormais par PR-61.

  CE QUE LE FICHIER NE FAIT PAS
  -----------------------------
  · Il ne dit pas qu'une révision a lieu : `reprenable` qualifie les
    conditions d'une révision possible (« obtiennent ou peuvent obtenir »).
  · Il ne vérifie pas que les décideurs, représentants et dates déclarés
    sont exacts : ce sont des déclarations, supposées sincères.
  · Il ne vérifie pas qu'une voie de contestation a été exercée, ni
    qu'elle aboutit : `perimetreContestable` qualifie une possibilité.
  · Il ne qualifie pas le critère de recevabilité : qu'il soit rattaché à
    l'objet est une déclaration, supposée sincère.
  · Il ne code pas la contestation de l'objet lui-même (autre procédure).
  · Il ne code ni la gradation des quatre états d'AX-4, ni leur
    non-implication mutuelle (fiche AX-4, colonne C).
  · Il ne dit pas qu'un dispositif reprenable est meilleur : AX-4 est
    descriptif.
-/

namespace ProfRegPR61

/-! ## 1. Le modèle -/

/-- Une voie de contestation du périmètre déclaré (décision n° 70). -/
structure VoiePerimetre where
  /-- Celui qui a tracé le périmètre. -/
  traceur           : Nat
  /-- Qui peut déposer une contestation : `none` = voie ouverte à tout
      exclu qui se rattache à l'objet ; `some l` = liste close. -/
  deposants         : Option (List Nat)
  /-- Tiers habilités à agir pour un exclu qui ne peut pas déposer. -/
  habilites         : List Nat
  /-- Qui tient le lieu de dépôt ; `[]` = aucun lieu. -/
  lieuTenuPar       : List Nat
  /-- Le critère de recevabilité est rattaché à l'objet déclaré. -/
  recevabiliteObjet : Bool
  /-- Une contestation reçue peut changer l'écriture du périmètre. -/
  effetEcriture     : Bool
  deriving DecidableEq, Repr

/-- Une révision, demandée ou possible, d'une inscription ou de
    l'instrument qui l'a produite. Les personnes sont désignées par leur DID. -/
structure Revision where
  /-- Porteur de l'inscription. -/
  porteur       : Nat
  /-- Personnes concernées (périmètre déclaré). -/
  concernes     : List Nat
  /-- Date de déclaration du périmètre ; `none` : jamais déclaré. -/
  perimetreLe   : Option Nat
  /-- Voie de contestation du périmètre ; `none` : aucune (décision n° 70). -/
  voie          : Option VoiePerimetre
  /-- Représentants institués : (concerné, représentant). -/
  representants : List (Nat × Nat)
  /-- Ceux qui tranchent la révision. -/
  decideurs     : List Nat
  /-- Date d'inscription de la procédure de révision ; `none` : aucune. -/
  procedureLe   : Option Nat
  /-- Date de la demande de révision. -/
  saisine       : Nat
  /-- La révision peut changer les termes (catégorie, critère, seuil). -/
  changeTermes  : Bool
  /-- La révision laisse une trace. -/
  trace         : Bool
  deriving DecidableEq, Repr

/-- Un concerné est partie à la révision : il décide, ou son représentant
    institué décide. -/
def partie (r : Revision) (c : Nat) : Bool :=
  r.decideurs.contains c
    || r.representants.any (fun p => p.1 == c && r.decideurs.contains p.2)

/-- Les concernés sont parties (périmètre non vide). -/
def concernesParties (r : Revision) : Bool :=
  !r.concernes.isEmpty && r.concernes.all (partie r)

/-- Le périmètre est déclaré avant la demande (décision n° 69). -/
def perimetreAvant (r : Revision) : Bool :=
  match r.perimetreLe with
  | some d => decide (d < r.saisine)
  | none   => false

/-- (a) La voie est exerçable par un exclu concerné (hors périmètre, ni
    traceur ni porteur), ou par un tiers habilité à agir pour lui. -/
def voieExercable (r : Revision) (v : VoiePerimetre) : Bool :=
  (match v.deposants with
   | none   => true
   | some l => l.any (fun a => !r.concernes.contains a && a != v.traceur && a != r.porteur))
  || v.habilites.any (fun h => h != v.traceur && h != r.porteur)

/-- (b) Le lieu de dépôt existe et n'est tenu ni par le traceur ni par le
    porteur (lecture conservatrice). -/
def lieuHorsControle (r : Revision) (v : VoiePerimetre) : Bool :=
  !v.lieuTenuPar.isEmpty && v.lieuTenuPar.all (fun c => c != v.traceur && c != r.porteur)

/-- **Le périmètre déclaré est contestable** (décision n° 70) : les quatre
    éléments (a) à (d), cumulatifs. -/
def perimetreContestable (r : Revision) : Bool :=
  match r.voie with
  | none   => false
  | some v => voieExercable r v && lieuHorsControle r v && v.recevabiliteObjet && v.effetEcriture

/-- **Condition 1** — tous les concernés du périmètre déclaré, déclaré avant
    la demande et contestable, sont parties. -/
def condition1 (r : Revision) : Bool :=
  perimetreAvant r && perimetreContestable r && concernesParties r

/-- **Condition 2** — le porteur ne décide pas seul. -/
def porteurPasSeul (r : Revision) : Bool :=
  r.decideurs.any (fun d => d != r.porteur)

/-- **Condition 3** — la procédure est inscrite avant la demande. -/
def procedureAvant (r : Revision) : Bool :=
  match r.procedureLe with
  | some d => decide (d < r.saisine)
  | none   => false

/-- **Condition 4** — la révision peut changer les termes et laisse une trace. -/
def termesEtTrace (r : Revision) : Bool :=
  r.changeTermes && r.trace

/-- **Le reprenable** : les quatre conditions, cumulatives. -/
def reprenable (r : Revision) : Bool :=
  condition1 r && porteurPasSeul r && procedureAvant r && termesEtTrace r

/-! ## 2. Chaque condition est nécessaire -/

/-- **PR-61 (1) — sans les concernés, pas de reprise.** -/
theorem sans_les_concernes_pas_de_reprise (r : Revision)
    (h : concernesParties r = false) : reprenable r = false := by
  simp [reprenable, condition1, h]

/-- **PR-61 (1 bis) — un périmètre déclaré après la demande, ou jamais, ne
    fait pas une reprise** (décision n° 69). -/
theorem sans_perimetre_declare_a_l_avance_pas_de_reprise (r : Revision)
    (h : ∀ d, r.perimetreLe = some d → r.saisine ≤ d) : reprenable r = false := by
  cases hp : r.perimetreLe with
  | none => simp [reprenable, condition1, perimetreAvant, hp]
  | some d =>
    have := h d hp
    simp [reprenable, condition1, perimetreAvant, hp]
    omega

/-- **PR-61 (2) — le porteur seul ne reprend pas.** Couvre la consultation :
    les concernés sont entendus, le porteur tranche. -/
theorem le_porteur_seul_ne_reprend_pas (r : Revision)
    (h : r.decideurs = [r.porteur]) : reprenable r = false := by
  simp [reprenable, porteurPasSeul, h]

/-- **PR-61 (3) — une procédure inscrite après la demande, ou jamais, ne
    fait pas une reprise.** -/
theorem sans_procedure_inscrite_a_l_avance_pas_de_reprise (r : Revision)
    (h : ∀ d, r.procedureLe = some d → r.saisine ≤ d) : reprenable r = false := by
  cases hp : r.procedureLe with
  | none => simp [reprenable, procedureAvant, hp]
  | some d =>
    have := h d hp
    simp [reprenable, procedureAvant, hp]
    omega

/-- **PR-61 (4) — la correction d'une erreur n'est pas une reprise** : une
    révision qui ne peut pas changer les termes de l'instrument ne reprend
    rien. -/
theorem la_correction_d_erreur_n_est_pas_une_reprise (r : Revision)
    (h : r.changeTermes = false) : reprenable r = false := by
  simp [reprenable, termesEtTrace, h]

/-- **PR-61 (5) — sans trace, pas de reprise.** -/
theorem sans_trace_pas_de_reprise (r : Revision)
    (h : r.trace = false) : reprenable r = false := by
  simp [reprenable, termesEtTrace, h]

/-! ## 3. Les cas exclus par l'énoncé -/

/-- **PR-61 (6) — la révision par le normalisateur n'est pas une reprise** :
    s'il tranche seul, n'est pas un concerné et ne représente personne, un
    concerné au moins n'est pas partie. -/
theorem la_revision_par_le_normalisateur_n_est_pas_une_reprise (r : Revision) (n c : Nat)
    (hd : r.decideurs = [n]) (hc : c ∈ r.concernes) (hn : c ≠ n)
    (hrep : ∀ p ∈ r.representants, p.2 ≠ n) : reprenable r = false := by
  apply sans_les_concernes_pas_de_reprise
  have hp : partie r c = false := by
    have e1 : r.decideurs.contains c = false := by
      rw [hd]; simp [hn]
    have e2 : ∀ l : List (Nat × Nat), (∀ q ∈ l, q.2 ≠ n) →
        l.any (fun q => q.1 == c && r.decideurs.contains q.2) = false := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons q l ih =>
        intro h
        have hq : r.decideurs.contains q.2 = false := by
          rw [hd]; simp [h q (List.mem_cons_self ..)]
        rw [List.any_cons, hq, Bool.and_false, Bool.false_or]
        exact ih (fun x hx => h x (List.mem_cons_of_mem q hx))
    unfold partie; rw [e1, e2 _ hrep]; rfl
  have hall : ∀ l : List Nat, c ∈ l → l.all (partie r) = false := by
    intro l h; induction h with
    | head => rw [List.all_cons, hp, Bool.false_and]
    | tail _ _ ih => rw [List.all_cons, ih, Bool.and_false]
  simp [concernesParties, hall _ hc]

/-- **PR-61 (7) — un représentant institué rend le concerné partie**, sans
    que le concerné décide lui-même (représentation des absents). -/
theorem un_representant_institue_rend_le_concerne_partie (r : Revision) (c p : Nat)
    (hr : (c, p) ∈ r.representants) (hd : p ∈ r.decideurs) : partie r c = true := by
  have h1 : r.decideurs.contains p = true := List.contains_iff_mem.mpr hd
  have hany : ∀ l : List (Nat × Nat), (c, p) ∈ l →
      l.any (fun q => q.1 == c && r.decideurs.contains q.2) = true := by
    intro l h; induction h with
    | head =>
      rw [List.any_cons]
      show ((c == c) && r.decideurs.contains p || _) = true
      rw [show (c == c) = true from decide_eq_true rfl, h1]; rfl
    | tail _ _ ih => rw [List.any_cons, ih, Bool.or_true]
  unfold partie; rw [hany _ hr, Bool.or_true]

/-! ## 3 bis. La contestabilité du périmètre (décision n° 70) -/

/-- **PR-61 (8) — sans voie de contestation, pas de reprise** : un périmètre
    déclaré d'avance mais incontestable ne satisfait pas la condition (1). -/
theorem sans_voie_pas_de_reprise (r : Revision)
    (h : r.voie = none) : reprenable r = false := by
  simp [reprenable, condition1, perimetreContestable, h]

/-- **PR-61 (9) — un lieu tenu par celui qui a tracé le périmètre ne suffit
    pas** : la contestation se dépose hors de son contrôle. -/
theorem un_lieu_tenu_par_le_traceur_ne_suffit_pas (r : Revision) (v : VoiePerimetre)
    (hv : r.voie = some v) (ht : v.traceur ∈ v.lieuTenuPar) : reprenable r = false := by
  have h2 : v.lieuTenuPar.all (fun c => c != v.traceur && c != r.porteur) = false := by
    rw [Bool.eq_false_iff]; intro h
    rw [List.all_eq_true] at h
    have := h _ ht
    simp at this
  simp [reprenable, condition1, perimetreContestable, hv, lieuHorsControle, h2]

/-- **PR-61 (10) — un lieu tenu par le porteur ne suffit pas non plus.** -/
theorem un_lieu_tenu_par_le_porteur_ne_suffit_pas (r : Revision) (v : VoiePerimetre)
    (hv : r.voie = some v) (hp : r.porteur ∈ v.lieuTenuPar) : reprenable r = false := by
  have h2 : v.lieuTenuPar.all (fun c => c != v.traceur && c != r.porteur) = false := by
    rw [Bool.eq_false_iff]; intro h
    rw [List.all_eq_true] at h
    have := h _ hp
    simp at this
  simp [reprenable, condition1, perimetreContestable, hv, lieuHorsControle, h2]

/-- **PR-61 (11) — sans critère de recevabilité rattaché à l'objet, pas de
    reprise** : la voie qui ne dit pas quel exclu est recevable, au nom de
    l'objet déclaré, se réduit à une faculté laissée au teneur du lieu. -/
theorem sans_critere_rattache_a_l_objet_pas_de_reprise (r : Revision) (v : VoiePerimetre)
    (hv : r.voie = some v) (h : v.recevabiliteObjet = false) : reprenable r = false := by
  simp [reprenable, condition1, perimetreContestable, hv, h]

/-- **PR-61 (12) — sans effet possible sur l'écriture du périmètre, pas de
    reprise** : homologue de `refutation_exige_une_reprise` (PR-16). -/
theorem sans_effet_sur_l_ecriture_pas_de_reprise (r : Revision) (v : VoiePerimetre)
    (hv : r.voie = some v) (h : v.effetEcriture = false) : reprenable r = false := by
  simp [reprenable, condition1, perimetreContestable, hv, h]

/-- **PR-61 (13) — seuls les inclus ne contestent pas leur périmètre** : une
    voie réservée aux concernés déjà dans le périmètre, sans tiers habilité,
    n'ouvre rien aux exclus (homologue de `autorefutation_n_est_pas_refutation`,
    PR-16). -/
theorem seuls_les_inclus_ne_contestent_pas_leur_perimetre (r : Revision) (v : VoiePerimetre)
    (hv : r.voie = some v) (hd : v.deposants = some r.concernes) (hh : v.habilites = []) :
    reprenable r = false := by
  have hx : r.concernes.any (fun a => !r.concernes.contains a && a != v.traceur && a != r.porteur)
      = false := by
    rw [Bool.eq_false_iff]; intro h
    rw [List.any_eq_true] at h
    obtain ⟨a, ha, hx⟩ := h
    simp at hx
    exact hx.1.1 ha
  have hve : voieExercable r v = false := by
    unfold voieExercable
    rw [hd, hh]
    simp only [List.any_nil, Bool.or_false]
    exact hx
  simp [reprenable, condition1, perimetreContestable, hv, hve]

/-- **PR-61 (14) — un tiers habilité ouvre la voie** à des exclus qui ne
    peuvent pas déposer eux-mêmes (aucun déposant admis), pourvu qu'il ne
    soit ni le traceur ni le porteur. -/
theorem un_tiers_habilite_ouvre_la_voie (r : Revision) (v : VoiePerimetre) (h : Nat)
    (hd : v.deposants = some []) (hh : h ∈ v.habilites)
    (h1 : h ≠ v.traceur) (h2 : h ≠ r.porteur) : voieExercable r v = true := by
  have : v.habilites.any (fun x => x != v.traceur && x != r.porteur) = true := by
    rw [List.any_eq_true]
    exact ⟨h, hh, by simp [h1, h2]⟩
  simp [voieExercable, hd, this]

/-- **PR-61 (15) — une liste close de déposants laisse un exclu sans voie** :
    le patron `liste_close_exclut_toujours` de PR-16, appliqué aux déposants ;
    d'où le tiers habilité, ou la voie ouverte. -/
theorem une_liste_close_de_deposants_laisse_un_exclu_sans_voie (v : VoiePerimetre)
    (l : List Nat) (_hd : v.deposants = some l) : ∃ a : Nat, a ∉ l :=
  ProfRegPR16.nat_non_enumerable l

/-! ## 4. Témoin et lecture -/

/-- Une voie de contestation type (décision n° 70) : périmètre tracé par 1,
    voie ouverte à tout exclu qui se rattache à l'objet, aucun tiers habilité,
    lieu tenu par 9 (un juge), critère rattaché à l'objet, effet sur
    l'écriture. -/
def voieType : VoiePerimetre :=
  ⟨1, none, [], [9], true, true⟩

/-- Une révision reprenable : concernés 3 et 4, périmètre déclaré en 2019 et
    contestable par la voie type, 4 représenté par 5 ; décideurs 3 et 5 ;
    porteur 1 ; procédure inscrite en 2020, demande en 2026 ; termes
    révisables ; trace. -/
def revisionType : Revision :=
  ⟨1, [3, 4], some 2019, some voieType, [(4, 5)], [3, 5], some 2020, 2026, true, true⟩

/-- **Témoin discriminant** : la révision type est reprenable ; chacune des
    quatre conditions retirée seule la fait échouer, et la condition (1) par
    l'un ou l'autre de ses trois tests (décision n° 70 : le troisième). -/
theorem reprenable_temoin_discriminant :
    reprenable revisionType = true
  ∧ reprenable { revisionType with representants := [] } = false
  ∧ reprenable { revisionType with perimetreLe := some 2026 } = false
  ∧ reprenable { revisionType with voie := none } = false
  ∧ reprenable { revisionType with decideurs := [1] } = false
  ∧ reprenable { revisionType with procedureLe := some 2026 } = false
  ∧ reprenable { revisionType with changeTermes := false } = false := by
  decide

/-- **Portée de la date** (décision n° 69) : un périmètre étroit, déclaré
    d'avance, satisfait le test de la date. Ici le concerné 4 est retiré du
    périmètre en 2019, avant la demande : la révision reste reprenable, parce
    que le périmètre reste contestable par la voie type. La date ne garde que
    contre le rétrécissement après coup ; la contestabilité ne fixe pas le
    bon périmètre, elle ouvre une voie aux exclus (décision n° 70). -/
theorem la_date_n_empeche_pas_un_perimetre_etroit :
    reprenable { revisionType with concernes := [3], representants := [] } = true := by
  decide

/-- **Témoin de la contestabilité** (décision n° 70) : la voie type rend le
    périmètre contestable ; chacun des quatre éléments retiré seul le rend
    incontestable — voie réservée aux inclus, aucun lieu, lieu tenu par le
    traceur, critère non rattaché à l'objet, aucun effet sur l'écriture. -/
theorem contestable_temoin_discriminant :
    perimetreContestable revisionType = true
  ∧ perimetreContestable { revisionType with voie := some { voieType with deposants := some [3, 4] } } = false
  ∧ perimetreContestable { revisionType with voie := some { voieType with lieuTenuPar := [] } } = false
  ∧ perimetreContestable { revisionType with voie := some { voieType with lieuTenuPar := [1] } } = false
  ∧ perimetreContestable { revisionType with voie := some { voieType with recevabiliteObjet := false } } = false
  ∧ perimetreContestable { revisionType with voie := some { voieType with effetEcriture := false } } = false := by
  decide

/-- **Un périmètre étroit et incontestable ne passe pas** (décision n° 70) :
    le cas que la date laissait passer (`la_date_n_empeche_pas_un_perimetre_etroit`)
    échoue dès que la voie de contestation manque. -/
theorem un_perimetre_etroit_non_contestable_ne_passe_pas :
    reprenable { revisionType with concernes := [3], representants := [], voie := none } = false := by
  decide

/-- **Lecture** : le périmètre est contestable exactement quand les quatre
    éléments sont réunis (décision n° 70). -/
theorem perimetre_contestable_ssi_quatre_elements (r : Revision) (v : VoiePerimetre)
    (hv : r.voie = some v) :
    perimetreContestable r = true ↔
      voieExercable r v = true ∧ lieuHorsControle r v = true
        ∧ v.recevabiliteObjet = true ∧ v.effetEcriture = true := by
  simp [perimetreContestable, hv, Bool.and_eq_true, and_assoc]

/-- **Lecture** : le reprenable est exactement la conjonction des quatre
    conditions. -/
theorem reprenable_ssi_quatre_conditions (r : Revision) :
    reprenable r = true ↔
      condition1 r = true ∧ porteurPasSeul r = true
        ∧ procedureAvant r = true ∧ termesEtTrace r = true := by
  simp [reprenable, Bool.and_eq_true, and_assoc]

end ProfRegPR61
