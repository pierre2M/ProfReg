/-!
# PR-31 — Bonne formation déclarative : S-P-I, ancrage T, « sans objet », P7

28 septembre 2026. Décision du porteur (groupe C de l'audit du 26/09, lot C-γ) :
verser C-7, C-10, C-11 et C-12 (P7 seul), **chacun avec le régime de défaut que
le set lui donne** :

| | Règle (set) | Défaut |
|---|---|---|
| C-7 | NT-G5, A-TÉTRA-3 (21/09) : S, P, I de `C-MILIEU-VECU` | **marqueur** `[INSCRIPTION DE MILIEU SANS INTERPRÈTE]` |
| C-10 | NT-ARCH §8.5 (19/09 ; élargi D7, 07/10) : ancrage d'une écriture T, un par côté pour une écriture duale | **refus** |
| C-11 | Annexe H §H (arbitrages 2-3, 26/09) : « sans objet » motivé | **refus** (≡ `NONDECLARE`) |
| C-12 | NT-ARCH §4.2bis.3 (P7 corrigée) : `dimension_pouvoir` | **mal formée**, phase DÉLIBÉRATION |

P5 (`INSTRUMENT_HOTE_NON_DECLARE`) et P2 (`C-CLOTURE-ACCES`) sont **écartés** :
signaux sans règle d'effet précise (forme 3 au sens de D-13).

`[DÉCOUPLAGE DÉCLARÉ]` Un théorème de bonne formation **n'éprouve pas** un
instrument : il établit qu'il trie, non qu'il sert sur un corpus.
Identités codées par `Nat` (pas de `String`, règle des deux portes). Lean pur.
-/

namespace ProfRegPR31

/-! ## 1. C-7 — S, P, I de `C-MILIEU-VECU` (A-TÉTRA-3) -/

structure InscriptionMilieu where
  declarant       : Nat
  modeMetabolique : Option Nat   -- S
  appelEntendu    : Option Nat   -- P
  interprete      : Option Nat   -- I
  deriving DecidableEq, Repr

def bienFormeeMilieu (i : InscriptionMilieu) : Bool :=
  i.modeMetabolique.isSome && i.appelEntendu.isSome && i.interprete.isSome

/-- Le défaut **propre à l'extension** : S et P renseignés, I manquant. -/
def marqueurSansInterprete (i : InscriptionMilieu) : Bool :=
  i.modeMetabolique.isSome && i.appelEntendu.isSome && i.interprete.isNone

/-- **Le marqueur se lève exactement sur l'interprète manquant**, S et P
    renseignés (caractérisation, patron PR-8 du 28/09). -/
theorem le_marqueur_de_milieu_se_leve_exactement_sur_l_interprete_manquant
    (i : InscriptionMilieu) :
    marqueurSansInterprete i = true ↔
      (i.modeMetabolique.isSome = true ∧ i.appelEntendu.isSome = true ∧ i.interprete = none) := by
  cases i with
  | mk d s p it => cases s <;> cases p <;> cases it <;> simp [marqueurSansInterprete]

/-- **Témoin discriminant** : même S et P ; avec I, bien formée ; sans I, mal
    formée **et marquée** (marqueur, jamais sanction). -/
theorem trois_termes_temoin_discriminant :
    bienFormeeMilieu ⟨0, some 1, some 2, some 3⟩ = true
  ∧ bienFormeeMilieu ⟨0, some 1, some 2, none⟩ = false
  ∧ marqueurSansInterprete ⟨0, some 1, some 2, none⟩ = true := by
  decide

/-- **L'interprète ne se déduit pas du déclarant** dans le modèle : une
    inscription bien formée dont l'interprète n'est pas le déclarant. Cela ne
    lève pas la condition de réfutation d'A-TÉTRA-3, qui est empirique
    (« dans tous les cas ») ; cela établit que le champ n'est pas redondant
    **par construction**. -/
theorem l_interprete_ne_se_deduit_pas_du_declarant :
    ∃ i : InscriptionMilieu, bienFormeeMilieu i = true ∧ i.interprete ≠ some i.declarant :=
  ⟨⟨0, some 1, some 2, some 3⟩, rfl, by decide⟩

/-! ## 2. C-10 — ancrage d'une écriture T (NT-ARCH §8.5, 19/09 ; élargi D7, 07/10/2026) -/

/-- L'ancrage déclaré d'UN côté d'écriture. -/
structure EcritureT where
  traduction  : Option Nat   -- `traduction_uri_ref`
  communalite : Option Nat   -- `inscription_communalite_uri_ref`
  deriving DecidableEq, Repr

/-- Un côté est ancré s'il porte au moins un ancrage déclaré. Défaut : refus.
    Le registre de communalité est une modalité d'ancrage, pour les entités ou
    concernés sans comptabilité admise (réparation du 19/09). -/
def ancree (e : EcritureT) : Bool :=
  e.traduction.isSome || e.communalite.isSome

/-- **Décision du porteur D7 (b), 07/10/2026.** Un côté d'écriture duale : un
    teneur identifié et l'ancrage qu'il déclare. Remplace le booléen `duale`
    (sans teneurs) du 28/09, qui exigeait cumulativement une traduction et une
    inscription de communalité et refusait ainsi deux comptabilités tenues
    (banque / emprunteur, PR-35 ; AX-15). `teneur` a le type de
    `ProfRegPR35.Entite` (`Nat`). -/
structure CoteDuale where
  teneur  : Nat
  ancrage : EcritureT
  deriving DecidableEq, Repr

/-- **Ancrage d'une écriture duale** (NT-ARCH §8.5.0, élargi le 07/10/2026) :
    deux registres tenus par des teneurs identifiés et distincts, chaque côté
    portant son ancrage déclaré — traduction comptable ou inscription de
    communalité, indifféremment. -/
def ancreeDuale (a b : CoteDuale) : Bool :=
  !(a.teneur == b.teneur) && ancree a.ancrage && ancree b.ancrage

/-- **Sans aucun ancrage, refusée** — « un typage qui ne qualifie rien ». -/
theorem sans_ancrage_refusee (e : EcritureT)
    (h₁ : e.traduction = none) (h₂ : e.communalite = none) : ancree e = false := by
  simp [ancree, h₁, h₂]

/-- **Le registre de communalité suffit** — la réparation du 19/09 : une
    écriture de communalité, sans traduction R, est ancrée. -/
theorem le_registre_de_communalite_suffit :
    ancree ⟨none, some 1⟩ = true := by
  decide

/-- **Ancrée simple ⇏ ancrée duale** : un seul ancrage suffit à un côté, pas
    à une écriture duale dont l'autre côté n'est pas ancré (un par côté). -/
theorem la_duale_exige_un_ancrage_par_cote :
    ancree ⟨some 1, none⟩ = true
    ∧ ancreeDuale ⟨0, ⟨some 1, none⟩⟩ ⟨1, ⟨none, none⟩⟩ = false := by
  decide

/-- Lecture de la définition (R-3) — licite parce que `ancreeDuale`
    discrimine : `deux_comptabilites_tenues_ancrent_une_duale` contre
    `la_duale_exige_un_ancrage_par_cote` et `un_seul_teneur_pas_de_duale`. -/
theorem ancree_duale_ssi (a b : CoteDuale) :
    ancreeDuale a b = true ↔
      (a.teneur == b.teneur) = false ∧ ancree a.ancrage = true ∧ ancree b.ancrage = true := by
  unfold ancreeDuale
  cases a.teneur == b.teneur <;> cases ancree a.ancrage <;> cases ancree b.ancrage <;> decide

/-- **D7 (b) — deux comptabilités tenues ancrent une écriture duale** :
    le couple banque / emprunteur de PR-35 (AX-15) est admis. -/
theorem deux_comptabilites_tenues_ancrent_une_duale :
    ancreeDuale ⟨0, ⟨some 1, none⟩⟩ ⟨1, ⟨some 2, none⟩⟩ = true := by
  decide

/-- **D7 (b) — le registre de communalité est une modalité d'ancrage** : il
    ancre un côté face à une comptabilité tenue, ou face à un autre registre
    de communalité. -/
theorem le_registre_de_communalite_ancre_un_cote :
    ancreeDuale ⟨0, ⟨some 1, none⟩⟩ ⟨1, ⟨none, some 2⟩⟩ = true
    ∧ ancreeDuale ⟨0, ⟨none, some 1⟩⟩ ⟨1, ⟨none, some 2⟩⟩ = true := by
  decide

/-- **Un seul teneur ne fait pas d'écriture duale**, même ancré des deux
    côtés (AX-15 : deux registres tenus indépendamment). -/
theorem un_seul_teneur_pas_de_duale :
    ancreeDuale ⟨0, ⟨some 1, none⟩⟩ ⟨0, ⟨some 2, none⟩⟩ = false := by
  decide

/-! ## 3. C-11 — « sans objet » non motivé (Annexe H, gabarit R211-9-7) -/

inductive Exigence where
  | G1 | G2 | G3 | G4
  deriving DecidableEq, Repr

inductive Motif where
  | titulaireNonHumain | autre (n : Nat)
  deriving DecidableEq, Repr

inductive ValeurGabarit where
  | satisfaite | partielle | nonSatisfaite
  | sansObjetMotive (m : Option Motif)
  | nondeclare
  deriving DecidableEq, Repr

inductive Effet where
  | admise | refusee
  deriving DecidableEq, Repr

/-- G4 n'admet pas le motif « titulaire non humain ». -/
def motifAdmis : Exigence → Motif → Bool
  | .G4, .titulaireNonHumain => false
  | _, _                     => true

def effet (g : Exigence) : ValeurGabarit → Effet
  | .nondeclare                 => .refusee
  | .sansObjetMotive none       => .refusee
  | .sansObjetMotive (some m)   => if motifAdmis g m then .admise else .refusee
  | _                           => .admise

/-- Le motif est réfutable par tout tiers ; réfuté, la valeur devient `NON_SATISFAITE`. -/
def requalifier (v : ValeurGabarit) (refute : Bool) : ValeurGabarit :=
  match v with
  | .sansObjetMotive (some _) => if refute then .nonSatisfaite else v
  | _                         => v

/-- **Un « sans objet » sans motif est un `NONDECLARE` renommé** : même effet, refus. -/
theorem sans_objet_sans_motif_est_un_nondeclare_renomme (g : Exigence) :
    effet g (.sansObjetMotive none) = effet g .nondeclare
  ∧ effet g .nondeclare = .refusee := by
  cases g <;> exact ⟨rfl, rfl⟩

/-- **Le motif réfuté requalifie la valeur en `NON_SATISFAITE`** ; non réfuté, il tient. -/
theorem le_motif_refute_requalifie (m : Motif) :
    requalifier (.sansObjetMotive (some m)) true = .nonSatisfaite
  ∧ requalifier (.sansObjetMotive (some m)) false = .sansObjetMotive (some m) := by
  exact ⟨rfl, rfl⟩

/-- **G4 n'admet pas le motif « titulaire non humain »** ; G1 l'admet. -/
theorem G4_n_admet_pas_le_titulaire_non_humain :
    effet .G4 (.sansObjetMotive (some .titulaireNonHumain)) = .refusee
  ∧ effet .G1 (.sansObjetMotive (some .titulaireNonHumain)) = .admise := by
  decide

/-! ## 4. C-12 — P7 corrigée : `dimension_pouvoir` est une liste (NT-ARCH §4.2bis) -/

inductive Dimension where
  | avec | sur | de
  deriving DecidableEq, Repr

structure AttributionPorteur where
  representeDesMembres : Option Bool
  membres              : List Nat
  dimensions           : List Dimension
  deriving DecidableEq, Repr

/-- §4.2bis.3. À défaut : `PORTEUR_COLLECTIF_SANS_DIMENSION_DECLAREE`, mal formée,
    phase DÉLIBÉRATION (non modélisée ici). -/
def bienFormeeP7 (a : AttributionPorteur) : Bool :=
  match a.representeDesMembres with
  | none       => false
  | some false => true
  | some true  => !a.membres.isEmpty && !a.dimensions.isEmpty

/-- **Représentant sans dimension déclarée : mal formée.** -/
theorem representant_sans_dimension_mal_forme (a : AttributionPorteur)
    (h₁ : a.representeDesMembres = some true) (h₂ : a.dimensions = []) :
    bienFormeeP7 a = false := by
  simp [bienFormeeP7, h₁, h₂]

/-- **Témoin discriminant** : la même attribution, avec une dimension, est bien formée. -/
theorem P7_temoin_discriminant :
    bienFormeeP7 ⟨some true, [1], [.avec]⟩ = true
  ∧ bienFormeeP7 ⟨some true, [1], []⟩ = false := by
  decide

/-- **La lecture exclusive ne porte pas deux dimensions** : une métaorganisation
    qui « accompagne » et « contraint » (AVEC et SUR) est bien formée, et aucune
    valeur unique — la lecture initiale de P7 — ne la représente. -/
theorem la_lecture_exclusive_ne_porte_pas_deux_dimensions :
    ∃ a : AttributionPorteur, bienFormeeP7 a = true ∧ a.dimensions = [.avec, .sur]
      ∧ ∀ d : Dimension, a.dimensions ≠ [d] :=
  ⟨⟨some true, [1], [.avec, .sur]⟩, rfl, rfl, fun d h => by cases d <;> cases h⟩

end ProfRegPR31
