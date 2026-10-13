import ProfReg.Sonde_PCEDed
/-!
# PR-29 — La table §8.5.2 : lecture du « + », colonne dédoublée, arités

28 septembre 2026. Décision du porteur (groupe C de l'audit du 26/09, lot C-α) :
**(c) puis (a)** — le « + » de la ligne `D−` est déclaré **composite** (lecture
de §8.5.4), puis la colonne « Nature de la relation » est **dédoublée** en
*lieu de l'écriture* (un livre / deux livres / trois livres) et *contrepartie
nommée*. Les quatre vraies lacunes (`E+→C+`, `E+→D+`, `E−→C−`, `d→C−`) sont
traitées au cas par cas, comme toute lacune de table (arbitrage A8).
[En-tête corrigé le 29/09/2026 — M11 : il disait « deux lacunes » ; aligné sur
`sous_la_colonne_dedoublee_restent_quatre_lacunes`, décision du porteur du 28/09.]

**Deux natures dans ce fichier.**
· §1-§2 formalisent **un texte** — la table du 18/09 (`miroir1809`) et ses
  colonnes : ils se comptent dans la **colonne texte**, comme la sonde.
· §3-§4 portent sur l'architecture : le statut d'un couple absent (C-3) et la
  troisième arité (C-14).

`[RÉSERVE DE MODÈLE]` L'affectation d'un lieu à chaque branche est la lecture
de l'instructeur (Instruction groupe C, §1.2), **validée par le porteur le
28/09** ; les branches « cas par cas » (`D+ ↔ D−`, `D− ↔ D+`) n'ont pas de lieu
unique et restent déclarées cas par cas.
-/

namespace ProfRegPR29

open SondePCEDed

/-! ## 1. Les deux lectures du « + » -/

/-- Lecture littérale : la ligne `y` porte `x` **seul**. -/
def porteLitteral (y x : Typage) : Bool := decide ([x] ∈ miroir1809 y)

/-- Lecture composite (décision (c), 28/09) : le « + » d'un composite vaut pour
    chacune de ses composantes — `C− + e` porte `C−` et porte `e`. -/
def porteComposante (y x : Typage) : Bool :=
  (miroir1809 y).any (fun l => decide (x ∈ l))

/-! ## 2. Les colonnes -/

/-- Colonne d'origine « Nature de la relation » (B7, 18/09). -/
inductive Nature where
  | intra | inter | mixte | casParCas
  deriving DecidableEq, Repr

/-- Colonne dédoublée (décision (a), 28/09) : **lieu de l'écriture**. -/
inductive Lieu where
  | unLivre | deuxLivres | troisLivres
  deriving DecidableEq, Repr

structure Branche where
  a      : Typage
  b      : Typage
  nature : Nature
  /-- `none` : déclaré cas par cas. -/
  lieu   : Option Lieu
  /-- Une contrepartie est nommée (autre acteur), quel que soit le livre. -/
  contrepartieNommee : Bool
  deriving DecidableEq, Repr

/-- Les 27 branches à contrepartie simple de la table du 18/09 (`E+ ↔ ∅` exclue ;
    la ligne composite `P+ + D+ ↔ P− + D−` est hors de `miroir1809`). -/
def branches : List Branche :=
  [ ⟨Prim.P⁺, Prim.D⁺, .inter, some .unLivre, true⟩
  , ⟨Prim.P⁺, Prim.e°, .intra, some .unLivre, false⟩
  , ⟨Prim.P⁺, Prim.P⁻, .intra, some .unLivre, false⟩
  , ⟨Prim.P⁻, Prim.C⁺, .inter, some .unLivre, true⟩
  , ⟨Prim.P⁻, Prim.d°, .intra, some .unLivre, false⟩
  , ⟨Prim.P⁻, Prim.P⁺, .intra, some .unLivre, false⟩
  , ⟨Prim.P⁻, Prim.e°, .intra, some .unLivre, false⟩
  , ⟨Prim.C⁺, Prim.D⁺, .inter, some .deuxLivres, true⟩
  , ⟨Prim.C⁻, Prim.D⁻, .inter, some .deuxLivres, true⟩
  , ⟨Prim.E⁺, Prim.D⁺, .inter, some .deuxLivres, true⟩   -- « chez B » (corrigé le 28/09)
  , ⟨Prim.E⁺, Prim.C⁺, .inter, some .deuxLivres, true⟩   -- « chez B » (corrigé le 28/09)
  , ⟨Prim.E⁺, Prim.e°, .intra, some .unLivre, false⟩
  , ⟨Prim.E⁺, Prim.E⁻, .intra, some .unLivre, false⟩
  , ⟨Prim.E⁺, Prim.D⁻, .mixte, some .unLivre, true⟩
  , ⟨Prim.E⁻, Prim.C⁻, .inter, some .deuxLivres, true⟩
  , ⟨Prim.E⁻, Prim.D⁺, .inter, some .unLivre, true⟩
  , ⟨Prim.E⁻, Prim.d°, .intra, some .unLivre, false⟩
  , ⟨Prim.D⁺, Prim.C⁺, .inter, some .deuxLivres, true⟩
  , ⟨Prim.D⁺, Prim.D⁻, .casParCas, none, true⟩
  , ⟨Prim.D⁻, Prim.C⁻, .mixte, some .deuxLivres, true⟩
  , ⟨Prim.D⁻, Prim.D⁺, .casParCas, none, true⟩
  , ⟨Prim.e°, Prim.d°, .inter, some .deuxLivres, true⟩
  , ⟨Prim.e°, Prim.D⁻, .inter, some .deuxLivres, true⟩
  , ⟨Prim.e°, Prim.E⁺, .intra, some .unLivre, false⟩
  , ⟨Prim.e°, Prim.P⁻, .intra, some .unLivre, false⟩
  , ⟨Prim.d°, Prim.e°, .inter, some .deuxLivres, true⟩
  , ⟨Prim.d°, Prim.C⁻, .inter, some .deuxLivres, true⟩ ]

def interOuMixte (b : Branche) : Bool := b.nature == .inter || b.nature == .mixte

/-- **Fidélité de la transcription** (garde) : chaque branche est admise par
    `miroir1809` en lecture composite ; les 27 y sont. -/
theorem branches_fideles_a_la_table :
    branches.length = 27 ∧ branches.all (fun b => porteComposante b.a b.b) = true := by
  decide

/-- **Constat (texte) — la colonne d'origine ne satisfait pas B7.** En lecture
    composite, 8 des 15 branches inter-acteurs ou mixtes échouent au contrôle
    « un couple `X ↔ Y` inter-acteurs exige que la ligne `Y` porte `X` ». -/
theorem la_colonne_d_origine_ne_satisfait_pas_B7 :
    (branches.filter interOuMixte).length = 15
  ∧ (branches.filter (fun b => interOuMixte b && !porteComposante b.b b.a)).map
      (fun b => (b.a, b.b)) =
      [(Prim.P⁺, Prim.D⁺), (Prim.P⁻, Prim.C⁺), (Prim.E⁺, Prim.D⁺), (Prim.E⁺, Prim.C⁺),
       (Prim.E⁺, Prim.D⁻), (Prim.E⁻, Prim.C⁻), (Prim.E⁻, Prim.D⁺), (Prim.d°, Prim.C⁻)] := by
  decide

/-- **Pourquoi (c) précède (a) (texte).** Le décompte dépend de la lecture du
    « + » : 10 échecs en lecture littérale, 8 en lecture composite. -/
theorem le_decompte_depend_de_la_lecture_du_plus :
    (branches.filter (fun b => interOuMixte b && !porteLitteral b.b b.a)).length = 10
  ∧ (branches.filter (fun b => interOuMixte b && !porteComposante b.b b.a)).length = 8 := by
  decide

/-- **Sous la colonne dédoublée (texte), restent exactement quatre lacunes** :
    parmi les branches à deux livres, seules `E+→D+`, `E+→C+`, `E−→C−` et `d→C−`
    ne sont pas réciproques. Elles sont traitées cas par cas (arbitrage A8).
    `[CORRIGÉ LE 28/09/2026]` La première version affectait « un livre » à `E+→D+` et
    `E+→C+`, que la table dit « chez B » ; elle concluait à deux lacunes
    (`sous_la_colonne_dedoublee_restent_deux_lacunes`, retiré). -/
theorem sous_la_colonne_dedoublee_restent_quatre_lacunes :
    (branches.filter (fun b => b.lieu == some .deuxLivres && !porteComposante b.b b.a)).map
      (fun b => (b.a, b.b)) =
      [(Prim.E⁺, Prim.D⁺), (Prim.E⁺, Prim.C⁺), (Prim.E⁻, Prim.C⁻), (Prim.d°, Prim.C⁻)] := by
  decide

/-- **Le dédoublement ne perd rien (texte)** : toute branche d'origine
    inter-acteurs ou mixte garde sa contrepartie nommée, qu'elle soit
    désormais « un livre » ou « deux livres ». -/
theorem le_dedoublement_conserve_la_contrepartie :
    (branches.filter interOuMixte).all (fun b => b.contrepartieNommee) = true
  ∧ (branches.filter interOuMixte).all
      (fun b => b.lieu == some .unLivre || b.lieu == some .deuxLivres) = true := by
  decide

/-! ## 3. C-3 — « absent de la table » n'implique pas « violation de R1 »

NT-ARCH §8.5.2, arbitrage A8 (18/09) : un couple absent est une **violation**
si le miroir n'existe nulle part, une **lacune** si le miroir existe et
qu'aucune ligne ne l'apparie. -/

inductive StatutCouple where
  | admis | lacune | violation
  deriving DecidableEq, Repr

structure EcritureObservee where
  a : Typage
  b : Type6
  /-- La contrepartie est inscrite dans un autre livre — un fait **extérieur à la table**. -/
  miroirAilleurs : Bool
  deriving DecidableEq, Repr

def statut (e : EcritureObservee) : StatutCouple :=
  if decide (e.b ∈ miroir1809 e.a) then .admis
  else if e.miroirAilleurs then .lacune else .violation

/-- **Un couple absent a deux issues.** `P− ↔ ∅` (écriture unilatérale) est une
    violation ; `C− ↔ E−`, la lacune `E−→C−` vue du livre de l'apporteur, dont
    le miroir est inscrit chez l'émetteur, est une lacune. -/
theorem absent_n_implique_pas_violation :
    statut ⟨Prim.P⁻, [], false⟩ = .violation
  ∧ ¬ (([Prim.E⁻] : Type6) ∈ miroir1809 Prim.C⁻)
  ∧ statut ⟨Prim.C⁻, [Prim.E⁻], true⟩ = .lacune := by
  decide

/-- **Le statut ne se lit pas sur la table seule** : même couple, deux statuts,
    selon que le miroir est inscrit ailleurs. Un contrôle binaire sur la table
    (« admis / non admis ») ne sépare donc pas la violation de la lacune. -/
theorem le_statut_ne_se_lit_pas_sur_la_table :
    ∃ e₁ e₂ : EcritureObservee, e₁.a = e₂.a ∧ e₁.b = e₂.b ∧ statut e₁ ≠ statut e₂ :=
  ⟨⟨Prim.C⁻, [Prim.E⁻], true⟩, ⟨Prim.C⁻, [Prim.E⁻], false⟩, rfl, rfl, by decide⟩

/-! ## 4. C-14 — la troisième arité (B7) et PR-20

PR-20 modélise **deux** livres (`Creance := Actor → Actor → Bool`). B7 exige
d'une écriture à trois livres **l'identité du tiers et la nature de ce qui
s'inscrit chez lui**. Identités codées par `Nat` (pas de `String`). -/

structure EcritureArite where
  lieu            : Lieu
  contrepartie    : Option Nat
  tiers           : Option Nat
  natureChezTiers : Option Nat
  deriving DecidableEq, Repr

def bienFormeeArite (e : EcritureArite) : Bool :=
  match e.lieu with
  | .unLivre     => true
  | .deuxLivres  => e.contrepartie.isSome
  | .troisLivres => e.contrepartie.isSome && e.tiers.isSome && e.natureChezTiers.isSome

/-- **Trois livres sans tiers nommé : mal formée.** -/
theorem trois_livres_sans_tiers_mal_formee (e : EcritureArite)
    (h₁ : e.lieu = .troisLivres) (h₂ : e.tiers = none) : bienFormeeArite e = false := by
  simp [bienFormeeArite, h₁, h₂]

/-- **Témoin discriminant** : le tiers nommé, avec la nature de ce qui
    s'inscrit chez lui, rend l'écriture bien formée. -/
theorem trois_livres_temoin_discriminant :
    bienFormeeArite ⟨.troisLivres, some 1, some 2, some 0⟩ = true
  ∧ bienFormeeArite ⟨.troisLivres, some 1, none, some 0⟩ = false := by
  decide

/-- **La troisième arité n'est pas la deuxième** (non-implication) : une
    écriture bien formée à deux livres, relue à trois livres, ne l'est plus.
    Le modèle de PR-20, à deux livres, ne porte donc pas la garde de B7. -/
theorem la_troisieme_arite_n_est_pas_la_deuxieme :
    ∃ e : EcritureArite, e.lieu = .deuxLivres ∧ bienFormeeArite e = true
      ∧ bienFormeeArite { e with lieu := .troisLivres } = false :=
  ⟨⟨.deuxLivres, some 1, none, none⟩, rfl, rfl, rfl⟩

end ProfRegPR29
