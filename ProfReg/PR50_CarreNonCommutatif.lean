/-
  PR50_CarreNonCommutatif.lean
  ===========================================================================
  Objet : le signal `carre_non_commutatif` de la Fiche F3 (NT-ARCH v5.7, §B.3,
  table 3.3) : « Défaut SVD ≠ FCA pondérée ≥ seuil → REVISION_CONCEPTUELLE ».

  CE QUI EST MODÉLISÉ : la FORME du signal — deux chemins d'un même carré,
  un écart DÉCLARÉ entre leurs sorties, un seuil DÉCLARÉ.
  CE QUI NE L'EST PAS : le calcul SVD, le treillis FCA pondéré, la 2-cellule,
  la « double catégorie ProfReg » invoquée par F3 (absente des sources Lean).
  Les deux chemins sont des fonctions quelconques ; l'écart est une donnée.

  Sans Mathlib ; aucun réel, aucune chaîne : contrôle des `Classical.choice`
  non affecté (règle des deux portes, NT-ARCH §8quinquies-ter).
-/
namespace ProfRegPR50

/-- Un carré à deux chemins de X vers V (ex. : chemin SVD, chemin FCA pondérée). -/
structure Carre (X V : Type) where
  cheminA : X → V
  cheminB : X → V

/-- Le carré commute s'il rend la même valeur par les deux chemins. -/
def Commute {X V : Type} (c : Carre X V) : Prop := ∀ x, c.cheminA x = c.cheminB x

/-- Un écart déclaré : nul sur deux valeurs égales. Il n'est pas calculé ici. -/
structure EcartDeclare (V : Type) where
  ecart : V → V → Nat
  nul_sur_egal : ∀ v, ecart v v = 0

/-- Le signal se lève si le seuil est déclaré, strictement positif, et atteint. -/
def signal {X V : Type} (c : Carre X V) (e : EcartDeclare V) (seuil : Option Nat) (x : X) : Bool :=
  match seuil with
  | none   => false
  | some k => decide (0 < k) && decide (k ≤ e.ecart (c.cheminA x) (c.cheminB x))

/-- Marqueur : un seuil non déclaré ne lève pas le signal, il se signale lui-même. -/
def marqueurSeuilNonDeclare (seuil : Option Nat) : Bool := seuil.isNone

/-- Un signal levé atteste une non-commutation en ce point. -/
theorem signal_implique_non_commutation {X V : Type} (c : Carre X V) (e : EcartDeclare V)
    (seuil : Option Nat) (x : X) (h : signal c e seuil x = true) :
    c.cheminA x ≠ c.cheminB x := by
  intro heq
  cases seuil with
  | none => simp [signal] at h
  | some k =>
    simp only [signal, heq, e.nul_sur_egal, Bool.and_eq_true, decide_eq_true_eq] at h
    exact absurd h.2 (Nat.not_le.mpr h.1)

/-- Un carré qui commute ne lève jamais le signal. -/
theorem commutatif_ne_signale_pas {X V : Type} (c : Carre X V) (e : EcartDeclare V)
    (seuil : Option Nat) (h : Commute c) (x : X) : signal c e seuil x = false := by
  cases hs : signal c e seuil x with
  | false => rfl
  | true => exact absurd (h x) (signal_implique_non_commutation c e seuil x hs)

/-- Un seuil non déclaré ne lève pas le signal, et porte le marqueur. -/
theorem seuil_non_declare_ne_signale_pas {X V : Type} (c : Carre X V) (e : EcartDeclare V) (x : X) :
    signal c e none x = false ∧ marqueurSeuilNonDeclare none = true := ⟨rfl, rfl⟩

/-- Témoin : écart sur `Nat` (distance absolue). -/
def ecartNat : EcartDeclare Nat :=
  ⟨fun a b => (a - b) + (b - a), fun v => by simp⟩

/-- Témoin : un carré qui ne commute pas (écart de 3 au point 0). -/
def carreTemoin : Carre Unit Nat := ⟨fun _ => 5, fun _ => 2⟩

/-- Le signal n'est pas la non-commutativité : sous le seuil, un carré qui ne commute pas ne signale rien. -/
theorem non_commutation_sous_le_seuil_ne_signale_pas :
    ¬ Commute carreTemoin ∧ signal carreTemoin ecartNat (some 10) () = false := by
  refine ⟨fun h => ?_, by decide⟩
  have := h (); simp [carreTemoin] at this

/-- Témoin discriminant : même carré, même écart ; le signal dépend du seuil déclaré. -/
theorem signal_temoin_discriminant :
    signal carreTemoin ecartNat (some 1) () = true ∧
    signal carreTemoin ecartNat (some 10) () = false := by decide

/-- Écart d'appoint : discret (0 si égal, 1 sinon). -/
def ecartDiscret : EcartDeclare Nat :=
  ⟨fun a b => if a = b then 0 else 1, fun v => by simp⟩

/-- Le signal dépend de l'écart déclaré : même carré, même seuil, deux écarts, deux verdicts.
    Le choix de la mesure (SVD, FCA pondérée…) est donc une déclaration, non un calcul neutre. -/
theorem le_signal_depend_de_l_ecart_declare :
    signal carreTemoin ecartNat (some 2) () = true ∧
    signal carreTemoin ecartDiscret (some 2) () = false := by decide

/-- L'action du signal est déclarée (REVISION_CONCEPTUELLE) ; l'évaluation du signal
    ne modifie pas le carré : la révision est un acte extérieur (patron PR-5, VJE). -/
inductive Action | revisionConceptuelle | aucune
deriving DecidableEq

def action {X V : Type} (c : Carre X V) (e : EcartDeclare V) (s : Option Nat) (x : X) : Action :=
  if signal c e s x then .revisionConceptuelle else .aucune

theorem action_temoin_discriminant :
    action carreTemoin ecartNat (some 1) () = .revisionConceptuelle ∧
    action carreTemoin ecartNat (some 10) () = .aucune := by decide

end ProfRegPR50
