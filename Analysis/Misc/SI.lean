import Mathlib.Tactic
import Analysis.Misc.UnitsSystem
import Mathlib.Algebra.Group.MinimalAxioms


/-- The SI unit system.  In order to permit fractional dimensions, we allow dimensions to be rational; but then to maintain definitional equality of various explicit dimensions, we need to unseal the arithmetic operations on the rationals. -/
@[ext]
structure SI_dimensions where
  units_length : ℚ
  units_mass : ℚ
  units_time : ℚ
  units_current : ℚ
  units_temperature : ℚ
  units_amount : ℚ
  units_intensity : ℚ
deriving DecidableEq

instance SI_dimensions.instZero : Zero SI_dimensions where
  zero := ⟨0, 0, 0, 0, 0, 0, 0⟩

theorem SI_dimensions.zero_eq : (0:SI_dimensions) = ⟨ 0,0,0,0,0,0,0⟩ := rfl

/-- {given -show (type := "SI_dimensions")}`d₁, d₂`The addition structure here is simple enough that
  one gets a lot of definitional equalities, e.g., between {lean}`d₁+d₂` and {lean}`d₂+d₁` for
  explicit choices of {name}`d₁` and {name}`d₂`, which is convenient as it means we do not need to
  utilize the {name (full := UnitsSystem.Scalar.cast)}`Scalar.cast` operator much. -/
instance SI_dimensions.instAdd : Add SI_dimensions where
  add d₁ d₂ := ⟨d₁.units_length + d₂.units_length,
                d₁.units_mass + d₂.units_mass,
                d₁.units_time + d₂.units_time,
                d₁.units_current + d₂.units_current,
                d₁.units_temperature + d₂.units_temperature,
                d₁.units_amount + d₂.units_amount,
                d₁.units_intensity + d₂.units_intensity
                ⟩

instance SI_dimensions.instNeg : Neg SI_dimensions where
  neg d := ⟨-d.units_length, -d.units_mass, -d.units_time, -d.units_current,
            -d.units_temperature, -d.units_amount, -d.units_intensity⟩

@[simp]
theorem Rat.neg_eq (q:ℚ) : Rat.neg q = -q := rfl

theorem Rat.add_eq (q r:ℚ) : Rat.add q r = q + r := rfl

instance SI_dimensions.instAddGroup : AddGroup SI_dimensions :=
AddGroup.ofLeftAxioms
  (by intros; simp_rw [HAdd.hAdd, Add.add]; simp [add_assoc])
  (by intros; simp_rw [HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]; simp)
  (by intros; simp_rw [Neg.neg, HAdd.hAdd, Add.add, OfNat.ofNat, Zero.zero]; simp)

instance SI_dimensions.instAddCommGroup : AddCommGroup SI_dimensions where
  add_comm d₁ d₂ := by
    simp_rw [HAdd.hAdd, Add.add]; simp [add_comm]

instance SI_dimensions.instSMul : SMul ℚ SI_dimensions where
  smul q d := ⟨q * d.units_length, q * d.units_mass, q * d.units_time, q * d.units_current,
                q * d.units_temperature, q * d.units_amount, q * d.units_intensity⟩

instance SI_dimensions.instModule : Module ℚ SI_dimensions where
  one_smul d := by
    ext <;> simp [HSMul.hSMul, SMul.smul]
  mul_smul q₁ q₂ d := by
    ext <;> simp [HSMul.hSMul, SMul.smul, mul_assoc]
  smul_add q d₁ d₂ := by
    ext <;> simp [HSMul.hSMul, SMul.smul, HAdd.hAdd, Add.add] <;> simp [Rat.add_eq, mul_add]
  smul_zero q := by
    ext <;> simp [HSMul.hSMul, SMul.smul, zero_eq]
  add_smul d₁ d₂ q := by
    ext <;> simp [HAdd.hAdd, Add.add, HSMul.hSMul, SMul.smul] <;> simp [Rat.add_eq, add_mul]
  zero_smul d := by
    ext <;> simp [HSMul.hSMul, SMul.smul, zero_eq]

abbrev SI : UnitsSystem := {
  Dimensions := SI_dimensions
  addCommGroup := SI_dimensions.instAddCommGroup
}

/-- The SI system will be automatically installed as a global instance by any Lean file that imports this one.  This makes it difficult to use any competing {name}`UnitsSystem`
simultaneously, but that should be a rare use case. -/
instance instSI : UnitsSystem := SI
instance instSI_module : Module ℚ SI.Dimensions := SI_dimensions.instModule

namespace SI
open UnitsSystem


abbrev deca {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ) • q
abbrev hecto {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^2 • q
abbrev kilo {d:Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^3 • q
abbrev mega {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^6 • q
abbrev giga {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^9 • q
abbrev tera {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^12 • q
abbrev peta {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^15 • q
abbrev exa {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^18 • q

noncomputable abbrev deci {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-1:ℤ) • q
noncomputable abbrev centi {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-2:ℤ) • q
noncomputable abbrev milli {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-3:ℤ) • q
noncomputable abbrev micro {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-6:ℤ) • q
noncomputable abbrev nano {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-9:ℤ) • q
noncomputable abbrev pico {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-12:ℤ) • q
noncomputable abbrev femto {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-15:ℤ) • q
noncomputable abbrev atto {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-18:ℤ) • q

abbrev Dimensionless := Scalar (0:Dimensions)

abbrev length_unit :Dimensions := ⟨1, 0, 0, 0, 0, 0, 0⟩
abbrev Length := Scalar length_unit
abbrev meter:Length := StandardUnit _

abbrev mass_unit :Dimensions := ⟨0, 1, 0, 0, 0, 0, 0⟩
abbrev Mass := Scalar mass_unit
abbrev kilogram:Mass := StandardUnit _
noncomputable abbrev gram:Mass := milli kilogram

abbrev time_unit :Dimensions := ⟨0, 0, 1, 0, 0, 0, 0⟩
abbrev Time := Scalar time_unit
abbrev second:Time := StandardUnit _
abbrev minute:Time := 60 • second
abbrev hour:Time := 60 • minute
abbrev day:Time := 24 • hour
abbrev week:Time := 7 • day
abbrev year:Time := (365.25:ℝ) • day -- average year length, accounting for leap years

abbrev current_unit :Dimensions := ⟨0, 0, 0, 1, 0, 0, 0⟩
abbrev Current := Scalar current_unit
abbrev ampere:Current := StandardUnit _

abbrev temperature_unit :Dimensions := ⟨0, 0, 0, 0, 1, 0, 0⟩
abbrev Temperature := Scalar temperature_unit
abbrev kelvin:Temperature := StandardUnit _

abbrev amount_unit :Dimensions := ⟨0, 0, 0, 0, 0, 1, 0⟩
abbrev Amount := Scalar amount_unit
abbrev mole:Amount := StandardUnit _

abbrev intensity_unit :Dimensions := ⟨0, 0, 0, 0, 0, 0, 1⟩
abbrev Intensity := Scalar intensity_unit
abbrev candela:Intensity := StandardUnit _

abbrev speed_unit := length_unit - time_unit
abbrev Speed := Scalar speed_unit

abbrev acceleration_unit := length_unit - (2 • time_unit)
abbrev Acceleration := Scalar acceleration_unit

abbrev momentum_unit := mass_unit + speed_unit
abbrev Momentum := Scalar momentum_unit

abbrev energy_unit := mass_unit + (2 • speed_unit)
abbrev Energy := Scalar energy_unit
abbrev joule:Energy := StandardUnit _

abbrev force_unit := mass_unit + acceleration_unit
abbrev Force := Scalar force_unit
abbrev newton:Force := StandardUnit _

abbrev frequency_unit := -time_unit
abbrev Frequency := Scalar frequency_unit
abbrev hertz:Frequency := StandardUnit _

abbrev pressure_unit := force_unit - (2 • length_unit)
abbrev Pressure := Scalar pressure_unit
abbrev pascal:Pressure := StandardUnit _

abbrev power_unit := energy_unit - time_unit
abbrev Power := Scalar power_unit
abbrev watt:Power := StandardUnit _

abbrev charge_unit := current_unit + time_unit
abbrev Charge := Scalar charge_unit
abbrev coulomb:Charge := StandardUnit _

abbrev voltage_unit := energy_unit - charge_unit
abbrev Voltage := Scalar voltage_unit
abbrev volt:Voltage := StandardUnit _

abbrev capacitance_unit := charge_unit - voltage_unit
abbrev Capacitance := Scalar capacitance_unit
abbrev farad:Capacitance := StandardUnit _

abbrev resistance_unit := voltage_unit - current_unit
abbrev Resistance := Scalar resistance_unit
abbrev ohm:Resistance := StandardUnit _

abbrev inductance_unit := voltage_unit - (2 • current_unit)
abbrev Inductance := Scalar inductance_unit
abbrev henry:Inductance := StandardUnit _

abbrev magnetic_flux_unit := voltage_unit + time_unit
abbrev MagneticFlux := Scalar magnetic_flux_unit
abbrev weber:MagneticFlux := StandardUnit _

abbrev magnetic_flux_density_unit := magnetic_flux_unit - length_unit
abbrev MagneticFluxDensity := Scalar magnetic_flux_density_unit
abbrev tesla:MagneticFluxDensity := StandardUnit _


abbrev c : Speed := 299792458 • StandardUnit _ -- speed of light in vacuum
noncomputable abbrev h : Scalar (energy_unit + time_unit) := (6.62607015 * (10:ℝ)^(-34:ℤ)) • StandardUnit _ -- Planck's constant
noncomputable abbrev e : Charge := (1.602176634 * (10:ℝ)^(-19:ℤ)) • StandardUnit _ -- elementary charge
noncomputable abbrev ε₀ : Capacitance := (8.854187817 * (10:ℝ)^(-12:ℤ)) • StandardUnit _ -- vacuum permittivity
noncomputable abbrev μ₀ : Inductance := (4 * Real.pi * (10:ℝ)^(-7:ℤ)) • StandardUnit _ -- vacuum permeability
noncomputable abbrev g : Acceleration := (9.80665:ℝ) • StandardUnit _ -- standard acceleration of gravity
noncomputable abbrev k : Scalar (energy_unit + temperature_unit) := (1.380649 * (10:ℝ)^(-23:ℤ)) • StandardUnit _ -- Boltzmann constant
noncomputable abbrev N_A : Amount := (6.02214076 * (10:ℝ)^(23:ℤ)) • StandardUnit _ -- Avogadro's number




end SI
