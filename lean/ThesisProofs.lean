-- ThesisProofs: Lean 4 Formalization of
-- "Hyper-Resolution Soil Moisture, Ecohydrological Optimality,
--  and Mechanistic Evapotranspiration Simulation"
-- IITB PhD Thesis by Sanjay

-- ═══════════════════════════════════════════════════
-- Shared Definitions
-- ═══════════════════════════════════════════════════
import ThesisProofs.Defs.SoilHydraulics
import ThesisProofs.Defs.EnergyBalance
import ThesisProofs.Defs.BuckinghamPi
import ThesisProofs.Defs.StatMetrics

-- ═══════════════════════════════════════════════════
-- Chapter 2: Conceptual Foundations
-- ═══════════════════════════════════════════════════
import ThesisProofs.Ch02_Foundations.EnergyBalanceLaw
import ThesisProofs.Ch02_Foundations.PriestleyTaylor
import ThesisProofs.Ch02_Foundations.PiecewiseStress

-- ═══════════════════════════════════════════════════
-- Chapter 3: Statistical Evaluation Metrics
-- ═══════════════════════════════════════════════════
import ThesisProofs.Ch03_Metrics.MetricProperties

-- ═══════════════════════════════════════════════════
-- Chapter 4: Downscaling & Data Assimilation
-- ═══════════════════════════════════════════════════
import ThesisProofs.Ch04_Downscaling.BeerLaw
import ThesisProofs.Ch04_Downscaling.FresnelReflectivity
import ThesisProofs.Ch04_Downscaling.KalmanUpdate

-- ═══════════════════════════════════════════════════
-- Chapter 5: Ecohydrological Optimality
-- ═══════════════════════════════════════════════════
import ThesisProofs.Ch05_Optimality.SPACFlux
import ThesisProofs.Ch05_Optimality.OWUSStress
import ThesisProofs.Ch05_Optimality.SoilSaturationPDF
import ThesisProofs.Ch05_Optimality.OptimalityCriterion

-- ═══════════════════════════════════════════════════
-- Chapter 6: PT-JPL-SM-OWUS Framework
-- ═══════════════════════════════════════════════════
import ThesisProofs.Ch06_Framework.PTJPLComponents
import ThesisProofs.Ch06_Framework.FusedMoistureConstraint
import ThesisProofs.Ch06_Framework.RadiationPartition

-- ═══════════════════════════════════════════════════
-- Chapter 7: Synthesis & Cross-Chapter Consistency
-- ═══════════════════════════════════════════════════
import ThesisProofs.Ch07_Synthesis.StressConsistency
