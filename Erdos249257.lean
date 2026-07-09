/-
SPDX-FileCopyrightText: 2026 Will Cook
SPDX-License-Identifier: Apache-2.0

Root module for the Erdős #249/#257 Lean formalisation.

This package contains:
* #257-side Erdős--Borwein support-family irrationality results;
* #249-side totient-series denominator exclusions and certificate reductions;
* generated finite certificate witnesses.

It does not prove Erdős #249, and it does not prove the universal #257 statement.

Import order follows the mathematical route (not historical wave order):
GapFareyBound → MersenneLambertLadder → GeometricCoprimality → GcdMomentCalculus →
TotientTailPeriodKiller → CarrySurvivorExtinction → LcmDiagonalReduction →
LcmConeFlatness → LcmConeNonflat → CertificateKernel ← GeneratedCertificates.
-/
import Erdos249257.GapFareyBound
import Erdos249257.MersenneLambertLadder
import Erdos249257.GeometricCoprimality
import Erdos249257.GcdMomentCalculus
import Erdos249257.TotientTailPeriodKiller
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.LcmDiagonalReduction
import Erdos249257.LcmConeFlatness
import Erdos249257.LcmConeNonflat
import Erdos249257.CertificateKernel
import Erdos249257.GeneratedCertificates
