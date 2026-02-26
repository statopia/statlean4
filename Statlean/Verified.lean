/-! # Statlean Verified Library

**Every declaration reachable from this import is fully proved (zero sorry).**

This is the "clean" entry point for the StatLean library. It only imports
modules that have been verified to contain no sorry — neither directly
nor transitively through their dependency chains.

To check: `lake build Statlean.Verified` should produce zero sorry warnings.

## Contents

- **RaoBlackwell_MSE**: Rao-Blackwell MSE theorem and variants (20 declarations)
- **Concentration/Basic**: σ-algebra infrastructure (4 declarations)
- **Concentration/Density**: Mollification, Sobolev density (2 declarations)
- **Concentration/EfronSteinProved**: Efron-Stein clean core (16 declarations)
- **Concentration/GaussianPoincareProved**: Stein identity, Lp integrability (13 declarations)
- **Concentration/LogSobolevProved**: LSI definitions and parametric theorems (13 declarations)
- **Concentration/GaussianLipschitzProved**: Integrability, parametric bounds (11 declarations)
- **Concentration/HermiteOrthogonality**: Hermite derivative + orthogonality (11 declarations)
- **Concentration/BerryEsseenProved**: Charfun chain, Taylor bounds, Lyapunov (17 declarations)
-/

-- Core
import Statlean.Basic
import Statlean.RaoBlackwell_MSE

-- Concentration: verified parts only
import Statlean.Concentration.Basic
import Statlean.Concentration.Density
import Statlean.Concentration.EfronSteinProved
import Statlean.Concentration.GaussianPoincareProved
import Statlean.Concentration.HermiteOrthogonality
import Statlean.Concentration.LogSobolevProved
import Statlean.Concentration.GaussianLipschitzProved
import Statlean.Concentration.BerryEsseenProved
