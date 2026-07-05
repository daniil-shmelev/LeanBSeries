# LeanBSeries

[![CI](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml/badge.svg)](https://github.com/daniil-shmelev/LeanBSeries/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.32-blue)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/mathlib4-latest-9cf)](https://github.com/leanprover-community/mathlib4)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-lightgrey.svg)](LICENSE)

A formalisation of Butcher series and Runge–Kutta order theory in Lean 4.

## Building

Requires the sibling repository
[LeanRoughPaths](https://github.com/daniil-shmelev/LeanRoughPaths)
(rooted trees and their Hopf algebras) checked out next to this one:

```
git clone https://github.com/daniil-shmelev/LeanRoughPaths lean-rough-paths
git clone https://github.com/daniil-shmelev/LeanBSeries    lean-b-series
cd lean-b-series
lake exe cache get
lake build
```
