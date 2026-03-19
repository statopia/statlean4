/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.Fourier.JacksonKernel
import Statlean.CharFun.Taylor

/-!
# CDF Inversion Infrastructure

This module previously contained a Fourier bound for kernel CDF convolution.
The Fourier bound for the triangle kernel was shown to be FALSE (Paley-Wiener:
the triangle kernel's FT is sinc², not compactly supported in [-T,T]).

The Esseen smoothing inequality now uses the Fejér CDF inversion remainder
bound directly (see `fejer_cdf_inversion_remainder` in BerryEsseen.lean),
bypassing the kernel Fourier bound.

## References
- Esseen (1945), Feller Vol II §XV.3
-/
