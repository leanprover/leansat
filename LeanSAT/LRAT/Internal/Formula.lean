/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.LRAT.Internal.Formula.Lemmas
import LeanSAT.LRAT.Internal.Formula.Class
import LeanSAT.LRAT.Internal.Formula.Implementation
import LeanSAT.LRAT.Internal.Formula.Instance
import LeanSAT.LRAT.Internal.Formula.RatAddResult
import LeanSAT.LRAT.Internal.Formula.RatAddSound
import LeanSAT.LRAT.Internal.Formula.RupAddResult
import LeanSAT.LRAT.Internal.Formula.RupAddSound

/-!
This directory contains the current implementation of the LRAT checker that is plugged into the
generic LRAT checking loop from `LRATChecker` and then used in the surface level LRAT checker
that is publicly exposed.
-/
