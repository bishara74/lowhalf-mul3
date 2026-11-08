module

public import LowHalfMul3.LambdaOneAssembly
public import LowHalfMul3.LambdaOneOrdinary

@[expose] public section

namespace UnrestrictedBooleanMul.LowHalfMul3

open LambdaOne

/-- The one-linear-gate exclusion, parameterized by the shared two-case work.
The ideal and rank premises are also included explicitly for integration.
Their consequences in this proof enter through `FeedbackNoPlaceModLow`. -/
theorem lambdaCase_one_of (hTwo : TwoClaim) (hLast : LastFactorLowIdeal)
    (_hIdeal : IdealExtract) (_hRank : Q2NotTwoWedges)
    (hMod : FeedbackNoPlaceModLow) (hNormal : FeedbackNormal) : LambdaCase 1 :=
  lambdaCase_one_of_branches hTwo (early_z1_core hNormal)
    (fun hb => by
      intro f h hf hh hc
      exact noncore_noNextZ2 hb hc (fun _ hF => ordinary_pair_noPlace hb hF)
        hLast hMod hNormal hf hh)

end UnrestrictedBooleanMul.LowHalfMul3
