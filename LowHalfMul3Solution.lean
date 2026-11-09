module

public import LowHalfMul3

@[expose] public section

/-! The unrestricted multiplicative complexity of the three-bit low-half multiplier. -/

namespace UnrestrictedBooleanMul.LowHalfMul3

theorem lambdaCase_one : LambdaCase 1 :=
  lambdaCase_one_of twoClaim LambdaOne.lastFactorLowIdeal LambdaOne.idealExtract
    LambdaOne.q2NotTwoWedges LambdaOne.feedbackNoPlaceModLow LambdaOne.feedbackNormal

theorem lambdaCase_two : LambdaCase 2 :=
  lambdaCase_two_of twoClaim

/-- Six products are necessary and sufficient for the three-bit low-half product. -/
theorem mc_lowMul3 : MC(lowMul3) = 6 :=
  mc_eq_six_of_lambda_one_two lambdaCase_one lambdaCase_two

end UnrestrictedBooleanMul.LowHalfMul3
