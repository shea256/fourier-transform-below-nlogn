import Work.FourierR11.Main
/- Modified copy of Work/Fourier233/Axioms.lean of github.com/chafreaky/wht-power-saving-lean (commit fd19e46,
   Apache-2.0): names with suffix `X` and module paths FourierR11 in place of `Y` and Fourier233. -/

/-! Axiom report for the every-length Fourier theorems at our exponent (nothing is proved here). -/

#print axioms OAI.PowerSaving.transform_mainX
#print axioms OAI.PowerSaving.convolution_mainX
#print axioms OAI.PowerSaving.transform_main_orderX
#print axioms OAI.PowerSaving.convolution_main_orderX
#print axioms OAI.PowerSaving.RAM.hillsX_program
#print OAI.PowerSaving.decimalExponentX
#print OAI.PowerSaving.alphaX
#check (OAI.PowerSaving.transform_mainX : OAI.PowerSaving.DFTGoalX)
#check (OAI.PowerSaving.convolution_mainX : OAI.PowerSaving.ConvGoalX)
