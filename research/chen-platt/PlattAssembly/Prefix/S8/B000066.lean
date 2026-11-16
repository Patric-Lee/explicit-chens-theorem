import PlattAssemblyKernel
import PlattCertificates.Count131072.C072112
import PlattCertificates.Count131072.C072113
import PlattCertificates.Count131072.C072114
import PlattCertificates.Count131072.C072115
import PlattCertificates.Count131072.C072116
import PlattCertificates.Count131072.C072117
import PlattCertificates.Count131072.C072118
import PlattCertificates.Count131072.C072119
import PlattCertificates.Count131072.C072120
import PlattCertificates.Count131072.C072121
import PlattCertificates.Count131072.C072122
import PlattCertificates.Count131072.C072123
import PlattCertificates.Count131072.C072124
import PlattCertificates.Count131072.C072125
import PlattCertificates.Count131072.C072126
import PlattCertificates.Count131072.C072127
import PlattCertificates.Count131072.C072128
import PlattCertificates.Count131072.C072129
import PlattCertificates.Count131072.C072130
import PlattCertificates.Count131072.C072131
import PlattCertificates.Count131072.C072132
import PlattCertificates.Count131072.C072133
import PlattCertificates.Count131072.C072134
import PlattCertificates.Count131072.C072135
import PlattCertificates.Count131072.C072136
import PlattCertificates.Count131072.C072137
import PlattCertificates.Count131072.C072138
import PlattCertificates.Count131072.C072139
import PlattCertificates.Count131072.C072140
import PlattCertificates.Count131072.C072141
import PlattCertificates.Count131072.C072142
import PlattCertificates.Count131072.C072143
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72112 : List PrefixCut := [⟨60,159522708,159522804⟩,
⟨64,169673271,169673373⟩]
theorem checked72112 : checkPrefixCuts (2^48) 9455796225 10 Manual.Count131072.C072112.packed 64 cuts72112 = true := by
 decide +kernel
def pointBounds72112 : List (Nat × Nat × Nat) := [(9455919104,116178254346561,116178644067129)]
theorem point_links_checked72112 : (cuts72112.take 1).map (fun c => (9455796225-1+2*2^10*c.k,116178094823853+c.lower,116178484544325+c.upper)) = pointBounds72112 := by
 decide +kernel
def cuts72113 : List PrefixCut := [⟨64,170176948,170177050⟩]
theorem checked72113 : checkPrefixCuts (2^48) 9455927297 10 Manual.Count131072.C072113.packed 64 cuts72113 = true := by
 decide +kernel
def cuts72114 : List PrefixCut := [⟨64,170115051,170115154⟩]
theorem checked72114 : checkPrefixCuts (2^48) 9456058369 10 Manual.Count131072.C072114.packed 64 cuts72114 = true := by
 decide +kernel
def cuts72115 : List PrefixCut := [⟨13,33903663,33903681⟩,
⟨64,167374228,167374326⟩]
theorem checked72115 : checkPrefixCuts (2^48) 9456189441 10 Manual.Count131072.C072115.packed 64 cuts72115 = true := by
 decide +kernel
def pointBounds72115 : List (Nat × Nat × Nat) := [(9456216064,116178638692786,116179028413583)]
theorem point_links_checked72115 : (cuts72115.take 1).map (fun c => (9456189441-1+2*2^10*c.k,116178604789123+c.lower,116178994509902+c.upper)) = pointBounds72115 := by
 decide +kernel
def cuts72116 : List PrefixCut := [⟨64,169574553,169574647⟩]
theorem checked72116 : checkPrefixCuts (2^48) 9456320513 10 Manual.Count131072.C072116.packed 64 cuts72116 = true := by
 decide +kernel
def cuts72117 : List PrefixCut := [⟨30,79503074,79503120⟩,
⟨64,170643748,170643845⟩]
theorem checked72117 : checkPrefixCuts (2^48) 9456451585 10 Manual.Count131072.C072117.packed 64 cuts72117 = true := by
 decide +kernel
def pointBounds72117 : List (Nat × Nat × Nat) := [(9456513024,116179021240978,116179410961995)]
theorem point_links_checked72117 : (cuts72117.take 1).map (fun c => (9456451585-1+2*2^10*c.k,116178941737904+c.lower,116179331458875+c.upper)) = pointBounds72117 := by
 decide +kernel
def cuts72118 : List PrefixCut := [⟨64,169034105,169034206⟩]
theorem checked72118 : checkPrefixCuts (2^48) 9456582657 10 Manual.Count131072.C072118.packed 64 cuts72118 = true := by
 decide +kernel
def cuts72119 : List PrefixCut := [⟨47,125486733,125486810⟩,
⟨64,170728315,170728420⟩]
theorem checked72119 : checkPrefixCuts (2^48) 9456713729 10 Manual.Count131072.C072119.packed 64 cuts72119 = true := by
 decide +kernel
def pointBounds72119 : List (Nat × Nat × Nat) := [(9456809984,116179406902490,116179796623736)]
theorem point_links_checked72119 : (cuts72119.take 1).map (fun c => (9456713729-1+2*2^10*c.k,116179281415757+c.lower,116179671136926+c.upper)) = pointBounds72119 := by
 decide +kernel
def cuts72120 : List PrefixCut := [⟨64,168731764,168731867⟩]
theorem checked72120 : checkPrefixCuts (2^48) 9456844801 10 Manual.Count131072.C072120.packed 64 cuts72120 = true := by
 decide +kernel
def cuts72121 : List PrefixCut := [⟨64,171497432,171497540⟩]
theorem checked72121 : checkPrefixCuts (2^48) 9456975873 10 Manual.Count131072.C072121.packed 64 cuts72121 = true := by
 decide +kernel
def pointBounds72121 : List (Nat × Nat × Nat) := [(9457106944,116179792373268,116180182094753)]
theorem point_links_checked72121 : (cuts72121.take 1).map (fun c => (9456975873-1+2*2^10*c.k,116179620875836+c.lower,116180010597213+c.upper)) = pointBounds72121 := by
 decide +kernel
def cuts72122 : List PrefixCut := [⟨64,169114001,169114104⟩]
theorem checked72122 : checkPrefixCuts (2^48) 9457106945 10 Manual.Count131072.C072122.packed 64 cuts72122 = true := by
 decide +kernel
def cuts72123 : List PrefixCut := [⟨64,172087933,172088028⟩]
theorem checked72123 : checkPrefixCuts (2^48) 9457238017 10 Manual.Count131072.C072123.packed 64 cuts72123 = true := by
 decide +kernel
def cuts72124 : List PrefixCut := [⟨17,44822236,44822259⟩,
⟨64,169645047,169645138⟩]
theorem checked72124 : checkPrefixCuts (2^48) 9457369089 10 Manual.Count131072.C072124.packed 64 cuts72124 = true := by
 decide +kernel
def pointBounds72124 : List (Nat × Nat × Nat) := [(9457403904,116180178397438,116180568119144)]
theorem point_links_checked72124 : (cuts72124.take 1).map (fun c => (9457369089-1+2*2^10*c.k,116180133575202+c.lower,116180523296885+c.upper)) = pointBounds72124 := by
 decide +kernel
def cuts72125 : List PrefixCut := [⟨64,170327206,170327307⟩]
theorem checked72125 : checkPrefixCuts (2^48) 9457500161 10 Manual.Count131072.C072125.packed 64 cuts72125 = true := by
 decide +kernel
def cuts72126 : List PrefixCut := [⟨34,90266811,90266861⟩,
⟨64,169818908,169819006⟩]
theorem checked72126 : checkPrefixCuts (2^48) 9457631233 10 Manual.Count131072.C072126.packed 64 cuts72126 = true := by
 decide +kernel
def pointBounds72126 : List (Nat × Nat × Nat) := [(9457700864,116180563814266,116180953536191)]
theorem point_links_checked72126 : (cuts72126.take 1).map (fun c => (9457631233-1+2*2^10*c.k,116180473547455+c.lower,116180863269330+c.upper)) = pointBounds72126 := by
 decide +kernel
def cuts72127 : List PrefixCut := [⟨64,168715390,168715489⟩]
theorem checked72127 : checkPrefixCuts (2^48) 9457762305 10 Manual.Count131072.C072127.packed 64 cuts72127 = true := by
 decide +kernel
def cuts72128 : List PrefixCut := [⟨51,134994443,134994525⟩,
⟨64,169010665,169010767⟩]
theorem checked72128 : checkPrefixCuts (2^48) 9457893377 10 Manual.Count131072.C072128.packed 64 cuts72128 = true := by
 decide +kernel
def pointBounds72128 : List (Nat × Nat × Nat) := [(9457997824,116180947076196,116181336798350)]
theorem point_links_checked72128 : (cuts72128.take 1).map (fun c => (9457893377-1+2*2^10*c.k,116180812081753+c.lower,116181201803825+c.upper)) = pointBounds72128 := by
 decide +kernel
def cuts72129 : List PrefixCut := [⟨64,171151053,171151155⟩]
theorem checked72129 : checkPrefixCuts (2^48) 9458024449 10 Manual.Count131072.C072129.packed 64 cuts72129 = true := by
 decide +kernel
def cuts72130 : List PrefixCut := [⟨64,169363098,169363198⟩]
theorem checked72130 : checkPrefixCuts (2^48) 9458155521 10 Manual.Count131072.C072130.packed 64 cuts72130 = true := by
 decide +kernel
def cuts72131 : List PrefixCut := [⟨4,10356338,10356345⟩,
⟨64,171473673,171473772⟩]
theorem checked72131 : checkPrefixCuts (2^48) 9458286593 10 Manual.Count131072.C072131.packed 64 cuts72131 = true := by
 decide +kernel
def pointBounds72131 : List (Nat × Nat × Nat) := [(9458294784,116181331962907,116181721685290)]
theorem point_links_checked72131 : (cuts72131.take 1).map (fun c => (9458286593-1+2*2^10*c.k,116181321606569+c.lower,116181711328945+c.upper)) = pointBounds72131 := by
 decide +kernel
def cuts72132 : List PrefixCut := [⟨64,170429730,170429827⟩]
theorem checked72132 : checkPrefixCuts (2^48) 9458417665 10 Manual.Count131072.C072132.packed 64 cuts72132 = true := by
 decide +kernel
def cuts72133 : List PrefixCut := [⟨21,54964345,54964382⟩,
⟨64,168433537,168433639⟩]
theorem checked72133 : checkPrefixCuts (2^48) 9458548737 10 Manual.Count131072.C072133.packed 64 cuts72133 = true := by
 decide +kernel
def pointBounds72133 : List (Nat × Nat × Nat) := [(9458591744,116181718474317,116182108196926)]
theorem point_links_checked72133 : (cuts72133.take 1).map (fun c => (9458548737-1+2*2^10*c.k,116181663509972+c.lower,116182053232544+c.upper)) = pointBounds72133 := by
 decide +kernel
def cuts72134 : List PrefixCut := [⟨64,168996602,168996708⟩]
theorem checked72134 : checkPrefixCuts (2^48) 9458679809 10 Manual.Count131072.C072134.packed 64 cuts72134 = true := by
 decide +kernel
def cuts72135 : List PrefixCut := [⟨38,102039612,102039677⟩,
⟨64,169202581,169202682⟩]
theorem checked72135 : checkPrefixCuts (2^48) 9458810881 10 Manual.Count131072.C072135.packed 64 cuts72135 = true := by
 decide +kernel
def pointBounds72135 : List (Nat × Nat × Nat) := [(9458888704,116182102979723,116182492702568)]
theorem point_links_checked72135 : (cuts72135.take 1).map (fun c => (9458810881-1+2*2^10*c.k,116182000940111+c.lower,116182390662891+c.upper)) = pointBounds72135 := by
 decide +kernel
def cuts72136 : List PrefixCut := [⟨64,172860379,172860480⟩]
theorem checked72136 : checkPrefixCuts (2^48) 9458941953 10 Manual.Count131072.C072136.packed 64 cuts72136 = true := by
 decide +kernel
def cuts72137 : List PrefixCut := [⟨55,145838842,145838923⟩,
⟨64,170090594,170090688⟩]
theorem checked72137 : checkPrefixCuts (2^48) 9459073025 10 Manual.Count131072.C072137.packed 64 cuts72137 = true := by
 decide +kernel
def pointBounds72137 : List (Nat × Nat × Nat) := [(9459185664,116182488841913,116182878564976)]
theorem point_links_checked72137 : (cuts72137.take 1).map (fun c => (9459073025-1+2*2^10*c.k,116182343003071+c.lower,116182732726053+c.upper)) = pointBounds72137 := by
 decide +kernel
def cuts72138 : List PrefixCut := [⟨64,169136028,169136135⟩]
theorem checked72138 : checkPrefixCuts (2^48) 9459204097 10 Manual.Count131072.C072138.packed 64 cuts72138 = true := by
 decide +kernel
def cuts72139 : List PrefixCut := [⟨64,171008315,171008417⟩]
theorem checked72139 : checkPrefixCuts (2^48) 9459335169 10 Manual.Count131072.C072139.packed 64 cuts72139 = true := by
 decide +kernel
def cuts72140 : List PrefixCut := [⟨8,21513492,21513507⟩,
⟨64,168744528,168744629⟩]
theorem checked72140 : checkPrefixCuts (2^48) 9459466241 10 Manual.Count131072.C072140.packed 64 cuts72140 = true := by
 decide +kernel
def pointBounds72140 : List (Nat × Nat × Nat) := [(9459482624,116182874751500,116183264474800)]
theorem point_links_checked72140 : (cuts72140.take 1).map (fun c => (9459466241-1+2*2^10*c.k,116182853238008+c.lower,116183242961293+c.upper)) = pointBounds72140 := by
 decide +kernel
def cuts72141 : List PrefixCut := [⟨64,168980226,168980323⟩]
theorem checked72141 : checkPrefixCuts (2^48) 9459597313 10 Manual.Count131072.C072141.packed 64 cuts72141 = true := by
 decide +kernel
def cuts72142 : List PrefixCut := [⟨25,63437638,63437681⟩,
⟨64,167162819,167162922⟩]
theorem checked72142 : checkPrefixCuts (2^48) 9459728385 10 Manual.Count131072.C072142.packed 64 cuts72142 = true := by
 decide +kernel
def pointBounds72142 : List (Nat × Nat × Nat) := [(9459779584,116183254400400,116183644123926)]
theorem point_links_checked72142 : (cuts72142.take 1).map (fun c => (9459728385-1+2*2^10*c.k,116183190962762+c.lower,116183580686245+c.upper)) = pointBounds72142 := by
 decide +kernel
def cuts72143 : List PrefixCut := [⟨64,171177364,171177470⟩]
theorem checked72143 : checkPrefixCuts (2^48) 9459859457 10 Manual.Count131072.C072143.packed 64 cuts72143 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000066
