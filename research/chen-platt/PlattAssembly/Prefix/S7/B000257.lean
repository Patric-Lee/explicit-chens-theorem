import PlattAssemblyKernel
import PlattCertificates.Count131072.C068224
import PlattCertificates.Count131072.C068225
import PlattCertificates.Count131072.C068226
import PlattCertificates.Count131072.C068227
import PlattCertificates.Count131072.C068228
import PlattCertificates.Count131072.C068229
import PlattCertificates.Count131072.C068230
import PlattCertificates.Count131072.C068231
import PlattCertificates.Count131072.C068232
import PlattCertificates.Count131072.C068233
import PlattCertificates.Count131072.C068234
import PlattCertificates.Count131072.C068235
import PlattCertificates.Count131072.C068236
import PlattCertificates.Count131072.C068237
import PlattCertificates.Count131072.C068238
import PlattCertificates.Count131072.C068239
import PlattCertificates.Count131072.C068240
import PlattCertificates.Count131072.C068241
import PlattCertificates.Count131072.C068242
import PlattCertificates.Count131072.C068243
import PlattCertificates.Count131072.C068244
import PlattCertificates.Count131072.C068245
import PlattCertificates.Count131072.C068246
import PlattCertificates.Count131072.C068247
import PlattCertificates.Count131072.C068248
import PlattCertificates.Count131072.C068249
import PlattCertificates.Count131072.C068250
import PlattCertificates.Count131072.C068251
import PlattCertificates.Count131072.C068252
import PlattCertificates.Count131072.C068253
import PlattCertificates.Count131072.C068254
import PlattCertificates.Count131072.C068255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000257
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68224 : List PrefixCut := [⟨3,8180406,8180410⟩,
⟨64,178929387,178929487⟩]
theorem checked68224 : checkPrefixCuts (2^48) 8946188289 10 Manual.Count131072.C068224.packed 64 cuts68224 = true := by
 decide +kernel
def pointBounds68224 : List (Nat × Nat × Nat) := [(8946194432,115498395898484,115498785218621)]
theorem point_links_checked68224 : (cuts68224.take 1).map (fun c => (8946188289-1+2*2^10*c.k,115498387718078+c.lower,115498777038211+c.upper)) = pointBounds68224 := by
 decide +kernel
def cuts68225 : List PrefixCut := [⟨64,179870636,179870741⟩]
theorem checked68225 : checkPrefixCuts (2^48) 8946319361 10 Manual.Count131072.C068225.packed 64 cuts68225 = true := by
 decide +kernel
def cuts68226 : List PrefixCut := [⟨12,32500396,32500413⟩,
⟨64,178703903,178704005⟩]
theorem checked68226 : checkPrefixCuts (2^48) 8946450433 10 Manual.Count131072.C068226.packed 64 cuts68226 = true := by
 decide +kernel
def pointBounds68226 : List (Nat × Nat × Nat) := [(8946475008,115498779018497,115499168338852)]
theorem point_links_checked68226 : (cuts68226.take 1).map (fun c => (8946450433-1+2*2^10*c.k,115498746518101+c.lower,115499135838439+c.upper)) = pointBounds68226 := by
 decide +kernel
def cuts68227 : List PrefixCut := [⟨64,178512517,178512623⟩]
theorem checked68227 : checkPrefixCuts (2^48) 8946581505 10 Manual.Count131072.C068227.packed 64 cuts68227 = true := by
 decide +kernel
def cuts68228 : List PrefixCut := [⟨21,58391968,58392003⟩,
⟨64,179485193,179485302⟩]
theorem checked68228 : checkPrefixCuts (2^48) 8946712577 10 Manual.Count131072.C068228.packed 64 cuts68228 = true := by
 decide +kernel
def pointBounds68228 : List (Nat × Nat × Nat) := [(8946755584,115499162126489,115499551447070)]
theorem point_links_checked68228 : (cuts68228.take 1).map (fun c => (8946712577-1+2*2^10*c.k,115499103734521+c.lower,115499493055067+c.upper)) = pointBounds68228 := by
 decide +kernel
def cuts68229 : List PrefixCut := [⟨64,180866826,180866931⟩]
theorem checked68229 : checkPrefixCuts (2^48) 8946843649 10 Manual.Count131072.C068229.packed 64 cuts68229 = true := by
 decide +kernel
def cuts68230 : List PrefixCut := [⟨30,85445998,85446046⟩,
⟨64,181902365,181902471⟩]
theorem checked68230 : checkPrefixCuts (2^48) 8946974721 10 Manual.Count131072.C068230.packed 64 cuts68230 = true := by
 decide +kernel
def pointBounds68230 : List (Nat × Nat × Nat) := [(8947036160,115499549532538,115499938853346)]
theorem point_links_checked68230 : (cuts68230.take 1).map (fun c => (8946974721-1+2*2^10*c.k,115499464086540+c.lower,115499853407300+c.upper)) = pointBounds68230 := by
 decide +kernel
def cuts68231 : List PrefixCut := [⟨64,180358187,180358289⟩]
theorem checked68231 : checkPrefixCuts (2^48) 8947105793 10 Manual.Count131072.C068231.packed 64 cuts68231 = true := by
 decide +kernel
def cuts68232 : List PrefixCut := [⟨39,110264771,110264838⟩,
⟨64,179254475,179254581⟩]
theorem checked68232 : checkPrefixCuts (2^48) 8947236865 10 Manual.Count131072.C068232.packed 64 cuts68232 = true := by
 decide +kernel
def pointBounds68232 : List (Nat × Nat × Nat) := [(8947316736,115499936611863,115500325932898)]
theorem point_links_checked68232 : (cuts68232.take 1).map (fun c => (8947236865-1+2*2^10*c.k,115499826347092+c.lower,115500215668060+c.upper)) = pointBounds68232 := by
 decide +kernel
def cuts68233 : List PrefixCut := [⟨64,181611253,181611357⟩]
theorem checked68233 : checkPrefixCuts (2^48) 8947367937 10 Manual.Count131072.C068233.packed 64 cuts68233 = true := by
 decide +kernel
def cuts68234 : List PrefixCut := [⟨48,132502465,132502541⟩,
⟨64,177267337,177267439⟩]
theorem checked68234 : checkPrefixCuts (2^48) 8947499009 10 Manual.Count131072.C068234.packed 64 cuts68234 = true := by
 decide +kernel
def pointBounds68234 : List (Nat × Nat × Nat) := [(8947597312,115500319715285,115500709036539)]
theorem point_links_checked68234 : (cuts68234.take 1).map (fun c => (8947499009-1+2*2^10*c.k,115500187212820+c.lower,115500576533998+c.upper)) = pointBounds68234 := by
 decide +kernel
def cuts68235 : List PrefixCut := [⟨64,180190329,180190430⟩]
theorem checked68235 : checkPrefixCuts (2^48) 8947630081 10 Manual.Count131072.C068235.packed 64 cuts68235 = true := by
 decide +kernel
def cuts68236 : List PrefixCut := [⟨57,159331591,159331675⟩,
⟨64,178174418,178174513⟩]
theorem checked68236 : checkPrefixCuts (2^48) 8947761153 10 Manual.Count131072.C068236.packed 64 cuts68236 = true := by
 decide +kernel
def pointBounds68236 : List (Nat × Nat × Nat) := [(8947877888,115500704002077,115501093323542)]
theorem point_links_checked68236 : (cuts68236.take 1).map (fun c => (8947761153-1+2*2^10*c.k,115500544670486+c.lower,115500933991867+c.upper)) = pointBounds68236 := by
 decide +kernel
def cuts68237 : List PrefixCut := [⟨64,180593985,180594092⟩]
theorem checked68237 : checkPrefixCuts (2^48) 8947892225 10 Manual.Count131072.C068237.packed 64 cuts68237 = true := by
 decide +kernel
def cuts68238 : List PrefixCut := [⟨64,180968811,180968922⟩]
theorem checked68238 : checkPrefixCuts (2^48) 8948023297 10 Manual.Count131072.C068238.packed 64 cuts68238 = true := by
 decide +kernel
def cuts68239 : List PrefixCut := [⟨2,5819394,5819398⟩,
⟨64,180651607,180651715⟩]
theorem checked68239 : checkPrefixCuts (2^48) 8948154369 10 Manual.Count131072.C068239.packed 64 cuts68239 = true := by
 decide +kernel
def pointBounds68239 : List (Nat × Nat × Nat) := [(8948158464,115501090227094,115501479548792)]
theorem point_links_checked68239 : (cuts68239.take 1).map (fun c => (8948154369-1+2*2^10*c.k,115501084407700+c.lower,115501473729394+c.upper)) = pointBounds68239 := by
 decide +kernel
def cuts68240 : List PrefixCut := [⟨64,180428784,180428892⟩]
theorem checked68240 : checkPrefixCuts (2^48) 8948285441 10 Manual.Count131072.C068240.packed 64 cuts68240 = true := by
 decide +kernel
def cuts68241 : List PrefixCut := [⟨11,31046315,31046335⟩,
⟨64,179702660,179702766⟩]
theorem checked68241 : checkPrefixCuts (2^48) 8948416513 10 Manual.Count131072.C068241.packed 64 cuts68241 = true := by
 decide +kernel
def pointBounds68241 : List (Nat × Nat × Nat) := [(8948439040,115501476534406,115501865856336)]
theorem point_links_checked68241 : (cuts68241.take 1).map (fun c => (8948416513-1+2*2^10*c.k,115501445488091+c.lower,115501834810001+c.upper)) = pointBounds68241 := by
 decide +kernel
def cuts68242 : List PrefixCut := [⟨64,177655496,177655600⟩]
theorem checked68242 : checkPrefixCuts (2^48) 8948547585 10 Manual.Count131072.C068242.packed 64 cuts68242 = true := by
 decide +kernel
def cuts68243 : List PrefixCut := [⟨20,55390987,55391020⟩,
⟨64,179980485,179980587⟩]
theorem checked68243 : checkPrefixCuts (2^48) 8948678657 10 Manual.Count131072.C068243.packed 64 cuts68243 = true := by
 decide +kernel
def pointBounds68243 : List (Nat × Nat × Nat) := [(8948719616,115501858237234,115502247559387)]
theorem point_links_checked68243 : (cuts68243.take 1).map (fun c => (8948678657-1+2*2^10*c.k,115501802846247+c.lower,115502192168367+c.upper)) = pointBounds68243 := by
 decide +kernel
def cuts68244 : List PrefixCut := [⟨64,179694770,179694881⟩]
theorem checked68244 : checkPrefixCuts (2^48) 8948809729 10 Manual.Count131072.C068244.packed 64 cuts68244 = true := by
 decide +kernel
def cuts68245 : List PrefixCut := [⟨29,82690799,82690844⟩,
⟨64,182806001,182806106⟩]
theorem checked68245 : checkPrefixCuts (2^48) 8948940801 10 Manual.Count131072.C068245.packed 64 cuts68245 = true := by
 decide +kernel
def pointBounds68245 : List (Nat × Nat × Nat) := [(8949000192,115502245212301,115502634534679)]
theorem point_links_checked68245 : (cuts68245.take 1).map (fun c => (8948940801-1+2*2^10*c.k,115502162521502+c.lower,115502551843835+c.upper)) = pointBounds68245 := by
 decide +kernel
def cuts68246 : List PrefixCut := [⟨64,179500789,179500893⟩]
theorem checked68246 : checkPrefixCuts (2^48) 8949071873 10 Manual.Count131072.C068246.packed 64 cuts68246 = true := by
 decide +kernel
def cuts68247 : List PrefixCut := [⟨38,106434831,106434889⟩,
⟨64,180567533,180567631⟩]
theorem checked68247 : checkPrefixCuts (2^48) 8949202945 10 Manual.Count131072.C068247.packed 64 cuts68247 = true := by
 decide +kernel
def pointBounds68247 : List (Nat × Nat × Nat) := [(8949280768,115502631263123,115503020585723)]
theorem point_links_checked68247 : (cuts68247.take 1).map (fun c => (8949202945-1+2*2^10*c.k,115502524828292+c.lower,115502914150834+c.upper)) = pointBounds68247 := by
 decide +kernel
def cuts68248 : List PrefixCut := [⟨64,182357646,182357748⟩]
theorem checked68248 : checkPrefixCuts (2^48) 8949334017 10 Manual.Count131072.C068248.packed 64 cuts68248 = true := by
 decide +kernel
def cuts68249 : List PrefixCut := [⟨47,132599193,132599274⟩,
⟨64,179713074,179713182⟩]
theorem checked68249 : checkPrefixCuts (2^48) 8949465089 10 Manual.Count131072.C068249.packed 64 cuts68249 = true := by
 decide +kernel
def pointBounds68249 : List (Nat × Nat × Nat) := [(8949561344,115503020352664,115503409675487)]
theorem point_links_checked68249 : (cuts68249.take 1).map (fun c => (8949465089-1+2*2^10*c.k,115502887753471+c.lower,115503277076213+c.upper)) = pointBounds68249 := by
 decide +kernel
def cuts68250 : List PrefixCut := [⟨64,181157159,181157268⟩]
theorem checked68250 : checkPrefixCuts (2^48) 8949596161 10 Manual.Count131072.C068250.packed 64 cuts68250 = true := by
 decide +kernel
def cuts68251 : List PrefixCut := [⟨56,158070042,158070142⟩,
⟨64,180116658,180116769⟩]
theorem checked68251 : checkPrefixCuts (2^48) 8949727233 10 Manual.Count131072.C068251.packed 64 cuts68251 = true := by
 decide +kernel
def pointBounds68251 : List (Nat × Nat × Nat) := [(8949841920,115503406693746,115503796016805)]
theorem point_links_checked68251 : (cuts68251.take 1).map (fun c => (8949727233-1+2*2^10*c.k,115503248623704+c.lower,115503637946663+c.upper)) = pointBounds68251 := by
 decide +kernel
def cuts68252 : List PrefixCut := [⟨64,179390665,179390776⟩]
theorem checked68252 : checkPrefixCuts (2^48) 8949858305 10 Manual.Count131072.C068252.packed 64 cuts68252 = true := by
 decide +kernel
def cuts68253 : List PrefixCut := [⟨64,178224405,178224514⟩]
theorem checked68253 : checkPrefixCuts (2^48) 8949989377 10 Manual.Count131072.C068253.packed 64 cuts68253 = true := by
 decide +kernel
def cuts68254 : List PrefixCut := [⟨1,2358696,2358698⟩,
⟨64,179857150,179857256⟩]
theorem checked68254 : checkPrefixCuts (2^48) 8950120449 10 Manual.Count131072.C068254.packed 64 cuts68254 = true := by
 decide +kernel
def pointBounds68254 : List (Nat × Nat × Nat) := [(8950122496,115503788714128,115504178037420)]
theorem point_links_checked68254 : (cuts68254.take 1).map (fun c => (8950120449-1+2*2^10*c.k,115503786355432+c.lower,115504175678722+c.upper)) = pointBounds68254 := by
 decide +kernel
def cuts68255 : List PrefixCut := [⟨64,178093394,178093503⟩]
theorem checked68255 : checkPrefixCuts (2^48) 8950251521 10 Manual.Count131072.C068255.packed 64 cuts68255 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000257
