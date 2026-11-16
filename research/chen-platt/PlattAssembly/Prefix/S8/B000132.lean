import PlattAssemblyKernel
import PlattCertificates.Count131072.C074224
import PlattCertificates.Count131072.C074225
import PlattCertificates.Count131072.C074226
import PlattCertificates.Count131072.C074227
import PlattCertificates.Count131072.C074228
import PlattCertificates.Count131072.C074229
import PlattCertificates.Count131072.C074230
import PlattCertificates.Count131072.C074231
import PlattCertificates.Count131072.C074232
import PlattCertificates.Count131072.C074233
import PlattCertificates.Count131072.C074234
import PlattCertificates.Count131072.C074235
import PlattCertificates.Count131072.C074236
import PlattCertificates.Count131072.C074237
import PlattCertificates.Count131072.C074238
import PlattCertificates.Count131072.C074239
import PlattCertificates.Count131072.C074240
import PlattCertificates.Count131072.C074241
import PlattCertificates.Count131072.C074242
import PlattCertificates.Count131072.C074243
import PlattCertificates.Count131072.C074244
import PlattCertificates.Count131072.C074245
import PlattCertificates.Count131072.C074246
import PlattCertificates.Count131072.C074247
import PlattCertificates.Count131072.C074248
import PlattCertificates.Count131072.C074249
import PlattCertificates.Count131072.C074250
import PlattCertificates.Count131072.C074251
import PlattCertificates.Count131072.C074252
import PlattCertificates.Count131072.C074253
import PlattCertificates.Count131072.C074254
import PlattCertificates.Count131072.C074255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000132
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74224 : List PrefixCut := [⟨31,77680935,77680986⟩,
⟨64,160856243,160856347⟩]
theorem checked74224 : checkPrefixCuts (2^48) 9732620289 10 Manual.Count131072.C074224.packed 64 cuts74224 = true := by
 decide +kernel
def pointBounds74224 : List (Nat × Nat × Nat) := [(9732683776,116531597018403,116531986949589)]
theorem point_links_checked74224 : (cuts74224.take 1).map (fun c => (9732620289-1+2*2^10*c.k,116531519337468+c.lower,116531909268603+c.upper)) = pointBounds74224 := by
 decide +kernel
def cuts74225 : List PrefixCut := [⟨64,168922819,168922921⟩]
theorem checked74225 : checkPrefixCuts (2^48) 9732751361 10 Manual.Count131072.C074225.packed 64 cuts74225 = true := by
 decide +kernel
def cuts74226 : List PrefixCut := [⟨52,136848659,136848737⟩,
⟨64,168052951,168053048⟩]
theorem checked74226 : checkPrefixCuts (2^48) 9732882433 10 Manual.Count131072.C074226.packed 64 cuts74226 = true := by
 decide +kernel
def pointBounds74226 : List (Nat × Nat × Nat) := [(9732988928,116531985965189,116532375896608)]
theorem point_links_checked74226 : (cuts74226.take 1).map (fun c => (9732882433-1+2*2^10*c.k,116531849116530+c.lower,116532239047871+c.upper)) = pointBounds74226 := by
 decide +kernel
def cuts74227 : List PrefixCut := [⟨64,164204406,164204504⟩]
theorem checked74227 : checkPrefixCuts (2^48) 9733013505 10 Manual.Count131072.C074227.packed 64 cuts74227 = true := by
 decide +kernel
def cuts74228 : List PrefixCut := [⟨64,164751660,164751764⟩]
theorem checked74228 : checkPrefixCuts (2^48) 9733144577 10 Manual.Count131072.C074228.packed 64 cuts74228 = true := by
 decide +kernel
def cuts74229 : List PrefixCut := [⟨9,22730174,22730188⟩,
⟨64,163650537,163650638⟩]
theorem checked74229 : checkPrefixCuts (2^48) 9733275649 10 Manual.Count131072.C074229.packed 64 cuts74229 = true := by
 decide +kernel
def pointBounds74229 : List (Nat × Nat × Nat) := [(9733294080,116532368855721,116532758787375)]
theorem point_links_checked74229 : (cuts74229.take 1).map (fun c => (9733275649-1+2*2^10*c.k,116532346125547+c.lower,116532736057187+c.upper)) = pointBounds74229 := by
 decide +kernel
def cuts74230 : List PrefixCut := [⟨64,163850753,163850853⟩]
theorem checked74230 : checkPrefixCuts (2^48) 9733406721 10 Manual.Count131072.C074230.packed 64 cuts74230 = true := by
 decide +kernel
def cuts74231 : List PrefixCut := [⟨30,80247325,80247368⟩,
⟨64,166537923,166538016⟩]
theorem checked74231 : checkPrefixCuts (2^48) 9733537793 10 Manual.Count131072.C074231.packed 64 cuts74231 = true := by
 decide +kernel
def pointBounds74231 : List (Nat × Nat × Nat) := [(9733599232,116532753874162,116533143806046)]
theorem point_links_checked74231 : (cuts74231.take 1).map (fun c => (9733537793-1+2*2^10*c.k,116532673626837+c.lower,116533063558678+c.upper)) = pointBounds74231 := by
 decide +kernel
def cuts74232 : List PrefixCut := [⟨64,164540360,164540459⟩]
theorem checked74232 : checkPrefixCuts (2^48) 9733668865 10 Manual.Count131072.C074232.packed 64 cuts74232 = true := by
 decide +kernel
def cuts74233 : List PrefixCut := [⟨51,132584957,132585037⟩,
⟨64,165608076,165608176⟩]
theorem checked74233 : checkPrefixCuts (2^48) 9733799937 10 Manual.Count131072.C074233.packed 64 cuts74233 = true := by
 decide +kernel
def pointBounds74233 : List (Nat × Nat × Nat) := [(9733904384,116533137290077,116533527222190)]
theorem point_links_checked74233 : (cuts74233.take 1).map (fun c => (9733799937-1+2*2^10*c.k,116533004705120+c.lower,116533394637153+c.upper)) = pointBounds74233 := by
 decide +kernel
def cuts74234 : List PrefixCut := [⟨64,163899751,163899852⟩]
theorem checked74234 : checkPrefixCuts (2^48) 9733931009 10 Manual.Count131072.C074234.packed 64 cuts74234 = true := by
 decide +kernel
def cuts74235 : List PrefixCut := [⟨64,163550560,163550660⟩]
theorem checked74235 : checkPrefixCuts (2^48) 9734062081 10 Manual.Count131072.C074235.packed 64 cuts74235 = true := by
 decide +kernel
def cuts74236 : List PrefixCut := [⟨8,21282232,21282243⟩,
⟨64,166237530,166237626⟩]
theorem checked74236 : checkPrefixCuts (2^48) 9734193153 10 Manual.Count131072.C074236.packed 64 cuts74236 = true := by
 decide +kernel
def pointBounds74236 : List (Nat × Nat × Nat) := [(9734209536,116533519045739,116533908978084)]
theorem point_links_checked74236 : (cuts74236.take 1).map (fun c => (9734193153-1+2*2^10*c.k,116533497763507+c.lower,116533887695841+c.upper)) = pointBounds74236 := by
 decide +kernel
def cuts74237 : List PrefixCut := [⟨64,164037721,164037818⟩]
theorem checked74237 : checkPrefixCuts (2^48) 9734324225 10 Manual.Count131072.C074237.packed 64 cuts74237 = true := by
 decide +kernel
def cuts74238 : List PrefixCut := [⟨29,74341064,74341108⟩,
⟨64,164411408,164411500⟩]
theorem checked74238 : checkPrefixCuts (2^48) 9734455297 10 Manual.Count131072.C074238.packed 64 cuts74238 = true := by
 decide +kernel
def pointBounds74238 : List (Nat × Nat × Nat) := [(9734514688,116533902379822,116534292312393)]
theorem point_links_checked74238 : (cuts74238.take 1).map (fun c => (9734455297-1+2*2^10*c.k,116533828038758+c.lower,116534217971285+c.upper)) = pointBounds74238 := by
 decide +kernel
def cuts74239 : List PrefixCut := [⟨64,164177869,164177975⟩]
theorem checked74239 : checkPrefixCuts (2^48) 9734586369 10 Manual.Count131072.C074239.packed 64 cuts74239 = true := by
 decide +kernel
def cuts74240 : List PrefixCut := [⟨50,127396788,127396866⟩,
⟨64,163076906,163077004⟩]
theorem checked74240 : checkPrefixCuts (2^48) 9734717441 10 Manual.Count131072.C074240.packed 64 cuts74240 = true := by
 decide +kernel
def pointBounds74240 : List (Nat × Nat × Nat) := [(9734819840,116534284024823,116534673957626)]
theorem point_links_checked74240 : (cuts74240.take 1).map (fun c => (9734717441-1+2*2^10*c.k,116534156628035+c.lower,116534546560760+c.upper)) = pointBounds74240 := by
 decide +kernel
def cuts74241 : List PrefixCut := [⟨64,164693910,164694005⟩]
theorem checked74241 : checkPrefixCuts (2^48) 9734848513 10 Manual.Count131072.C074241.packed 64 cuts74241 = true := by
 decide +kernel
def cuts74242 : List PrefixCut := [⟨64,164431453,164431552⟩]
theorem checked74242 : checkPrefixCuts (2^48) 9734979585 10 Manual.Count131072.C074242.packed 64 cuts74242 = true := by
 decide +kernel
def cuts74243 : List PrefixCut := [⟨7,17666058,17666069⟩,
⟨64,163735324,163735419⟩]
theorem checked74243 : checkPrefixCuts (2^48) 9735110657 10 Manual.Count131072.C074243.packed 64 cuts74243 = true := by
 decide +kernel
def pointBounds74243 : List (Nat × Nat × Nat) := [(9735124992,116534666496362,116535056429390)]
theorem point_links_checked74243 : (cuts74243.take 1).map (fun c => (9735110657-1+2*2^10*c.k,116534648830304+c.lower,116535038763321+c.upper)) = pointBounds74243 := by
 decide +kernel
def cuts74244 : List PrefixCut := [⟨64,166219617,166219718⟩]
theorem checked74244 : checkPrefixCuts (2^48) 9735241729 10 Manual.Count131072.C074244.packed 64 cuts74244 = true := by
 decide +kernel
def cuts74245 : List PrefixCut := [⟨28,70633263,70633310⟩,
⟨64,163962217,163962319⟩]
theorem checked74245 : checkPrefixCuts (2^48) 9735372801 10 Manual.Count131072.C074245.packed 64 cuts74245 = true := by
 decide +kernel
def pointBounds74245 : List (Nat × Nat × Nat) := [(9735430144,116535049418508,116535439351768)]
theorem point_links_checked74245 : (cuts74245.take 1).map (fun c => (9735372801-1+2*2^10*c.k,116534978785245+c.lower,116535368718458+c.upper)) = pointBounds74245 := by
 decide +kernel
def cuts74246 : List PrefixCut := [⟨64,165174318,165174419⟩]
theorem checked74246 : checkPrefixCuts (2^48) 9735503873 10 Manual.Count131072.C074246.packed 64 cuts74246 = true := by
 decide +kernel
def cuts74247 : List PrefixCut := [⟨49,125360990,125361066⟩,
⟨64,164536036,164536136⟩]
theorem checked74247 : checkPrefixCuts (2^48) 9735634945 10 Manual.Count131072.C074247.packed 64 cuts74247 = true := by
 decide +kernel
def pointBounds74247 : List (Nat × Nat × Nat) := [(9735735296,116535433282770,116535823216262)]
theorem point_links_checked74247 : (cuts74247.take 1).map (fun c => (9735634945-1+2*2^10*c.k,116535307921780+c.lower,116535697855196+c.upper)) = pointBounds74247 := by
 decide +kernel
def cuts74248 : List PrefixCut := [⟨64,164765122,164765224⟩]
theorem checked74248 : checkPrefixCuts (2^48) 9735766017 10 Manual.Count131072.C074248.packed 64 cuts74248 = true := by
 decide +kernel
def cuts74249 : List PrefixCut := [⟨64,164705075,164705174⟩]
theorem checked74249 : checkPrefixCuts (2^48) 9735897089 10 Manual.Count131072.C074249.packed 64 cuts74249 = true := by
 decide +kernel
def cuts74250 : List PrefixCut := [⟨6,15929757,15929768⟩,
⟨64,167015695,167015788⟩]
theorem checked74250 : checkPrefixCuts (2^48) 9736028161 10 Manual.Count131072.C074250.packed 64 cuts74250 = true := by
 decide +kernel
def pointBounds74250 : List (Nat × Nat × Nat) := [(9736040448,116535817857770,116536207791498)]
theorem point_links_checked74250 : (cuts74250.take 1).map (fun c => (9736028161-1+2*2^10*c.k,116535801928013+c.lower,116536191861730+c.upper)) = pointBounds74250 := by
 decide +kernel
def cuts74251 : List PrefixCut := [⟨64,164093525,164093620⟩]
theorem checked74251 : checkPrefixCuts (2^48) 9736159233 10 Manual.Count131072.C074251.packed 64 cuts74251 = true := by
 decide +kernel
def cuts74252 : List PrefixCut := [⟨27,69296761,69296804⟩,
⟨64,164814062,164814160⟩]
theorem checked74252 : checkPrefixCuts (2^48) 9736290305 10 Manual.Count131072.C074252.packed 64 cuts74252 = true := by
 decide +kernel
def pointBounds74252 : List (Nat × Nat × Nat) := [(9736345600,116536202333994,116536592267942)]
theorem point_links_checked74252 : (cuts74252.take 1).map (fun c => (9736290305-1+2*2^10*c.k,116536133037233+c.lower,116536522971138+c.upper)) = pointBounds74252 := by
 decide +kernel
def cuts74253 : List PrefixCut := [⟨64,166344036,166344136⟩]
theorem checked74253 : checkPrefixCuts (2^48) 9736421377 10 Manual.Count131072.C074253.packed 64 cuts74253 = true := by
 decide +kernel
def cuts74254 : List PrefixCut := [⟨48,124424107,124424177⟩,
⟨64,165792529,165792625⟩]
theorem checked74254 : checkPrefixCuts (2^48) 9736552449 10 Manual.Count131072.C074254.packed 64 cuts74254 = true := by
 decide +kernel
def pointBounds74254 : List (Nat × Nat × Nat) := [(9736650752,116536588619438,116536978553611)]
theorem point_links_checked74254 : (cuts74254.take 1).map (fun c => (9736552449-1+2*2^10*c.k,116536464195331+c.lower,116536854129434+c.upper)) = pointBounds74254 := by
 decide +kernel
def cuts74255 : List PrefixCut := [⟨64,164258155,164258249⟩]
theorem checked74255 : checkPrefixCuts (2^48) 9736683521 10 Manual.Count131072.C074255.packed 64 cuts74255 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000132
