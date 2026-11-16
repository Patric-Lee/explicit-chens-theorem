import PlattAssemblyKernel
import PlattCertificates.Count131072.C019216
import PlattCertificates.Count131072.C019217
import PlattCertificates.Count131072.C019218
import PlattCertificates.Count131072.C019219
import PlattCertificates.Count131072.C019220
import PlattCertificates.Count131072.C019221
import PlattCertificates.Count131072.C019222
import PlattCertificates.Count131072.C019223
import PlattCertificates.Count131072.C019224
import PlattCertificates.Count131072.C019225
import PlattCertificates.Count131072.C019226
import PlattCertificates.Count131072.C019227
import PlattCertificates.Count131072.C019228
import PlattCertificates.Count131072.C019229
import PlattCertificates.Count131072.C019230
import PlattCertificates.Count131072.C019231
import PlattCertificates.Count131072.C019232
import PlattCertificates.Count131072.C019233
import PlattCertificates.Count131072.C019234
import PlattCertificates.Count131072.C019235
import PlattCertificates.Count131072.C019236
import PlattCertificates.Count131072.C019237
import PlattCertificates.Count131072.C019238
import PlattCertificates.Count131072.C019239
import PlattCertificates.Count131072.C019240
import PlattCertificates.Count131072.C019241
import PlattCertificates.Count131072.C019242
import PlattCertificates.Count131072.C019243
import PlattCertificates.Count131072.C019244
import PlattCertificates.Count131072.C019245
import PlattCertificates.Count131072.C019246
import PlattCertificates.Count131072.C019247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000288
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19216 : List PrefixCut := [⟨43,219365815,219365947⟩,
⟨120,631196711,631197085⟩,
⟨128,671810055,671810454⟩]
theorem checked19216 : checkPrefixCuts (2^48) 2522611713 9 Manual.Count131072.C019216.packed 128 cuts19216 = true := by
 decide +kernel
def pointBounds19216 : List (Nat × Nat × Nat) := [(2522655744,99502312727190,99502692790066),(2522734592,99502724558086,99503104621204)]
theorem point_links_checked19216 : (cuts19216.take 2).map (fun c => (2522611713-1+2*2^9*c.k,99502093361375+c.lower,99502473424119+c.upper)) = pointBounds19216 := by
 decide +kernel
def cuts19217 : List PrefixCut := [⟨69,365849135,365849346⟩,
⟨128,678246514,678246912⟩]
theorem checked19217 : checkPrefixCuts (2^48) 2522742785 9 Manual.Count131072.C019217.packed 128 cuts19217 = true := by
 decide +kernel
def pointBounds19217 : List (Nat × Nat × Nat) := [(2522813440,99503131020565,99503511083919)]
theorem point_links_checked19217 : (cuts19217.take 1).map (fun c => (2522742785-1+2*2^9*c.k,99502765171430+c.lower,99503145234573+c.upper)) = pointBounds19217 := by
 decide +kernel
def cuts19218 : List PrefixCut := [⟨18,95837541,95837598⟩,
⟨95,504171308,504171610⟩,
⟨128,673525636,673526041⟩]
theorem checked19218 : checkPrefixCuts (2^48) 2522873857 9 Manual.Count131072.C019218.packed 128 cuts19218 = true := by
 decide +kernel
def pointBounds19218 : List (Nat × Nat × Nat) := [(2522892288,99503539255485,99503919319083),(2522971136,99503947589252,99504327653095)]
theorem point_links_checked19218 : (cuts19218.take 2).map (fun c => (2522873857-1+2*2^9*c.k,99503443417944+c.lower,99503823481485+c.upper)) = pointBounds19218 := by
 decide +kernel
def cuts19219 : List PrefixCut := [⟨44,227810349,227810486⟩,
⟨121,631767770,631768142⟩,
⟨128,668247144,668247537⟩]
theorem checked19219 : checkPrefixCuts (2^48) 2523004929 9 Manual.Count131072.C019219.packed 128 cuts19219 = true := by
 decide +kernel
def pointBounds19219 : List (Nat × Nat × Nat) := [(2523049984,99504344753929,99504724818012),(2523128832,99504748711350,99505128775668)]
theorem point_links_checked19219 : (cuts19219.take 2).map (fun c => (2523004929-1+2*2^9*c.k,99504116943580+c.lower,99504497007526+c.upper)) = pointBounds19219 := by
 decide +kernel
def cuts19220 : List PrefixCut := [⟨70,370923602,370923823⟩,
⟨128,676132809,676133212⟩]
theorem checked19220 : checkPrefixCuts (2^48) 2523136001 9 Manual.Count131072.C019220.packed 128 cuts19220 = true := by
 decide +kernel
def pointBounds19220 : List (Nat × Nat × Nat) := [(2523207680,99505156114326,99505536178886)]
theorem point_links_checked19220 : (cuts19220.take 1).map (fun c => (2523136001-1+2*2^9*c.k,99504785190724+c.lower,99505165255063+c.upper)) = pointBounds19220 := by
 decide +kernel
def cuts19221 : List PrefixCut := [⟨20,104188921,104188985⟩,
⟨98,515135798,515136104⟩,
⟨128,672416548,672416951⟩]
theorem checked19221 : checkPrefixCuts (2^48) 2523267073 9 Manual.Count131072.C019221.packed 128 cuts19221 = true := by
 decide +kernel
def pointBounds19221 : List (Nat × Nat × Nat) := [(2523287552,99505565512454,99505945577260),(2523367424,99505976459331,99506356524379)]
theorem point_links_checked19221 : (cuts19221.take 2).map (fun c => (2523267073-1+2*2^9*c.k,99505461323533+c.lower,99505841388275+c.upper)) = pointBounds19221 := by
 decide +kernel
def cuts19222 : List PrefixCut := [⟨48,253318440,253318591⟩,
⟨126,668589460,668589860⟩,
⟨128,679855023,679855429⟩]
theorem checked19222 : checkPrefixCuts (2^48) 2523398145 9 Manual.Count131072.C019222.packed 128 cuts19222 = true := by
 decide +kernel
def pointBounds19222 : List (Nat × Nat × Nat) := [(2523447296,99506387058521,99506767123817),(2523527168,99506802329541,99507182395086)]
theorem point_links_checked19222 : (cuts19222.take 2).map (fun c => (2523398145-1+2*2^9*c.k,99506133740081+c.lower,99506513805226+c.upper)) = pointBounds19222 := by
 decide +kernel
def cuts19223 : List PrefixCut := [⟨76,398526910,398527147⟩,
⟨128,673350561,673350964⟩]
theorem checked19223 : checkPrefixCuts (2^48) 2523529217 9 Manual.Count131072.C019223.packed 128 cuts19223 = true := by
 decide +kernel
def pointBounds19223 : List (Nat × Nat × Nat) := [(2523607040,99507212122014,99507592187802)]
theorem point_links_checked19223 : (cuts19223.take 1).map (fun c => (2523529217-1+2*2^9*c.k,99506813595104+c.lower,99507193660655+c.upper)) = pointBounds19223 := by
 decide +kernel
def cuts19224 : List PrefixCut := [⟨26,141536368,141536452⟩,
⟨104,551525951,551526279⟩,
⟨128,677888465,677888870⟩]
theorem checked19224 : checkPrefixCuts (2^48) 2523660289 9 Manual.Count131072.C019224.packed 128 cuts19224 = true := by
 decide +kernel
def pointBounds19224 : List (Nat × Nat × Nat) := [(2523686912,99507628482033,99508008548071),(2523766784,99508038471616,99508418537898)]
theorem point_links_checked19224 : (cuts19224.take 2).map (fun c => (2523660289-1+2*2^9*c.k,99507486945665+c.lower,99507867011619+c.upper)) = pointBounds19224 := by
 decide +kernel
def cuts19225 : List PrefixCut := [⟨54,286959916,286960090⟩,
⟨128,676849487,676849893⟩]
theorem checked19225 : checkPrefixCuts (2^48) 2523791361 9 Manual.Count131072.C019225.packed 128 cuts19225 = true := by
 decide +kernel
def pointBounds19225 : List (Nat × Nat × Nat) := [(2523846656,99508451794046,99508831860579)]
theorem point_links_checked19225 : (cuts19225.take 1).map (fun c => (2523791361-1+2*2^9*c.k,99508164834130+c.lower,99508544900489+c.upper)) = pointBounds19225 := by
 decide +kernel
def cuts19226 : List PrefixCut := [⟨4,21077792,21077804⟩,
⟨82,432366724,432366984⟩,
⟨128,680271323,680271731⟩]
theorem checked19226 : checkPrefixCuts (2^48) 2523922433 9 Manual.Count131072.C019226.packed 128 cuts19226 = true := by
 decide +kernel
def pointBounds19226 : List (Nat × Nat × Nat) := [(2523926528,99508862761409,99509242828186),(2524006400,99509274050341,99509654117366)]
theorem point_links_checked19226 : (cuts19226.take 2).map (fun c => (2523922433-1+2*2^9*c.k,99508841683617+c.lower,99509221750382+c.upper)) = pointBounds19226 := by
 decide +kernel
def cuts19227 : List PrefixCut := [⟨32,172627226,172627326⟩,
⟨110,576864694,576865034⟩,
⟨128,672541675,672542072⟩]
theorem checked19227 : checkPrefixCuts (2^48) 2524053505 9 Manual.Count131072.C019227.packed 128 cuts19227 = true := by
 decide +kernel
def pointBounds19227 : List (Nat × Nat × Nat) := [(2524086272,99509694582166,99510074649439),(2524166144,99510098819634,99510478887147)]
theorem point_links_checked19227 : (cuts19227.take 2).map (fun c => (2524053505-1+2*2^9*c.k,99509521954940+c.lower,99509902022113+c.upper)) = pointBounds19227 := by
 decide +kernel
def cuts19228 : List PrefixCut := [⟨60,310889481,310889669⟩,
⟨128,670387982,670388385⟩]
theorem checked19228 : checkPrefixCuts (2^48) 2524184577 9 Manual.Count131072.C019228.packed 128 cuts19228 = true := by
 decide +kernel
def pointBounds19228 : List (Nat × Nat × Nat) := [(2524246016,99510505386096,99510885453854)]
theorem point_links_checked19228 : (cuts19228.take 1).map (fun c => (2524184577-1+2*2^9*c.k,99510194496615+c.lower,99510574564185+c.upper)) = pointBounds19228 := by
 decide +kernel
def cuts19229 : List PrefixCut := [⟨10,55641094,55641126⟩,
⟨88,464188833,464189111⟩,
⟨128,675705359,675705762⟩]
theorem checked19229 : checkPrefixCuts (2^48) 2524315649 9 Manual.Count131072.C019229.packed 128 cuts19229 = true := by
 decide +kernel
def pointBounds19229 : List (Nat × Nat × Nat) := [(2524325888,99510920525691,99511300593696),(2524405760,99511329073430,99511709141681)]
theorem point_links_checked19229 : (cuts19229.take 2).map (fun c => (2524315649-1+2*2^9*c.k,99510864884597+c.lower,99511244952570+c.upper)) = pointBounds19229 := by
 decide +kernel
def cuts19230 : List PrefixCut := [⟨38,199025318,199025438⟩,
⟨116,610557617,610557985⟩,
⟨128,671879382,671879788⟩]
theorem checked19230 : checkPrefixCuts (2^48) 2524446721 9 Manual.Count131072.C019230.packed 128 cuts19230 = true := by
 decide +kernel
def pointBounds19230 : List (Nat × Nat × Nat) := [(2524485632,99511739615274,99512119683770),(2524565504,99512151147573,99512531216317)]
theorem point_links_checked19230 : (cuts19230.take 2).map (fun c => (2524446721-1+2*2^9*c.k,99511540589956+c.lower,99511920658332+c.upper)) = pointBounds19230 := by
 decide +kernel
def cuts19231 : List PrefixCut := [⟨66,347856200,347856410⟩,
⟨128,671956123,671956527⟩]
theorem checked19231 : checkPrefixCuts (2^48) 2524577793 9 Manual.Count131072.C019231.packed 128 cuts19231 = true := by
 decide +kernel
def pointBounds19231 : List (Nat × Nat × Nat) := [(2524645376,99512560325538,99512940394530)]
theorem point_links_checked19231 : (cuts19231.take 1).map (fun c => (2524577793-1+2*2^9*c.k,99512212469338+c.lower,99512592538120+c.upper)) = pointBounds19231 := by
 decide +kernel
def cuts19232 : List PrefixCut := [⟨16,86291490,86291541⟩,
⟨94,497673238,497673541⟩,
⟨128,679502075,679502484⟩]
theorem checked19232 : checkPrefixCuts (2^48) 2524708865 9 Manual.Count131072.C019232.packed 128 cuts19232 = true := by
 decide +kernel
def pointBounds19232 : List (Nat × Nat × Nat) := [(2524725248,99512970716951,99513350786188),(2524805120,99513382098699,99513762168188)]
theorem point_links_checked19232 : (cuts19232.take 2).map (fun c => (2524708865-1+2*2^9*c.k,99512884425461+c.lower,99513264494647+c.upper)) = pointBounds19232 := by
 decide +kernel
def cuts19233 : List PrefixCut := [⟨44,229874383,229874518⟩,
⟨122,633872593,633872969⟩,
⟨128,667538532,667538929⟩]
theorem checked19233 : checkPrefixCuts (2^48) 2524839937 9 Manual.Count131072.C019233.packed 128 cuts19233 = true := by
 decide +kernel
def pointBounds19233 : List (Nat × Nat × Nat) := [(2524884992,99513793801919,99514173871649),(2524964864,99514197800129,99514577870100)]
theorem point_links_checked19233 : (cuts19233.take 2).map (fun c => (2524839937-1+2*2^9*c.k,99513563927536+c.lower,99513943997131+c.upper)) = pointBounds19233 := by
 decide +kernel
def cuts19234 : List PrefixCut := [⟨72,380575143,380575365⟩,
⟨128,669844874,669845268⟩]
theorem checked19234 : checkPrefixCuts (2^48) 2524971009 9 Manual.Count131072.C019234.packed 128 cuts19234 = true := by
 decide +kernel
def pointBounds19234 : List (Nat × Nat × Nat) := [(2525044736,99514612041211,99514992111425)]
theorem point_links_checked19234 : (cuts19234.take 1).map (fun c => (2524971009-1+2*2^9*c.k,99514231466068+c.lower,99514611536060+c.upper)) = pointBounds19234 := by
 decide +kernel
def cuts19235 : List PrefixCut := [⟨22,114479904,114479972⟩,
⟨100,521226420,521226730⟩,
⟨128,667580683,667581081⟩]
theorem checked19235 : checkPrefixCuts (2^48) 2525102081 9 Manual.Count131072.C019235.packed 128 cuts19235 = true := by
 decide +kernel
def pointBounds19235 : List (Nat × Nat × Nat) := [(2525124608,99515015790846,99515395861300),(2525204480,99515422537362,99515802608058)]
theorem point_links_checked19235 : (cuts19235.take 2).map (fun c => (2525102081-1+2*2^9*c.k,99514901310942+c.lower,99515281381328+c.upper)) = pointBounds19235 := by
 decide +kernel
def cuts19236 : List PrefixCut := [⟨50,266175488,266175648⟩,
⟨128,680029832,680030242⟩]
theorem checked19236 : checkPrefixCuts (2^48) 2525233153 9 Manual.Count131072.C019236.packed 128 cuts19236 = true := by
 decide +kernel
def pointBounds19236 : List (Nat × Nat × Nat) := [(2525284352,99515835067113,99516215138057),(2525364224,99516248921457,99516628992651)]
theorem point_links_checked19236 : (cuts19236.take 2).map (fun c => (2525233153-1+2*2^9*c.k,99515568891625+c.lower,99515948962409+c.upper)) = pointBounds19236 := by
 decide +kernel
def cuts19237 : List PrefixCut := [⟨78,404255911,404256153⟩,
⟨128,666731177,666731576⟩]
theorem checked19237 : checkPrefixCuts (2^48) 2525364225 9 Manual.Count131072.C019237.packed 128 cuts19237 = true := by
 decide +kernel
def pointBounds19237 : List (Nat × Nat × Nat) := [(2525444096,99516653177368,99517033248804)]
theorem point_links_checked19237 : (cuts19237.take 1).map (fun c => (2525364225-1+2*2^9*c.k,99516248921457+c.lower,99516628992651+c.upper)) = pointBounds19237 := by
 decide +kernel
def cuts19238 : List PrefixCut := [⟨28,151575701,151575790⟩,
⟨106,564164781,564165115⟩,
⟨128,684751578,684751984⟩]
theorem checked19238 : checkPrefixCuts (2^48) 2525495297 9 Manual.Count131072.C019238.packed 128 cuts19238 = true := by
 decide +kernel
def pointBounds19238 : List (Nat × Nat × Nat) := [(2525523968,99517067228335,99517447300017),(2525603840,99517479817415,99517859889342)]
theorem point_links_checked19238 : (cuts19238.take 2).map (fun c => (2525495297-1+2*2^9*c.k,99516915652634+c.lower,99517295724227+c.upper)) = pointBounds19238 := by
 decide +kernel
def cuts19239 : List PrefixCut := [⟨56,298230286,298230466⟩,
⟨128,677695088,677695493⟩]
theorem checked19239 : checkPrefixCuts (2^48) 2525626369 9 Manual.Count131072.C019239.packed 128 cuts19239 = true := by
 decide +kernel
def pointBounds19239 : List (Nat × Nat × Nat) := [(2525683712,99517898634498,99518278706677)]
theorem point_links_checked19239 : (cuts19239.take 1).map (fun c => (2525626369-1+2*2^9*c.k,99517600404212+c.lower,99517980476211+c.upper)) = pointBounds19239 := by
 decide +kernel
def cuts19240 : List PrefixCut := [⟨6,32206633,32206651⟩,
⟨84,441524850,441525110⟩,
⟨128,673425219,673425612⟩]
theorem checked19240 : checkPrefixCuts (2^48) 2525757441 9 Manual.Count131072.C019240.packed 128 cuts19240 = true := by
 decide +kernel
def pointBounds19240 : List (Nat × Nat × Nat) := [(2525763584,99518310305933,99518690378355),(2525843456,99518719624150,99519099696814)]
theorem point_links_checked19240 : (cuts19240.take 2).map (fun c => (2525757441-1+2*2^9*c.k,99518278099300+c.lower,99518658171704+c.upper)) = pointBounds19240 := by
 decide +kernel
def cuts19241 : List PrefixCut := [⟨34,172613164,172613269⟩,
⟨112,582685487,582685834⟩,
⟨128,668375598,668375997⟩]
theorem checked19241 : checkPrefixCuts (2^48) 2525888513 9 Manual.Count131072.C019241.packed 128 cuts19241 = true := by
 decide +kernel
def pointBounds19241 : List (Nat × Nat × Nat) := [(2525923328,99519124137683,99519504210585),(2526003200,99519534210006,99519914283150)]
theorem point_links_checked19241 : (cuts19241.take 2).map (fun c => (2525888513-1+2*2^9*c.k,99518951524519+c.lower,99519331597316+c.upper)) = pointBounds19241 := by
 decide +kernel
def cuts19242 : List PrefixCut := [⟨62,330052166,330052359⟩,
⟨128,674135434,674135834⟩]
theorem checked19242 : checkPrefixCuts (2^48) 2526019585 9 Manual.Count131072.C019242.packed 128 cuts19242 = true := by
 decide +kernel
def pointBounds19242 : List (Nat × Nat × Nat) := [(2526083072,99519949952283,99520330025672)]
theorem point_links_checked19242 : (cuts19242.take 1).map (fun c => (2526019585-1+2*2^9*c.k,99519619900117+c.lower,99519999973313+c.upper)) = pointBounds19242 := by
 decide +kernel
def cuts19243 : List PrefixCut := [⟨12,63066073,63066110⟩,
⟨90,470202521,470202800⟩,
⟨128,673543118,673543518⟩]
theorem checked19243 : checkPrefixCuts (2^48) 2526150657 9 Manual.Count131072.C019243.packed 128 cuts19243 = true := by
 decide +kernel
def pointBounds19243 : List (Nat × Nat × Nat) := [(2526162944,99520357101624,99520737175257),(2526242816,99520764238072,99521144311947)]
theorem point_links_checked19243 : (cuts19243.take 2).map (fun c => (2526150657-1+2*2^9*c.k,99520294035551+c.lower,99520674109147+c.upper)) = pointBounds19243 := by
 decide +kernel
def cuts19244 : List PrefixCut := [⟨40,214144900,214145024⟩,
⟨118,629054695,629055069⟩,
⟨128,681307436,681307842⟩]
theorem checked19244 : checkPrefixCuts (2^48) 2526281729 9 Manual.Count131072.C019244.packed 128 cuts19244 = true := by
 decide +kernel
def pointBounds19244 : List (Nat × Nat × Nat) := [(2526322688,99521181723569,99521561797689),(2526402560,99521596633364,99521976707734)]
theorem point_links_checked19244 : (cuts19244.take 2).map (fun c => (2526281729-1+2*2^9*c.k,99520967578669+c.lower,99521347652665+c.upper)) = pointBounds19244 := by
 decide +kernel
def cuts19245 : List PrefixCut := [⟨68,356850503,356850716⟩,
⟨128,676258539,676258938⟩]
theorem checked19245 : checkPrefixCuts (2^48) 2526412801 9 Manual.Count131072.C019245.packed 128 cuts19245 = true := by
 decide +kernel
def pointBounds19245 : List (Nat × Nat × Nat) := [(2526482432,99522005736608,99522385811223)]
theorem point_links_checked19245 : (cuts19245.take 1).map (fun c => (2526412801-1+2*2^9*c.k,99521648886105+c.lower,99522028960507+c.upper)) = pointBounds19245 := by
 decide +kernel
def cuts19246 : List PrefixCut := [⟨18,92578954,92579007⟩,
⟨96,503215975,503216271⟩,
⟨128,673995290,673995688⟩]
theorem checked19246 : checkPrefixCuts (2^48) 2526543873 9 Manual.Count131072.C019246.packed 128 cuts19246 = true := by
 decide +kernel
def pointBounds19246 : List (Nat × Nat × Nat) := [(2526562304,99522417723598,99522797798452),(2526642176,99522828360619,99523208435716)]
theorem point_links_checked19246 : (cuts19246.take 2).map (fun c => (2526543873-1+2*2^9*c.k,99522325144644+c.lower,99522705219445+c.upper)) = pointBounds19246 := by
 decide +kernel
def cuts19247 : List PrefixCut := [⟨46,237282580,237282723⟩,
⟨124,655580081,655580472⟩,
⟨128,677859204,677859608⟩]
theorem checked19247 : checkPrefixCuts (2^48) 2526674945 9 Manual.Count131072.C019247.packed 128 cuts19247 = true := by
 decide +kernel
def pointBounds19247 : List (Nat × Nat × Nat) := [(2526722048,99523236422514,99523616497856),(2526801920,99523654720015,99524034795605)]
theorem point_links_checked19247 : (cuts19247.take 2).map (fun c => (2526674945-1+2*2^9*c.k,99522999139934+c.lower,99523379215133+c.upper)) = pointBounds19247 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000288
