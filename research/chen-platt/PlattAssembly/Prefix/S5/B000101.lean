import PlattAssemblyKernel
import PlattCertificates.Count131072.C043232
import PlattCertificates.Count131072.C043233
import PlattCertificates.Count131072.C043234
import PlattCertificates.Count131072.C043235
import PlattCertificates.Count131072.C043236
import PlattCertificates.Count131072.C043237
import PlattCertificates.Count131072.C043238
import PlattCertificates.Count131072.C043239
import PlattCertificates.Count131072.C043240
import PlattCertificates.Count131072.C043241
import PlattCertificates.Count131072.C043242
import PlattCertificates.Count131072.C043243
import PlattCertificates.Count131072.C043244
import PlattCertificates.Count131072.C043245
import PlattCertificates.Count131072.C043246
import PlattCertificates.Count131072.C043247
import PlattCertificates.Count131072.C043248
import PlattCertificates.Count131072.C043249
import PlattCertificates.Count131072.C043250
import PlattCertificates.Count131072.C043251
import PlattCertificates.Count131072.C043252
import PlattCertificates.Count131072.C043253
import PlattCertificates.Count131072.C043254
import PlattCertificates.Count131072.C043255
import PlattCertificates.Count131072.C043256
import PlattCertificates.Count131072.C043257
import PlattCertificates.Count131072.C043258
import PlattCertificates.Count131072.C043259
import PlattCertificates.Count131072.C043260
import PlattCertificates.Count131072.C043261
import PlattCertificates.Count131072.C043262
import PlattCertificates.Count131072.C043263
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000101
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43232 : List PrefixCut := [⟨64,291377648,291377822⟩]
theorem checked43232 : checkPrefixCuts (2^48) 5670436865 10 Manual.Count131072.C043232.packed 64 cuts43232 = true := by
 decide +kernel
def cuts43233 : List PrefixCut := [⟨13,58473269,58473303⟩,
⟨64,290824873,290825040⟩]
theorem checked43233 : checkPrefixCuts (2^48) 5670567937 10 Manual.Count131072.C043233.packed 64 cuts43233 = true := by
 decide +kernel
def pointBounds43233 : List (Nat × Nat × Nat) := [(5670594560,109841434295518,109841820374417)]
theorem point_links_checked43233 : (cuts43233.take 1).map (fun c => (5670567937-1+2*2^10*c.k,109841375822249+c.lower,109841761901114+c.upper)) = pointBounds43233 := by
 decide +kernel
def cuts43234 : List PrefixCut := [⟨36,162261372,162261469⟩,
⟨64,286648739,286648908⟩]
theorem checked43234 : checkPrefixCuts (2^48) 5670699009 10 Manual.Count131072.C043234.packed 64 cuts43234 = true := by
 decide +kernel
def pointBounds43234 : List (Nat × Nat × Nat) := [(5670772736,109841828908494,109842214987623)]
theorem point_links_checked43234 : (cuts43234.take 1).map (fun c => (5670699009-1+2*2^10*c.k,109841666647122+c.lower,109842052726154+c.upper)) = pointBounds43234 := by
 decide +kernel
def cuts43235 : List PrefixCut := [⟨59,265696390,265696550⟩,
⟨64,289570569,289570743⟩]
theorem checked43235 : checkPrefixCuts (2^48) 5670830081 10 Manual.Count131072.C043235.packed 64 cuts43235 = true := by
 decide +kernel
def pointBounds43235 : List (Nat × Nat × Nat) := [(5670950912,109842218992251,109842605071612)]
theorem point_links_checked43235 : (cuts43235.take 1).map (fun c => (5670830081-1+2*2^10*c.k,109841953295861+c.lower,109842339375062+c.upper)) = pointBounds43235 := by
 decide +kernel
def cuts43236 : List PrefixCut := [⟨64,287231096,287231265⟩]
theorem checked43236 : checkPrefixCuts (2^48) 5670961153 10 Manual.Count131072.C043236.packed 64 cuts43236 = true := by
 decide +kernel
def cuts43237 : List PrefixCut := [⟨18,80008583,80008629⟩,
⟨64,290946899,290947066⟩]
theorem checked43237 : checkPrefixCuts (2^48) 5671092225 10 Manual.Count131072.C043237.packed 64 cuts43237 = true := by
 decide +kernel
def pointBounds43237 : List (Nat × Nat × Nat) := [(5671129088,109842610106109,109842996185699)]
theorem point_links_checked43237 : (cuts43237.take 1).map (fun c => (5671092225-1+2*2^10*c.k,109842530097526+c.lower,109842916177070+c.upper)) = pointBounds43237 := by
 decide +kernel
def cuts43238 : List PrefixCut := [⟨41,184878319,184878426⟩,
⟨64,290692019,290692186⟩]
theorem checked43238 : checkPrefixCuts (2^48) 5671223297 10 Manual.Count131072.C043238.packed 64 cuts43238 = true := by
 decide +kernel
def pointBounds43238 : List (Nat × Nat × Nat) := [(5671307264,109843005922744,109843392002562)]
theorem point_links_checked43238 : (cuts43238.take 1).map (fun c => (5671223297-1+2*2^10*c.k,109842821044425+c.lower,109843207124136+c.upper)) = pointBounds43238 := by
 decide +kernel
def cuts43239 : List PrefixCut := [⟨64,292074986,292075153⟩]
theorem checked43239 : checkPrefixCuts (2^48) 5671354369 10 Manual.Count131072.C043239.packed 64 cuts43239 = true := by
 decide +kernel
def pointBounds43239 : List (Nat × Nat × Nat) := [(5671485440,109843403811430,109843789891475)]
theorem point_links_checked43239 : (cuts43239.take 1).map (fun c => (5671354369-1+2*2^10*c.k,109843111736444+c.lower,109843497816322+c.upper)) = pointBounds43239 := by
 decide +kernel
def cuts43240 : List PrefixCut := [⟨64,289140067,289140234⟩]
theorem checked43240 : checkPrefixCuts (2^48) 5671485441 10 Manual.Count131072.C043240.packed 64 cuts43240 = true := by
 decide +kernel
def cuts43241 : List PrefixCut := [⟨23,102730959,102731018⟩,
⟨64,289282262,289282435⟩]
theorem checked43241 : checkPrefixCuts (2^48) 5671616513 10 Manual.Count131072.C043241.packed 64 cuts43241 = true := by
 decide +kernel
def pointBounds43241 : List (Nat × Nat × Nat) := [(5671663616,109843795682456,109844181762727)]
theorem point_links_checked43241 : (cuts43241.take 1).map (fun c => (5671616513-1+2*2^10*c.k,109843692951497+c.lower,109844079031709+c.upper)) = pointBounds43241 := by
 decide +kernel
def cuts43242 : List PrefixCut := [⟨46,206697005,206697126⟩,
⟨64,287389783,287389953⟩]
theorem checked43242 : checkPrefixCuts (2^48) 5671747585 10 Manual.Count131072.C043242.packed 64 cuts43242 = true := by
 decide +kernel
def pointBounds43242 : List (Nat × Nat × Nat) := [(5671841792,109844188930764,109844575011270)]
theorem point_links_checked43242 : (cuts43242.take 1).map (fun c => (5671747585-1+2*2^10*c.k,109843982233759+c.lower,109844368314144+c.upper)) = pointBounds43242 := by
 decide +kernel
def cuts43243 : List PrefixCut := [⟨64,290360699,290360871⟩]
theorem checked43243 : checkPrefixCuts (2^48) 5671878657 10 Manual.Count131072.C043243.packed 64 cuts43243 = true := by
 decide +kernel
def cuts43244 : List PrefixCut := [⟨5,23075719,23075732⟩,
⟨64,292239692,292239860⟩]
theorem checked43244 : checkPrefixCuts (2^48) 5672009729 10 Manual.Count131072.C043244.packed 64 cuts43244 = true := by
 decide +kernel
def pointBounds43244 : List (Nat × Nat × Nat) := [(5672019968,109844583059960,109844969140700)]
theorem point_links_checked43244 : (cuts43244.take 1).map (fun c => (5672009729-1+2*2^10*c.k,109844559984241+c.lower,109844946064968+c.upper)) = pointBounds43244 := by
 decide +kernel
def cuts43245 : List PrefixCut := [⟨28,124853609,124853683⟩,
⟨64,286278144,286278318⟩]
theorem checked43245 : checkPrefixCuts (2^48) 5672140801 10 Manual.Count131072.C043245.packed 64 cuts43245 = true := by
 decide +kernel
def pointBounds43245 : List (Nat × Nat × Nat) := [(5672198144,109844977077542,109845363158511)]
theorem point_links_checked43245 : (cuts43245.take 1).map (fun c => (5672140801-1+2*2^10*c.k,109844852223933+c.lower,109845238304828+c.upper)) = pointBounds43245 := by
 decide +kernel
def cuts43246 : List PrefixCut := [⟨51,231141609,231141744⟩,
⟨64,288504553,288504722⟩]
theorem checked43246 : checkPrefixCuts (2^48) 5672271873 10 Manual.Count131072.C043246.packed 64 cuts43246 = true := by
 decide +kernel
def pointBounds43246 : List (Nat × Nat × Nat) := [(5672376320,109845369643686,109845755724890)]
theorem point_links_checked43246 : (cuts43246.take 1).map (fun c => (5672271873-1+2*2^10*c.k,109845138502077+c.lower,109845524583146+c.upper)) = pointBounds43246 := by
 decide +kernel
def cuts43247 : List PrefixCut := [⟨64,289391060,289391227⟩]
theorem checked43247 : checkPrefixCuts (2^48) 5672402945 10 Manual.Count131072.C043247.packed 64 cuts43247 = true := by
 decide +kernel
def cuts43248 : List PrefixCut := [⟨10,46494478,46494505⟩,
⟨64,293254736,293254904⟩]
theorem checked43248 : checkPrefixCuts (2^48) 5672534017 10 Manual.Count131072.C043248.packed 64 cuts43248 = true := by
 decide +kernel
def pointBounds43248 : List (Nat × Nat × Nat) := [(5672554496,109845762892168,109846148973600)]
theorem point_links_checked43248 : (cuts43248.take 1).map (fun c => (5672534017-1+2*2^10*c.k,109845716397690+c.lower,109846102479095+c.upper)) = pointBounds43248 := by
 decide +kernel
def cuts43249 : List PrefixCut := [⟨33,149850040,149850129⟩,
⟨64,289675390,289675559⟩]
theorem checked43249 : checkPrefixCuts (2^48) 5672665089 10 Manual.Count131072.C043249.packed 64 cuts43249 = true := by
 decide +kernel
def pointBounds43249 : List (Nat × Nat × Nat) := [(5672732672,109846159502466,109846545584128)]
theorem point_links_checked43249 : (cuts43249.take 1).map (fun c => (5672665089-1+2*2^10*c.k,109846009652426+c.lower,109846395733999+c.upper)) = pointBounds43249 := by
 decide +kernel
def cuts43250 : List PrefixCut := [⟨56,254043459,254043604⟩,
⟨64,289023653,289023819⟩]
theorem checked43250 : checkPrefixCuts (2^48) 5672796161 10 Manual.Count131072.C043250.packed 64 cuts43250 = true := by
 decide +kernel
def pointBounds43250 : List (Nat × Nat × Nat) := [(5672910848,109846553371275,109846939453162)]
theorem point_links_checked43250 : (cuts43250.take 1).map (fun c => (5672796161-1+2*2^10*c.k,109846299327816+c.lower,109846685409558+c.upper)) = pointBounds43250 := by
 decide +kernel
def cuts43251 : List PrefixCut := [⟨64,289513134,289513300⟩]
theorem checked43251 : checkPrefixCuts (2^48) 5672927233 10 Manual.Count131072.C043251.packed 64 cuts43251 = true := by
 decide +kernel
def cuts43252 : List PrefixCut := [⟨15,65641889,65641931⟩,
⟨64,287124889,287125066⟩]
theorem checked43252 : checkPrefixCuts (2^48) 5673058305 10 Manual.Count131072.C043252.packed 64 cuts43252 = true := by
 decide +kernel
def pointBounds43252 : List (Nat × Nat × Nat) := [(5673089024,109846943506492,109847329588608)]
theorem point_links_checked43252 : (cuts43252.take 1).map (fun c => (5673058305-1+2*2^10*c.k,109846877864603+c.lower,109847263946677+c.upper)) = pointBounds43252 := by
 decide +kernel
def cuts43253 : List PrefixCut := [⟨38,171716088,171716189⟩,
⟨64,289400531,289400703⟩]
theorem checked43253 : checkPrefixCuts (2^48) 5673189377 10 Manual.Count131072.C043253.packed 64 cuts43253 = true := by
 decide +kernel
def pointBounds43253 : List (Nat × Nat × Nat) := [(5673267200,109847336705580,109847722787932)]
theorem point_links_checked43253 : (cuts43253.take 1).map (fun c => (5673189377-1+2*2^10*c.k,109847164989492+c.lower,109847551071743+c.upper)) = pointBounds43253 := by
 decide +kernel
def cuts43254 : List PrefixCut := [⟨61,279223293,279223460⟩,
⟨64,292717938,292718112⟩]
theorem checked43254 : checkPrefixCuts (2^48) 5673320449 10 Manual.Count131072.C043254.packed 64 cuts43254 = true := by
 decide +kernel
def pointBounds43254 : List (Nat × Nat × Nat) := [(5673445376,109847733613316,109848119695906)]
theorem point_links_checked43254 : (cuts43254.take 1).map (fun c => (5673320449-1+2*2^10*c.k,109847454390023+c.lower,109847840472446+c.upper)) = pointBounds43254 := by
 decide +kernel
def cuts43255 : List PrefixCut := [⟨64,294249153,294249328⟩]
theorem checked43255 : checkPrefixCuts (2^48) 5673451521 10 Manual.Count131072.C043255.packed 64 cuts43255 = true := by
 decide +kernel
def cuts43256 : List PrefixCut := [⟨20,92078600,92078655⟩,
⟨64,291811450,291811619⟩]
theorem checked43256 : checkPrefixCuts (2^48) 5673582593 10 Manual.Count131072.C043256.packed 64 cuts43256 = true := by
 decide +kernel
def pointBounds43256 : List (Nat × Nat × Nat) := [(5673623552,109848133435714,109848519518541)]
theorem point_links_checked43256 : (cuts43256.take 1).map (fun c => (5673582593-1+2*2^10*c.k,109848041357114+c.lower,109848427439886+c.upper)) = pointBounds43256 := by
 decide +kernel
def cuts43257 : List PrefixCut := [⟨43,191246407,191246519⟩,
⟨64,285851513,285851682⟩]
theorem checked43257 : checkPrefixCuts (2^48) 5673713665 10 Manual.Count131072.C043257.packed 64 cuts43257 = true := by
 decide +kernel
def pointBounds43257 : List (Nat × Nat × Nat) := [(5673801728,109848524414971,109848910498024)]
theorem point_links_checked43257 : (cuts43257.take 1).map (fun c => (5673713665-1+2*2^10*c.k,109848333168564+c.lower,109848719251505+c.upper)) = pointBounds43257 := by
 decide +kernel
def cuts43258 : List PrefixCut := [⟨64,290160830,290160997⟩]
theorem checked43258 : checkPrefixCuts (2^48) 5673844737 10 Manual.Count131072.C043258.packed 64 cuts43258 = true := by
 decide +kernel
def cuts43259 : List PrefixCut := [⟨2,9822391,9822397⟩,
⟨64,289707667,289707839⟩]
theorem checked43259 : checkPrefixCuts (2^48) 5673975809 10 Manual.Count131072.C043259.packed 64 cuts43259 = true := by
 decide +kernel
def pointBounds43259 : List (Nat × Nat × Nat) := [(5673979904,109848919003298,109849305086581)]
theorem point_links_checked43259 : (cuts43259.take 1).map (fun c => (5673975809-1+2*2^10*c.k,109848909180907+c.lower,109849295264184+c.upper)) = pointBounds43259 := by
 decide +kernel
def cuts43260 : List PrefixCut := [⟨25,115385148,115385212⟩,
⟨64,291734867,291735033⟩]
theorem checked43260 : checkPrefixCuts (2^48) 5674106881 10 Manual.Count131072.C043260.packed 64 cuts43260 = true := by
 decide +kernel
def pointBounds43260 : List (Nat × Nat × Nat) := [(5674158080,109849314273722,109849700357235)]
theorem point_links_checked43260 : (cuts43260.take 1).map (fun c => (5674106881-1+2*2^10*c.k,109849198888574+c.lower,109849584972023+c.upper)) = pointBounds43260 := by
 decide +kernel
def cuts43261 : List PrefixCut := [⟨48,215138323,215138449⟩,
⟨64,289545465,289545633⟩]
theorem checked43261 : checkPrefixCuts (2^48) 5674237953 10 Manual.Count131072.C043261.packed 64 cuts43261 = true := by
 decide +kernel
def pointBounds43261 : List (Nat × Nat × Nat) := [(5674336256,109849705761764,109850091845505)]
theorem point_links_checked43261 : (cuts43261.take 1).map (fun c => (5674237953-1+2*2^10*c.k,109849490623441+c.lower,109849876707056+c.upper)) = pointBounds43261 := by
 decide +kernel
def cuts43262 : List PrefixCut := [⟨64,287604187,287604355⟩]
theorem checked43262 : checkPrefixCuts (2^48) 5674369025 10 Manual.Count131072.C043262.packed 64 cuts43262 = true := by
 decide +kernel
def cuts43263 : List PrefixCut := [⟨7,32043800,32043819⟩,
⟨64,287101580,287101748⟩]
theorem checked43263 : checkPrefixCuts (2^48) 5674500097 10 Manual.Count131072.C043263.packed 64 cuts43263 = true := by
 decide +kernel
def pointBounds43263 : List (Nat × Nat × Nat) := [(5674514432,109850099816893,109850485900863)]
theorem point_links_checked43263 : (cuts43263.take 1).map (fun c => (5674500097-1+2*2^10*c.k,109850067773093+c.lower,109850453857044+c.upper)) = pointBounds43263 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000101
