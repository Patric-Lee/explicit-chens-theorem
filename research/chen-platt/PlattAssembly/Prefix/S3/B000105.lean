import PlattAssemblyKernel
import PlattCertificates.Count131072.C023360
import PlattCertificates.Count131072.C023361
import PlattCertificates.Count131072.C023362
import PlattCertificates.Count131072.C023363
import PlattCertificates.Count131072.C023364
import PlattCertificates.Count131072.C023365
import PlattCertificates.Count131072.C023366
import PlattCertificates.Count131072.C023367
import PlattCertificates.Count131072.C023368
import PlattCertificates.Count131072.C023369
import PlattCertificates.Count131072.C023370
import PlattCertificates.Count131072.C023371
import PlattCertificates.Count131072.C023372
import PlattCertificates.Count131072.C023373
import PlattCertificates.Count131072.C023374
import PlattCertificates.Count131072.C023375
import PlattCertificates.Count131072.C023376
import PlattCertificates.Count131072.C023377
import PlattCertificates.Count131072.C023378
import PlattCertificates.Count131072.C023379
import PlattCertificates.Count131072.C023380
import PlattCertificates.Count131072.C023381
import PlattCertificates.Count131072.C023382
import PlattCertificates.Count131072.C023383
import PlattCertificates.Count131072.C023384
import PlattCertificates.Count131072.C023385
import PlattCertificates.Count131072.C023386
import PlattCertificates.Count131072.C023387
import PlattCertificates.Count131072.C023388
import PlattCertificates.Count131072.C023389
import PlattCertificates.Count131072.C023390
import PlattCertificates.Count131072.C023391
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000105
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23360 : List PrefixCut := [⟨28,120732232,120732305⟩,
⟨122,531856164,531856471⟩,
⟨128,556001714,556002036⟩]
theorem checked23360 : checkPrefixCuts (2^48) 3065774081 9 Manual.Count131072.C023360.packed 128 cuts23360 = true := by
 decide +kernel
def pointBounds23360 : List (Nat × Nat × Nat) := [(3065802752,102026312198862,102026693723716),(3065899008,102026723322794,102027104847882)]
theorem point_links_checked23360 : (cuts23360.take 2).map (fun c => (3065774081-1+2*2^9*c.k,102026191466630+c.lower,102026572991411+c.upper)) = pointBounds23360 := by
 decide +kernel
def cuts23361 : List PrefixCut := [⟨88,380171709,380171927⟩,
⟨128,552305687,552306000⟩]
theorem checked23361 : checkPrefixCuts (2^48) 3065905153 9 Manual.Count131072.C023361.packed 128 cuts23361 = true := by
 decide +kernel
def pointBounds23361 : List (Nat × Nat × Nat) := [(3065995264,102027127640053,102027509165374)]
theorem point_links_checked23361 : (cuts23361.take 1).map (fun c => (3065905153-1+2*2^9*c.k,102026747468344+c.lower,102027128993447+c.upper)) = pointBounds23361 := by
 decide +kernel
def cuts23362 : List PrefixCut := [⟨54,225560791,225560925⟩,
⟨128,545213186,545213495⟩]
theorem checked23362 : checkPrefixCuts (2^48) 3066036225 9 Manual.Count131072.C023362.packed 128 cuts23362 = true := by
 decide +kernel
def pointBounds23362 : List (Nat × Nat × Nat) := [(3066091520,102027525334822,102027906860372)]
theorem point_links_checked23362 : (cuts23362.take 1).map (fun c => (3066036225-1+2*2^9*c.k,102027299774031+c.lower,102027681299447+c.upper)) = pointBounds23362 := by
 decide +kernel
def cuts23363 : List PrefixCut := [⟨20,86016536,86016585⟩,
⟨114,491489152,491489433⟩,
⟨128,552717436,552717751⟩]
theorem checked23363 : checkPrefixCuts (2^48) 3066167297 9 Manual.Count131072.C023363.packed 128 cuts23363 = true := by
 decide +kernel
def pointBounds23363 : List (Nat × Nat × Nat) := [(3066187776,102027931003753,102028312529527),(3066284032,102028336476369,102028718002375)]
theorem point_links_checked23363 : (cuts23363.take 2).map (fun c => (3066167297-1+2*2^9*c.k,102027844987217+c.lower,102028226512942+c.upper)) = pointBounds23363 := by
 decide +kernel
def cuts23364 : List PrefixCut := [⟨80,348545955,348546153⟩,
⟨128,556824565,556824883⟩]
theorem checked23364 : checkPrefixCuts (2^48) 3066298369 9 Manual.Count131072.C023364.packed 128 cuts23364 = true := by
 decide +kernel
def pointBounds23364 : List (Nat × Nat × Nat) := [(3066380288,102028746250608,102029127776846)]
theorem point_links_checked23364 : (cuts23364.take 1).map (fun c => (3066298369-1+2*2^9*c.k,102028397704653+c.lower,102028779230693+c.upper)) = pointBounds23364 := by
 decide +kernel
def cuts23365 : List PrefixCut := [⟨46,200473058,200473164⟩,
⟨128,557076182,557076488⟩]
theorem checked23365 : checkPrefixCuts (2^48) 3066429441 9 Manual.Count131072.C023365.packed 128 cuts23365 = true := by
 decide +kernel
def pointBounds23365 : List (Nat × Nat × Nat) := [(3066476544,102029155002276,102029536528740)]
theorem point_links_checked23365 : (cuts23365.take 1).map (fun c => (3066429441-1+2*2^9*c.k,102028954529218+c.lower,102029336055576+c.upper)) = pointBounds23365 := by
 decide +kernel
def cuts23366 : List PrefixCut := [⟨12,48831363,48831392⟩,
⟨106,450122596,450122851⟩,
⟨128,544936382,544936691⟩]
theorem checked23366 : checkPrefixCuts (2^48) 3066560513 9 Manual.Count131072.C023366.packed 128 cuts23366 = true := by
 decide +kernel
def pointBounds23366 : List (Nat × Nat × Nat) := [(3066572800,102029560436763,102029941963456),(3066669056,102029961727996,102030343254915)]
theorem point_links_checked23366 : (cuts23366.take 2).map (fun c => (3066560513-1+2*2^9*c.k,102029511605400+c.lower,102029893132064+c.upper)) = pointBounds23366 := by
 decide +kernel
def cuts23367 : List PrefixCut := [⟨72,309218390,309218567⟩,
⟨128,549685873,549686189⟩]
theorem checked23367 : checkPrefixCuts (2^48) 3066691585 9 Manual.Count131072.C023367.packed 128 cuts23367 = true := by
 decide +kernel
def pointBounds23367 : List (Nat × Nat × Nat) := [(3066765312,102030365760172,102030747287322)]
theorem point_links_checked23367 : (cuts23367.take 1).map (fun c => (3066691585-1+2*2^9*c.k,102030056541782+c.lower,102030438068755+c.upper)) = pointBounds23367 := by
 decide +kernel
def cuts23368 : List PrefixCut := [⟨38,163643808,163643902⟩,
⟨128,546909077,546909394⟩]
theorem checked23368 : checkPrefixCuts (2^48) 3066822657 9 Manual.Count131072.C023368.packed 128 cuts23368 = true := by
 decide +kernel
def pointBounds23368 : List (Nat × Nat × Nat) := [(3066861568,102030769871463,102031151398846)]
theorem point_links_checked23368 : (cuts23368.take 1).map (fun c => (3066822657-1+2*2^9*c.k,102030606227655+c.lower,102030987754944+c.upper)) = pointBounds23368 := by
 decide +kernel
def cuts23369 : List PrefixCut := [⟨4,17896445,17896455⟩,
⟨98,427764126,427764369⟩,
⟨128,557531479,557531794⟩]
theorem checked23369 : checkPrefixCuts (2^48) 3066953729 9 Manual.Count131072.C023369.packed 128 cuts23369 = true := by
 decide +kernel
def pointBounds23369 : List (Nat × Nat × Nat) := [(3066957824,102031171033177,102031552560793),(3067054080,102031580900858,102031962428707)]
theorem point_links_checked23369 : (cuts23369.take 2).map (fun c => (3066953729-1+2*2^9*c.k,102031153136732+c.lower,102031534664338+c.upper)) = pointBounds23369 := by
 decide +kernel
def cuts23370 : List PrefixCut := [⟨64,279261580,279261742⟩,
⟨128,552368624,552368942⟩]
theorem checked23370 : checkPrefixCuts (2^48) 3067084801 9 Manual.Count131072.C023370.packed 128 cuts23370 = true := by
 decide +kernel
def pointBounds23370 : List (Nat × Nat × Nat) := [(3067150336,102031989929791,102032371457874)]
theorem point_links_checked23370 : (cuts23370.take 1).map (fun c => (3067084801-1+2*2^9*c.k,102031710668211+c.lower,102032092196132+c.upper)) = pointBounds23370 := by
 decide +kernel
def cuts23371 : List PrefixCut := [⟨30,125814465,125814537⟩,
⟨124,527017632,527017931⟩,
⟨128,544452982,544453291⟩]
theorem checked23371 : checkPrefixCuts (2^48) 3067215873 9 Manual.Count131072.C023371.packed 128 cuts23371 = true := by
 decide +kernel
def pointBounds23371 : List (Nat × Nat × Nat) := [(3067246592,102032388851300,102032770379611),(3067342848,102032790054467,102033171583005)]
theorem point_links_checked23371 : (cuts23371.take 2).map (fun c => (3067215873-1+2*2^9*c.k,102032263036835+c.lower,102032644565074+c.upper)) = pointBounds23371 := by
 decide +kernel
def cuts23372 : List PrefixCut := [⟨90,388710453,388710669⟩,
⟨128,551954348,551954658⟩]
theorem checked23372 : checkPrefixCuts (2^48) 3067346945 9 Manual.Count131072.C023372.packed 128 cuts23372 = true := by
 decide +kernel
def pointBounds23372 : List (Nat × Nat × Nat) := [(3067439104,102033196200270,102033577729034)]
theorem point_links_checked23372 : (cuts23372.take 1).map (fun c => (3067346945-1+2*2^9*c.k,102032807489817+c.lower,102033189018365+c.upper)) = pointBounds23372 := by
 decide +kernel
def cuts23373 : List PrefixCut := [⟨56,243715000,243715133⟩,
⟨128,555325869,555326173⟩]
theorem checked23373 : checkPrefixCuts (2^48) 3067478017 9 Manual.Count131072.C023373.packed 128 cuts23373 = true := by
 decide +kernel
def pointBounds23373 : List (Nat × Nat × Nat) := [(3067535360,102033603159165,102033984688156)]
theorem point_links_checked23373 : (cuts23373.take 1).map (fun c => (3067478017-1+2*2^9*c.k,102033359444165+c.lower,102033740973023+c.upper)) = pointBounds23373 := by
 decide +kernel
def cuts23374 : List PrefixCut := [⟨22,93958915,93958967⟩,
⟨116,494102396,494102674⟩,
⟨128,543098689,543098995⟩]
theorem checked23374 : checkPrefixCuts (2^48) 3067609089 9 Manual.Count131072.C023374.packed 128 cuts23374 = true := by
 decide +kernel
def pointBounds23374 : List (Nat × Nat × Nat) := [(3067631616,102034008728949,102034390258163),(3067727872,102034408872430,102034790401870)]
theorem point_links_checked23374 : (cuts23374.take 2).map (fun c => (3067609089-1+2*2^9*c.k,102033914770034+c.lower,102034296299196+c.upper)) = pointBounds23374 := by
 decide +kernel
def cuts23375 : List PrefixCut := [⟨82,352786130,352786327⟩,
⟨128,554727790,554728103⟩]
theorem checked23375 : checkPrefixCuts (2^48) 3067740161 9 Manual.Count131072.C023375.packed 128 cuts23375 = true := by
 decide +kernel
def pointBounds23375 : List (Nat × Nat × Nat) := [(3067824128,102034810654853,102035192184518)]
theorem point_links_checked23375 : (cuts23375.take 1).map (fun c => (3067740161-1+2*2^9*c.k,102034457868723+c.lower,102034839398191+c.upper)) = pointBounds23375 := by
 decide +kernel
def cuts23376 : List PrefixCut := [⟨48,205057937,205058049⟩,
⟨128,552869093,552869396⟩]
theorem checked23376 : checkPrefixCuts (2^48) 3067871233 9 Manual.Count131072.C023376.packed 128 cuts23376 = true := by
 decide +kernel
def pointBounds23376 : List (Nat × Nat × Nat) := [(3067920384,102035217654450,102035599184343)]
theorem point_links_checked23376 : (cuts23376.take 1).map (fun c => (3067871233-1+2*2^9*c.k,102035012596513+c.lower,102035394126294+c.upper)) = pointBounds23376 := by
 decide +kernel
def cuts23377 : List PrefixCut := [⟨14,60368288,60368320⟩,
⟨108,462755125,462755380⟩,
⟨128,550093249,550093550⟩]
theorem checked23377 : checkPrefixCuts (2^48) 3068002305 9 Manual.Count131072.C023377.packed 128 cuts23377 = true := by
 decide +kernel
def pointBounds23377 : List (Nat × Nat × Nat) := [(3068016640,102035625833894,102036007364010),(3068112896,102036028220731,102036409751070)]
theorem point_links_checked23377 : (cuts23377.take 2).map (fun c => (3068002305-1+2*2^9*c.k,102035565465606+c.lower,102035946995690+c.upper)) = pointBounds23377 := by
 decide +kernel
def cuts23378 : List PrefixCut := [⟨74,317146195,317146372⟩,
⟨128,547776364,547776673⟩]
theorem checked23378 : checkPrefixCuts (2^48) 3068133377 9 Manual.Count131072.C023378.packed 128 cuts23378 = true := by
 decide +kernel
def pointBounds23378 : List (Nat × Nat × Nat) := [(3068209152,102036432705050,102036814235612)]
theorem point_links_checked23378 : (cuts23378.take 1).map (fun c => (3068133377-1+2*2^9*c.k,102036115558855+c.lower,102036497089240+c.upper)) = pointBounds23378 := by
 decide +kernel
def cuts23379 : List PrefixCut := [⟨40,174483567,174483666⟩,
⟨128,551697588,551697904⟩]
theorem checked23379 : checkPrefixCuts (2^48) 3068264449 9 Manual.Count131072.C023379.packed 128 cuts23379 = true := by
 decide +kernel
def pointBounds23379 : List (Nat × Nat × Nat) := [(3068305408,102036837818786,102037219349579)]
theorem point_links_checked23379 : (cuts23379.take 1).map (fun c => (3068264449-1+2*2^9*c.k,102036663335219+c.lower,102037044865913+c.upper)) = pointBounds23379 := by
 decide +kernel
def cuts23380 : List PrefixCut := [⟨6,25593642,25593656⟩,
⟨100,430315012,430315251⟩,
⟨128,546720486,546720792⟩]
theorem checked23380 : checkPrefixCuts (2^48) 3068395521 9 Manual.Count131072.C023380.packed 128 cuts23380 = true := by
 decide +kernel
def pointBounds23380 : List (Nat × Nat × Nat) := [(3068401664,102037240626449,102037622157473),(3068497920,102037645347819,102038026879068)]
theorem point_links_checked23380 : (cuts23380.take 2).map (fun c => (3068395521-1+2*2^9*c.k,102037215032807+c.lower,102037596563817+c.upper)) = pointBounds23380 := by
 decide +kernel
def cuts23381 : List PrefixCut := [⟨66,285643008,285643169⟩,
⟨128,553668416,553668727⟩]
theorem checked23381 : checkPrefixCuts (2^48) 3068526593 9 Manual.Count131072.C023381.packed 128 cuts23381 = true := by
 decide +kernel
def pointBounds23381 : List (Nat × Nat × Nat) := [(3068594176,102038047396301,102038428927778)]
theorem point_links_checked23381 : (cuts23381.take 1).map (fun c => (3068526593-1+2*2^9*c.k,102037761753293+c.lower,102038143284609+c.upper)) = pointBounds23381 := by
 decide +kernel
def cuts23382 : List PrefixCut := [⟨32,135753355,135753437⟩,
⟨126,538235270,538235584⟩,
⟨128,547957787,547958106⟩]
theorem checked23382 : checkPrefixCuts (2^48) 3068657665 9 Manual.Count131072.C023382.packed 128 cuts23382 = true := by
 decide +kernel
def pointBounds23382 : List (Nat × Nat × Nat) := [(3068690432,102038451175064,102038832706773),(3068786688,102038853656979,102039235188920)]
theorem point_links_checked23382 : (cuts23382.take 2).map (fun c => (3068657665-1+2*2^9*c.k,102038315421709+c.lower,102038696953336+c.upper)) = pointBounds23382 := by
 decide +kernel
def cuts23383 : List PrefixCut := [⟨92,391187507,391187730⟩,
⟨128,548576386,548576700⟩]
theorem checked23383 : checkPrefixCuts (2^48) 3068788737 9 Manual.Count131072.C023383.packed 128 cuts23383 = true := by
 decide +kernel
def pointBounds23383 : List (Nat × Nat × Nat) := [(3068882944,102039254567003,102039636099172)]
theorem point_links_checked23383 : (cuts23383.take 1).map (fun c => (3068788737-1+2*2^9*c.k,102038863379496+c.lower,102039244911442+c.upper)) = pointBounds23383 := by
 decide +kernel
def cuts23384 : List PrefixCut := [⟨58,251488054,251488196⟩,
⟨128,548736550,548736861⟩]
theorem checked23384 : checkPrefixCuts (2^48) 3068919809 9 Manual.Count131072.C023384.packed 128 cuts23384 = true := by
 decide +kernel
def pointBounds23384 : List (Nat × Nat × Nat) := [(3068979200,102039663443936,102040044976338)]
theorem point_links_checked23384 : (cuts23384.take 1).map (fun c => (3068919809-1+2*2^9*c.k,102039411955882+c.lower,102039793488142+c.upper)) = pointBounds23384 := by
 decide +kernel
def cuts23385 : List PrefixCut := [⟨24,102627539,102627594⟩,
⟨118,506251286,506251569⟩,
⟨128,548071151,548071457⟩]
theorem checked23385 : checkPrefixCuts (2^48) 3069050881 9 Manual.Count131072.C023385.packed 128 cuts23385 = true := by
 decide +kernel
def pointBounds23385 : List (Nat × Nat × Nat) := [(3069075456,102040063319971,102040444852597),(3069171712,102040466943718,102040848476572)]
theorem point_links_checked23385 : (cuts23385.take 2).map (fun c => (3069050881-1+2*2^9*c.k,102039960692432+c.lower,102040342225003+c.upper)) = pointBounds23385 := by
 decide +kernel
def cuts23386 : List PrefixCut := [⟨84,368119091,368119298⟩,
⟨128,557126855,557127174⟩]
theorem checked23386 : checkPrefixCuts (2^48) 3069181953 9 Manual.Count131072.C023386.packed 128 cuts23386 = true := by
 decide +kernel
def pointBounds23386 : List (Nat × Nat × Nat) := [(3069267968,102040876882674,102041258415758)]
theorem point_links_checked23386 : (cuts23386.take 1).map (fun c => (3069181953-1+2*2^9*c.k,102040508763583+c.lower,102040890296460+c.upper)) = pointBounds23386 := by
 decide +kernel
def cuts23387 : List PrefixCut := [⟨50,213123327,213123451⟩,
⟨128,552609468,552609784⟩]
theorem checked23387 : checkPrefixCuts (2^48) 3069313025 9 Manual.Count131072.C023387.packed 128 cuts23387 = true := by
 decide +kernel
def pointBounds23387 : List (Nat × Nat × Nat) := [(3069364224,102041279013765,102041660547085)]
theorem point_links_checked23387 : (cuts23387.take 1).map (fun c => (3069313025-1+2*2^9*c.k,102041065890438+c.lower,102041447423634+c.upper)) = pointBounds23387 := by
 decide +kernel
def cuts23388 : List PrefixCut := [⟨16,64925014,64925050⟩,
⟨110,468773227,468773497⟩,
⟨128,549101202,549101518⟩]
theorem checked23388 : checkPrefixCuts (2^48) 3069444097 9 Manual.Count131072.C023388.packed 128 cuts23388 = true := by
 decide +kernel
def pointBounds23388 : List (Nat × Nat × Nat) := [(3069460480,102041683424920,102042064958468),(3069556736,102042087273133,102042468806915)]
theorem point_links_checked23388 : (cuts23388.take 2).map (fun c => (3069444097-1+2*2^9*c.k,102041618499906+c.lower,102042000033418+c.upper)) = pointBounds23388 := by
 decide +kernel
def cuts23389 : List PrefixCut := [⟨76,328000744,328000929⟩,
⟨128,552378895,552379203⟩]
theorem checked23389 : checkPrefixCuts (2^48) 3069575169 9 Manual.Count131072.C023389.packed 128 cuts23389 = true := by
 decide +kernel
def pointBounds23389 : List (Nat × Nat × Nat) := [(3069652992,102042495601852,102042877135865)]
theorem point_links_checked23389 : (cuts23389.take 1).map (fun c => (3069575169-1+2*2^9*c.k,102042167601108+c.lower,102042549134936+c.upper)) = pointBounds23389 := by
 decide +kernel
def cuts23390 : List PrefixCut := [⟨42,182837378,182837481⟩,
⟨128,554097503,554097811⟩]
theorem checked23390 : checkPrefixCuts (2^48) 3069706241 9 Manual.Count131072.C023390.packed 128 cuts23390 = true := by
 decide +kernel
def pointBounds23390 : List (Nat × Nat × Nat) := [(3069749248,102042902817381,102043284351620)]
theorem point_links_checked23390 : (cuts23390.take 1).map (fun c => (3069706241-1+2*2^9*c.k,102042719980003+c.lower,102043101514139+c.upper)) = pointBounds23390 := by
 decide +kernel
def cuts23391 : List PrefixCut := [⟨8,35942624,35942644⟩,
⟨102,437264562,437264816⟩,
⟨128,550039537,550039853⟩]
theorem checked23391 : checkPrefixCuts (2^48) 3069837313 9 Manual.Count131072.C023391.packed 128 cuts23391 = true := by
 decide +kernel
def pointBounds23391 : List (Nat × Nat × Nat) := [(3069845504,102043310020130,102043691554594),(3069941760,102043711342068,102044092876766)]
theorem point_links_checked23391 : (cuts23391.take 2).map (fun c => (3069837313-1+2*2^9*c.k,102043274077506+c.lower,102043655611950+c.upper)) = pointBounds23391 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000105
