import PlattAssemblyKernel
import PlattCertificates.Count131072.C046272
import PlattCertificates.Count131072.C046273
import PlattCertificates.Count131072.C046274
import PlattCertificates.Count131072.C046275
import PlattCertificates.Count131072.C046276
import PlattCertificates.Count131072.C046277
import PlattCertificates.Count131072.C046278
import PlattCertificates.Count131072.C046279
import PlattCertificates.Count131072.C046280
import PlattCertificates.Count131072.C046281
import PlattCertificates.Count131072.C046282
import PlattCertificates.Count131072.C046283
import PlattCertificates.Count131072.C046284
import PlattCertificates.Count131072.C046285
import PlattCertificates.Count131072.C046286
import PlattCertificates.Count131072.C046287
import PlattCertificates.Count131072.C046288
import PlattCertificates.Count131072.C046289
import PlattCertificates.Count131072.C046290
import PlattCertificates.Count131072.C046291
import PlattCertificates.Count131072.C046292
import PlattCertificates.Count131072.C046293
import PlattCertificates.Count131072.C046294
import PlattCertificates.Count131072.C046295
import PlattCertificates.Count131072.C046296
import PlattCertificates.Count131072.C046297
import PlattCertificates.Count131072.C046298
import PlattCertificates.Count131072.C046299
import PlattCertificates.Count131072.C046300
import PlattCertificates.Count131072.C046301
import PlattCertificates.Count131072.C046302
import PlattCertificates.Count131072.C046303
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000196
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46272 : List PrefixCut := [⟨64,271041316,271041474⟩]
theorem checked46272 : checkPrefixCuts (2^48) 6068895745 10 Manual.Count131072.C046272.packed 64 cuts46272 = true := by
 decide +kernel
def cuts46273 : List PrefixCut := [⟨2,8440960,8440965⟩,
⟨64,268670174,268670329⟩]
theorem checked46273 : checkPrefixCuts (2^48) 6069026817 10 Manual.Count131072.C046273.packed 64 cuts46273 = true := by
 decide +kernel
def pointBounds46273 : List (Nat × Nat × Nat) := [(6069030912,110691174224851,110691560794780)]
theorem point_links_checked46273 : (cuts46273.take 1).map (fun c => (6069026817-1+2*2^10*c.k,110691165783891+c.lower,110691552353815+c.upper)) = pointBounds46273 := by
 decide +kernel
def cuts46274 : List PrefixCut := [⟨31,132129982,132130054⟩,
⟨64,271818028,271818180⟩]
theorem checked46274 : checkPrefixCuts (2^48) 6069157889 10 Manual.Count131072.C046274.packed 64 cuts46274 = true := by
 decide +kernel
def pointBounds46274 : List (Nat × Nat × Nat) := [(6069221376,110691566584047,110691953154198)]
theorem point_links_checked46274 : (cuts46274.take 1).map (fun c => (6069157889-1+2*2^10*c.k,110691434454065+c.lower,110691821024144+c.upper)) = pointBounds46274 := by
 decide +kernel
def cuts46275 : List PrefixCut := [⟨60,253169030,253169180⟩,
⟨64,270142626,270142785⟩]
theorem checked46275 : checkPrefixCuts (2^48) 6069288961 10 Manual.Count131072.C046275.packed 64 cuts46275 = true := by
 decide +kernel
def pointBounds46275 : List (Nat × Nat × Nat) := [(6069411840,110691959441123,110692346011504)]
theorem point_links_checked46275 : (cuts46275.take 1).map (fun c => (6069288961-1+2*2^10*c.k,110691706272093+c.lower,110692092842324+c.upper)) = pointBounds46275 := by
 decide +kernel
def cuts46276 : List PrefixCut := [⟨64,263041344,263041503⟩]
theorem checked46276 : checkPrefixCuts (2^48) 6069420033 10 Manual.Count131072.C046276.packed 64 cuts46276 = true := by
 decide +kernel
def cuts46277 : List PrefixCut := [⟨25,106244467,106244532⟩,
⟨64,270130942,270131103⟩]
theorem checked46277 : checkPrefixCuts (2^48) 6069551105 10 Manual.Count131072.C046277.packed 64 cuts46277 = true := by
 decide +kernel
def pointBounds46277 : List (Nat × Nat × Nat) := [(6069602304,110692345700530,110692732271144)]
theorem point_links_checked46277 : (cuts46277.take 1).map (fun c => (6069551105-1+2*2^10*c.k,110692239456063+c.lower,110692626026612+c.upper)) = pointBounds46277 := by
 decide +kernel
def cuts46278 : List PrefixCut := [⟨54,227601067,227601198⟩,
⟨64,271052555,271052712⟩]
theorem checked46278 : checkPrefixCuts (2^48) 6069682177 10 Manual.Count131072.C046278.packed 64 cuts46278 = true := by
 decide +kernel
def pointBounds46278 : List (Nat × Nat × Nat) := [(6069792768,110692737188072,110693123758913)]
theorem point_links_checked46278 : (cuts46278.take 1).map (fun c => (6069682177-1+2*2^10*c.k,110692509587005+c.lower,110692896157715+c.upper)) = pointBounds46278 := by
 decide +kernel
def cuts46279 : List PrefixCut := [⟨64,271649575,271649727⟩]
theorem checked46279 : checkPrefixCuts (2^48) 6069813249 10 Manual.Count131072.C046279.packed 64 cuts46279 = true := by
 decide +kernel
def cuts46280 : List PrefixCut := [⟨19,79481195,79481238⟩,
⟨64,267748512,267748661⟩]
theorem checked46280 : checkPrefixCuts (2^48) 6069944321 10 Manual.Count131072.C046280.packed 64 cuts46280 = true := by
 decide +kernel
def pointBounds46280 : List (Nat × Nat × Nat) := [(6069983232,110693131770330,110693518341392)]
theorem point_links_checked46280 : (cuts46280.take 1).map (fun c => (6069944321-1+2*2^10*c.k,110693052289135+c.lower,110693438860154+c.upper)) = pointBounds46280 := by
 decide +kernel
def cuts46281 : List PrefixCut := [⟨48,201062606,201062722⟩,
⟨64,268391891,268392046⟩]
theorem checked46281 : checkPrefixCuts (2^48) 6070075393 10 Manual.Count131072.C046281.packed 64 cuts46281 = true := by
 decide +kernel
def pointBounds46281 : List (Nat × Nat × Nat) := [(6070173696,110693521100253,110693907671537)]
theorem point_links_checked46281 : (cuts46281.take 1).map (fun c => (6070075393-1+2*2^10*c.k,110693320037647+c.lower,110693706608815+c.upper)) = pointBounds46281 := by
 decide +kernel
def cuts46282 : List PrefixCut := [⟨64,272883962,272884113⟩]
theorem checked46282 : checkPrefixCuts (2^48) 6070206465 10 Manual.Count131072.C046282.packed 64 cuts46282 = true := by
 decide +kernel
def cuts46283 : List PrefixCut := [⟨13,54112390,54112421⟩,
⟨64,267174725,267174879⟩]
theorem checked46283 : checkPrefixCuts (2^48) 6070337537 10 Manual.Count131072.C046283.packed 64 cuts46283 = true := by
 decide +kernel
def pointBounds46283 : List (Nat × Nat × Nat) := [(6070364160,110693915425890,110694301997395)]
theorem point_links_checked46283 : (cuts46283.take 1).map (fun c => (6070337537-1+2*2^10*c.k,110693861313500+c.lower,110694247884974+c.upper)) = pointBounds46283 := by
 decide +kernel
def cuts46284 : List PrefixCut := [⟨42,176382251,176382354⟩,
⟨64,268977294,268977453⟩]
theorem checked46284 : checkPrefixCuts (2^48) 6070468609 10 Manual.Count131072.C046284.packed 64 cuts46284 = true := by
 decide +kernel
def pointBounds46284 : List (Nat × Nat × Nat) := [(6070554624,110694304870476,110694691442207)]
theorem point_links_checked46284 : (cuts46284.take 1).map (fun c => (6070468609-1+2*2^10*c.k,110694128488225+c.lower,110694515059853+c.upper)) = pointBounds46284 := by
 decide +kernel
def cuts46285 : List PrefixCut := [⟨64,268739662,268739815⟩]
theorem checked46285 : checkPrefixCuts (2^48) 6070599681 10 Manual.Count131072.C046285.packed 64 cuts46285 = true := by
 decide +kernel
def cuts46286 : List PrefixCut := [⟨7,29627776,29627793⟩,
⟨64,271283956,271284113⟩]
theorem checked46286 : checkPrefixCuts (2^48) 6070730753 10 Manual.Count131072.C046286.packed 64 cuts46286 = true := by
 decide +kernel
def pointBounds46286 : List (Nat × Nat × Nat) := [(6070745088,110694695832957,110695082404914)]
theorem point_links_checked46286 : (cuts46286.take 1).map (fun c => (6070730753-1+2*2^10*c.k,110694666205181+c.lower,110695052777121+c.upper)) = pointBounds46286 := by
 decide +kernel
def cuts46287 : List PrefixCut := [⟨36,152817787,152817867⟩,
⟨64,272066301,272066447⟩]
theorem checked46287 : checkPrefixCuts (2^48) 6070861825 10 Manual.Count131072.C046287.packed 64 cuts46287 = true := by
 decide +kernel
def pointBounds46287 : List (Nat × Nat × Nat) := [(6070935552,110695090306924,110695476879101)]
theorem point_links_checked46287 : (cuts46287.take 1).map (fun c => (6070861825-1+2*2^10*c.k,110694937489137+c.lower,110695324061234+c.upper)) = pointBounds46287 := by
 decide +kernel
def cuts46288 : List PrefixCut := [⟨64,268165894,268166049⟩]
theorem checked46288 : checkPrefixCuts (2^48) 6070992897 10 Manual.Count131072.C046288.packed 64 cuts46288 = true := by
 decide +kernel
def cuts46289 : List PrefixCut := [⟨1,4636289,4636292⟩,
⟨64,264543830,264543977⟩]
theorem checked46289 : checkPrefixCuts (2^48) 6071123969 10 Manual.Count131072.C046289.packed 64 cuts46289 = true := by
 decide +kernel
def pointBounds46289 : List (Nat × Nat × Nat) := [(6071126016,110695482357621,110695868930022)]
theorem point_links_checked46289 : (cuts46289.take 1).map (fun c => (6071123969-1+2*2^10*c.k,110695477721332+c.lower,110695864293730+c.upper)) = pointBounds46289 := by
 decide +kernel
def cuts46290 : List PrefixCut := [⟨30,130415353,130415430⟩,
⟨64,270333337,270333495⟩]
theorem checked46290 : checkPrefixCuts (2^48) 6071255041 10 Manual.Count131072.C046290.packed 64 cuts46290 = true := by
 decide +kernel
def pointBounds46290 : List (Nat × Nat × Nat) := [(6071316480,110695872680515,110696259253137)]
theorem point_links_checked46290 : (cuts46290.take 1).map (fun c => (6071255041-1+2*2^10*c.k,110695742265162+c.lower,110696128837707+c.upper)) = pointBounds46290 := by
 decide +kernel
def cuts46291 : List PrefixCut := [⟨59,248074662,248074805⟩,
⟨64,269400232,269400388⟩]
theorem checked46291 : checkPrefixCuts (2^48) 6071386113 10 Manual.Count131072.C046291.packed 64 cuts46291 = true := by
 decide +kernel
def pointBounds46291 : List (Nat × Nat × Nat) := [(6071506944,110696260673161,110696647246007)]
theorem point_links_checked46291 : (cuts46291.take 1).map (fun c => (6071386113-1+2*2^10*c.k,110696012598499+c.lower,110696399171202+c.upper)) = pointBounds46291 := by
 decide +kernel
def cuts46292 : List PrefixCut := [⟨64,274864855,274865016⟩]
theorem checked46292 : checkPrefixCuts (2^48) 6071517185 10 Manual.Count131072.C046292.packed 64 cuts46292 = true := by
 decide +kernel
def cuts46293 : List PrefixCut := [⟨24,102916324,102916383⟩,
⟨64,267580687,267580844⟩]
theorem checked46293 : checkPrefixCuts (2^48) 6071648257 10 Manual.Count131072.C046293.packed 64 cuts46293 = true := by
 decide +kernel
def pointBounds46293 : List (Nat × Nat × Nat) := [(6071697408,110696659779910,110697046352989)]
theorem point_links_checked46293 : (cuts46293.take 1).map (fun c => (6071648257-1+2*2^10*c.k,110696556863586+c.lower,110696943436606+c.upper)) = pointBounds46293 := by
 decide +kernel
def cuts46294 : List PrefixCut := [⟨53,223211256,223211386⟩,
⟨64,271607940,271608097⟩]
theorem checked46294 : checkPrefixCuts (2^48) 6071779329 10 Manual.Count131072.C046294.packed 64 cuts46294 = true := by
 decide +kernel
def pointBounds46294 : List (Nat × Nat × Nat) := [(6071887872,110697047655529,110697434228836)]
theorem point_links_checked46294 : (cuts46294.take 1).map (fun c => (6071779329-1+2*2^10*c.k,110696824444273+c.lower,110697211017450+c.upper)) = pointBounds46294 := by
 decide +kernel
def cuts46295 : List PrefixCut := [⟨64,270906731,270906885⟩]
theorem checked46295 : checkPrefixCuts (2^48) 6071910401 10 Manual.Count131072.C046295.packed 64 cuts46295 = true := by
 decide +kernel
def cuts46296 : List PrefixCut := [⟨18,75049960,75050005⟩,
⟨64,265152849,265153005⟩]
theorem checked46296 : checkPrefixCuts (2^48) 6072041473 10 Manual.Count131072.C046296.packed 64 cuts46296 = true := by
 decide +kernel
def pointBounds46296 : List (Nat × Nat × Nat) := [(6072078336,110697442008904,110697828582437)]
theorem point_links_checked46296 : (cuts46296.take 1).map (fun c => (6072041473-1+2*2^10*c.k,110697366958944+c.lower,110697753532432+c.upper)) = pointBounds46296 := by
 decide +kernel
def cuts46297 : List PrefixCut := [⟨47,197516625,197516742⟩,
⟨64,268901824,268901980⟩]
theorem checked46297 : checkPrefixCuts (2^48) 6072172545 10 Manual.Count131072.C046297.packed 64 cuts46297 = true := by
 decide +kernel
def pointBounds46297 : List (Nat × Nat × Nat) := [(6072268800,110697829628418,110698216202179)]
theorem point_links_checked46297 : (cuts46297.take 1).map (fun c => (6072172545-1+2*2^10*c.k,110697632111793+c.lower,110698018685437+c.upper)) = pointBounds46297 := by
 decide +kernel
def cuts46298 : List PrefixCut := [⟨64,273763155,273763304⟩]
theorem checked46298 : checkPrefixCuts (2^48) 6072303617 10 Manual.Count131072.C046298.packed 64 cuts46298 = true := by
 decide +kernel
def cuts46299 : List PrefixCut := [⟨12,52517719,52517748⟩,
⟨64,267546019,267546170⟩]
theorem checked46299 : checkPrefixCuts (2^48) 6072434689 10 Manual.Count131072.C046299.packed 64 cuts46299 = true := by
 decide +kernel
def pointBounds46299 : List (Nat × Nat × Nat) := [(6072459264,110698227294491,110698613868469)]
theorem point_links_checked46299 : (cuts46299.take 1).map (fun c => (6072434689-1+2*2^10*c.k,110698174776772+c.lower,110698561350721+c.upper)) = pointBounds46299 := by
 decide +kernel
def cuts46300 : List PrefixCut := [⟨41,175487035,175487134⟩,
⟨64,271758195,271758348⟩]
theorem checked46300 : checkPrefixCuts (2^48) 6072565761 10 Manual.Count131072.C046300.packed 64 cuts46300 = true := by
 decide +kernel
def pointBounds46300 : List (Nat × Nat × Nat) := [(6072649728,110698617809826,110699004384025)]
theorem point_links_checked46300 : (cuts46300.take 1).map (fun c => (6072565761-1+2*2^10*c.k,110698442322791+c.lower,110698828896891+c.upper)) = pointBounds46300 := by
 decide +kernel
def cuts46301 : List PrefixCut := [⟨64,270593570,270593725⟩]
theorem checked46301 : checkPrefixCuts (2^48) 6072696833 10 Manual.Count131072.C046301.packed 64 cuts46301 = true := by
 decide +kernel
def cuts46302 : List PrefixCut := [⟨6,26419409,26419426⟩,
⟨64,270680420,270680576⟩]
theorem checked46302 : checkPrefixCuts (2^48) 6072827905 10 Manual.Count131072.C046302.packed 64 cuts46302 = true := by
 decide +kernel
def pointBounds46302 : List (Nat × Nat × Nat) := [(6072840192,110699011093965,110699397668390)]
theorem point_links_checked46302 : (cuts46302.take 1).map (fun c => (6072827905-1+2*2^10*c.k,110698984674556+c.lower,110699371248964+c.upper)) = pointBounds46302 := by
 decide +kernel
def cuts46303 : List PrefixCut := [⟨35,144190542,144190624⟩,
⟨64,265159118,265159270⟩]
theorem checked46303 : checkPrefixCuts (2^48) 6072958977 10 Manual.Count131072.C046303.packed 64 cuts46303 = true := by
 decide +kernel
def pointBounds46303 : List (Nat × Nat × Nat) := [(6073030656,110699399545518,110699786120164)]
theorem point_links_checked46303 : (cuts46303.take 1).map (fun c => (6072958977-1+2*2^10*c.k,110699255354976+c.lower,110699641929540+c.upper)) = pointBounds46303 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000196
