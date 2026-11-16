import PlattAssemblyKernel
import PlattCertificates.Count131072.C021312
import PlattCertificates.Count131072.C021313
import PlattCertificates.Count131072.C021314
import PlattCertificates.Count131072.C021315
import PlattCertificates.Count131072.C021316
import PlattCertificates.Count131072.C021317
import PlattCertificates.Count131072.C021318
import PlattCertificates.Count131072.C021319
import PlattCertificates.Count131072.C021320
import PlattCertificates.Count131072.C021321
import PlattCertificates.Count131072.C021322
import PlattCertificates.Count131072.C021323
import PlattCertificates.Count131072.C021324
import PlattCertificates.Count131072.C021325
import PlattCertificates.Count131072.C021326
import PlattCertificates.Count131072.C021327
import PlattCertificates.Count131072.C021328
import PlattCertificates.Count131072.C021329
import PlattCertificates.Count131072.C021330
import PlattCertificates.Count131072.C021331
import PlattCertificates.Count131072.C021332
import PlattCertificates.Count131072.C021333
import PlattCertificates.Count131072.C021334
import PlattCertificates.Count131072.C021335
import PlattCertificates.Count131072.C021336
import PlattCertificates.Count131072.C021337
import PlattCertificates.Count131072.C021338
import PlattCertificates.Count131072.C021339
import PlattCertificates.Count131072.C021340
import PlattCertificates.Count131072.C021341
import PlattCertificates.Count131072.C021342
import PlattCertificates.Count131072.C021343
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21312 : List PrefixCut := [⟨26,125173637,125173710⟩,
⟨112,539727439,539727748⟩,
⟨128,617303890,617304244⟩]
theorem checked21312 : checkPrefixCuts (2^48) 2797338625 9 Manual.Count131072.C021312.packed 128 cuts21312 = true := by
 decide +kernel
def pointBounds21312 : List (Nat × Nat × Nat) := [(2797365248,100843074286336,100843455134825),(2797453312,100843488840138,100843869688863)]
theorem point_links_checked21312 : (cuts21312.take 2).map (fun c => (2797338625-1+2*2^9*c.k,100842949112699+c.lower,100843329961115+c.upper)) = pointBounds21312 := by
 decide +kernel
def cuts21313 : List PrefixCut := [⟨70,333643969,333644163⟩,
⟨128,611539915,611540269⟩]
theorem checked21313 : checkPrefixCuts (2^48) 2797469697 9 Manual.Count131072.C021313.packed 128 cuts21313 = true := by
 decide +kernel
def pointBounds21313 : List (Nat × Nat × Nat) := [(2797541376,100843900060558,100844280909522)]
theorem point_links_checked21313 : (cuts21313.take 1).map (fun c => (2797469697-1+2*2^9*c.k,100843566416589+c.lower,100843947265359+c.upper)) = pointBounds21313 := by
 decide +kernel
def cuts21314 : List PrefixCut := [⟨28,130494333,130494408⟩,
⟨114,534545477,534545789⟩,
⟨128,601852566,601852916⟩]
theorem checked21314 : checkPrefixCuts (2^48) 2797600769 9 Manual.Count131072.C021314.packed 128 cuts21314 = true := by
 decide +kernel
def pointBounds21314 : List (Nat × Nat × Nat) := [(2797629440,100844308450837,100844689300036),(2797717504,100844712501981,100845093351417)]
theorem point_links_checked21314 : (cuts21314.take 2).map (fun c => (2797600769-1+2*2^9*c.k,100844177956504+c.lower,100844558805628+c.upper)) = pointBounds21314 := by
 decide +kernel
def cuts21315 : List PrefixCut := [⟨72,343874478,343874676⟩,
⟨128,611784458,611784808⟩]
theorem checked21315 : checkPrefixCuts (2^48) 2797731841 9 Manual.Count131072.C021315.packed 128 cuts21315 = true := by
 decide +kernel
def pointBounds21315 : List (Nat × Nat × Nat) := [(2797805568,100845123683548,100845504533220)]
theorem point_links_checked21315 : (cuts21315.take 1).map (fun c => (2797731841-1+2*2^9*c.k,100844779809070+c.lower,100845160658544+c.upper)) = pointBounds21315 := by
 decide +kernel
def cuts21316 : List PrefixCut := [⟨30,137826093,137826174⟩,
⟨116,553206972,553207289⟩,
⟨128,608737639,608737988⟩]
theorem checked21316 : checkPrefixCuts (2^48) 2797862913 9 Manual.Count131072.C021316.packed 128 cuts21316 = true := by
 decide +kernel
def pointBounds21316 : List (Nat × Nat × Nat) := [(2797893632,100845529419621,100845910269526),(2797981696,100845944800500,100846325650641)]
theorem point_links_checked21316 : (cuts21316.take 2).map (fun c => (2797862913-1+2*2^9*c.k,100845391593528+c.lower,100845772443352+c.upper)) = pointBounds21316 := by
 decide +kernel
def cuts21317 : List PrefixCut := [⟨74,353600038,353600244⟩,
⟨128,604383653,604384004⟩]
theorem checked21317 : checkPrefixCuts (2^48) 2797993985 9 Manual.Count131072.C021317.packed 128 cuts21317 = true := by
 decide +kernel
def pointBounds21317 : List (Nat × Nat × Nat) := [(2798069760,100846353931205,100846734781584)]
theorem point_links_checked21317 : (cuts21317.take 1).map (fun c => (2797993985-1+2*2^9*c.k,100846000331167+c.lower,100846381181340+c.upper)) = pointBounds21317 := by
 decide +kernel
def cuts21318 : List PrefixCut := [⟨32,152499782,152499874⟩,
⟨118,557882919,557883248⟩,
⟨128,605864145,605864503⟩]
theorem checked21318 : checkPrefixCuts (2^48) 2798125057 9 Manual.Count131072.C021318.packed 128 cuts21318 = true := by
 decide +kernel
def pointBounds21318 : List (Nat × Nat × Nat) := [(2798157824,100846757214602,100847138065218),(2798245888,100847162597739,100847543448592)]
theorem point_links_checked21318 : (cuts21318.take 2).map (fun c => (2798125057-1+2*2^9*c.k,100846604714820+c.lower,100846985565344+c.upper)) = pointBounds21318 := by
 decide +kernel
def cuts21319 : List PrefixCut := [⟨76,358093264,358093479⟩,
⟨128,606036861,606037221⟩]
theorem checked21319 : checkPrefixCuts (2^48) 2798256129 9 Manual.Count131072.C021319.packed 128 cuts21319 = true := by
 decide +kernel
def pointBounds21319 : List (Nat × Nat × Nat) := [(2798333952,100847568672229,100847949523326)]
theorem point_links_checked21319 : (cuts21319.take 1).map (fun c => (2798256129-1+2*2^9*c.k,100847210578965+c.lower,100847591429847+c.upper)) = pointBounds21319 := by
 decide +kernel
def cuts21320 : List PrefixCut := [⟨34,162141495,162141590⟩,
⟨120,568190413,568190746⟩,
⟨128,605505637,605505990⟩]
theorem checked21320 : checkPrefixCuts (2^48) 2798387201 9 Manual.Count131072.C021320.packed 128 cuts21320 = true := by
 decide +kernel
def pointBounds21320 : List (Nat × Nat × Nat) := [(2798422016,100847978757321,100848359608658),(2798510080,100848384806239,100848765657814)]
theorem point_links_checked21320 : (cuts21320.take 2).map (fun c => (2798387201-1+2*2^9*c.k,100847816615826+c.lower,100848197467068+c.upper)) = pointBounds21320 := by
 decide +kernel
def cuts21321 : List PrefixCut := [⟨78,369424954,369425167⟩,
⟨128,609902595,609902941⟩]
theorem checked21321 : checkPrefixCuts (2^48) 2798518273 9 Manual.Count131072.C021321.packed 128 cuts21321 = true := by
 decide +kernel
def pointBounds21321 : List (Nat × Nat × Nat) := [(2798598144,100848791546417,100849172398225)]
theorem point_links_checked21321 : (cuts21321.take 1).map (fun c => (2798518273-1+2*2^9*c.k,100848422121463+c.lower,100848802973058+c.upper)) = pointBounds21321 := by
 decide +kernel
def cuts21322 : List PrefixCut := [⟨36,169669352,169669445⟩,
⟨122,580306311,580306642⟩,
⟨128,607259249,607259596⟩]
theorem checked21322 : checkPrefixCuts (2^48) 2798649345 9 Manual.Count131072.C021322.packed 128 cuts21322 = true := by
 decide +kernel
def pointBounds21322 : List (Nat × Nat × Nat) := [(2798686208,100849201693410,100849582545444),(2798774272,100849612330369,100849993182641)]
theorem point_links_checked21322 : (cuts21322.take 2).map (fun c => (2798649345-1+2*2^9*c.k,100849032024058+c.lower,100849412875999+c.upper)) = pointBounds21322 := by
 decide +kernel
def cuts21323 : List PrefixCut := [⟨80,378139677,378139900⟩,
⟨128,598783066,598783422⟩]
theorem checked21323 : checkPrefixCuts (2^48) 2798780417 9 Manual.Count131072.C021323.packed 128 cuts21323 = true := by
 decide +kernel
def pointBounds21323 : List (Nat × Nat × Nat) := [(2798862336,100850017422984,100850398275495)]
theorem point_links_checked21323 : (cuts21323.take 1).map (fun c => (2798780417-1+2*2^9*c.k,100849639283307+c.lower,100850020135595+c.upper)) = pointBounds21323 := by
 decide +kernel
def cuts21324 : List PrefixCut := [⟨38,177095204,177095310⟩,
⟨124,580754599,580754942⟩,
⟨128,599660107,599660460⟩]
theorem checked21324 : checkPrefixCuts (2^48) 2798911489 9 Manual.Count131072.C021324.packed 128 cuts21324 = true := by
 decide +kernel
def pointBounds21324 : List (Nat × Nat × Nat) := [(2798950400,100850415161577,100850796014327),(2799038464,100850818820972,100851199673959)]
theorem point_links_checked21324 : (cuts21324.take 2).map (fun c => (2798911489-1+2*2^9*c.k,100850238066373+c.lower,100850618919017+c.upper)) = pointBounds21324 := by
 decide +kernel
def cuts21325 : List PrefixCut := [⟨82,385042787,385043010⟩,
⟨128,606168224,606168576⟩]
theorem checked21325 : checkPrefixCuts (2^48) 2799042561 9 Manual.Count131072.C021325.packed 128 cuts21325 = true := by
 decide +kernel
def pointBounds21325 : List (Nat × Nat × Nat) := [(2799126528,100851222769267,100851603622487)]
theorem point_links_checked21325 : (cuts21325.take 1).map (fun c => (2799042561-1+2*2^9*c.k,100850837726480+c.lower,100851218579477+c.upper)) = pointBounds21325 := by
 decide +kernel
def cuts21326 : List PrefixCut := [⟨40,192463606,192463715⟩,
⟨126,598296998,598297340⟩,
⟨128,608050518,608050866⟩]
theorem checked21326 : checkPrefixCuts (2^48) 2799173633 9 Manual.Count131072.C021326.packed 128 cuts21326 = true := by
 decide +kernel
def pointBounds21326 : List (Nat × Nat × Nat) := [(2799214592,100851636358310,100852017211768),(2799302656,100852042191702,100852423045393)]
theorem point_links_checked21326 : (cuts21326.take 2).map (fun c => (2799173633-1+2*2^9*c.k,100851443894704+c.lower,100851824748053+c.upper)) = pointBounds21326 := by
 decide +kernel
def cuts21327 : List PrefixCut := [⟨84,394257168,394257391⟩,
⟨128,596861051,596861393⟩]
theorem checked21327 : checkPrefixCuts (2^48) 2799304705 9 Manual.Count131072.C021327.packed 128 cuts21327 = true := by
 decide +kernel
def pointBounds21327 : List (Nat × Nat × Nat) := [(2799390720,100852446202390,100852827056310)]
theorem point_links_checked21327 : (cuts21327.take 1).map (fun c => (2799304705-1+2*2^9*c.k,100852051945222+c.lower,100852432798919+c.upper)) = pointBounds21327 := by
 decide +kernel
def cuts21328 : List PrefixCut := [⟨42,198377734,198377852⟩,
⟨128,611713594,611713945⟩]
theorem checked21328 : checkPrefixCuts (2^48) 2799435777 9 Manual.Count131072.C021328.packed 128 cuts21328 = true := by
 decide +kernel
def pointBounds21328 : List (Nat × Nat × Nat) := [(2799478784,100852847184007,100853228038164),(2799566848,100853260519867,100853641374257)]
theorem point_links_checked21328 : (cuts21328.take 2).map (fun c => (2799435777-1+2*2^9*c.k,100852648806273+c.lower,100853029660312+c.upper)) = pointBounds21328 := by
 decide +kernel
def cuts21329 : List PrefixCut := [⟨86,411613743,411613984⟩,
⟨128,607563030,607563386⟩]
theorem checked21329 : checkPrefixCuts (2^48) 2799566849 9 Manual.Count131072.C021329.packed 128 cuts21329 = true := by
 decide +kernel
def pointBounds21329 : List (Nat × Nat × Nat) := [(2799654912,100853672133610,100854052988241)]
theorem point_links_checked21329 : (cuts21329.take 1).map (fun c => (2799566849-1+2*2^9*c.k,100853260519867+c.lower,100853641374257+c.upper)) = pointBounds21329 := by
 decide +kernel
def cuts21330 : List PrefixCut := [⟨44,206904701,206904821⟩,
⟨128,603915166,603915515⟩]
theorem checked21330 : checkPrefixCuts (2^48) 2799697921 9 Manual.Count131072.C021330.packed 128 cuts21330 = true := by
 decide +kernel
def pointBounds21330 : List (Nat × Nat × Nat) := [(2799742976,100854074987598,100854455842464)]
theorem point_links_checked21330 : (cuts21330.take 1).map (fun c => (2799697921-1+2*2^9*c.k,100853868082897+c.lower,100854248937643+c.upper)) = pointBounds21330 := by
 decide +kernel
def cuts21331 : List PrefixCut := [⟨2,9550621,9550626⟩,
⟨88,416501059,416501295⟩,
⟨128,601474255,601474602⟩]
theorem checked21331 : checkPrefixCuts (2^48) 2799828993 9 Manual.Count131072.C021331.packed 128 cuts21331 = true := by
 decide +kernel
def pointBounds21331 : List (Nat × Nat × Nat) := [(2799831040,100854481548684,100854862403784),(2799919104,100854888499122,100855269354453)]
theorem point_links_checked21331 : (cuts21331.take 2).map (fun c => (2799828993-1+2*2^9*c.k,100854471998063+c.lower,100854852853158+c.upper)) = pointBounds21331 := by
 decide +kernel
def cuts21332 : List PrefixCut := [⟨46,218848021,218848147⟩,
⟨128,604160273,604160620⟩]
theorem checked21332 : checkPrefixCuts (2^48) 2799960065 9 Manual.Count131072.C021332.packed 128 cuts21332 = true := by
 decide +kernel
def pointBounds21332 : List (Nat × Nat × Nat) := [(2800007168,100855292320339,100855673175907)]
theorem point_links_checked21332 : (cuts21332.take 1).map (fun c => (2799960065-1+2*2^9*c.k,100855073472318+c.lower,100855454327760+c.upper)) = pointBounds21332 := by
 decide +kernel
def cuts21333 : List PrefixCut := [⟨4,19903634,19903646⟩,
⟨90,428323532,428323787⟩,
⟨128,608755981,608756335⟩]
theorem checked21333 : checkPrefixCuts (2^48) 2800091137 9 Manual.Count131072.C021333.packed 128 cuts21333 = true := by
 decide +kernel
def pointBounds21333 : List (Nat × Nat × Nat) := [(2800095232,100855697536225,100856078392026),(2800183296,100856105956123,100856486812167)]
theorem point_links_checked21333 : (cuts21333.take 2).map (fun c => (2800091137-1+2*2^9*c.k,100855677632591+c.lower,100856058488380+c.upper)) = pointBounds21333 := by
 decide +kernel
def cuts21334 : List PrefixCut := [⟨48,226165267,226165397⟩,
⟨128,603299522,603299872⟩]
theorem checked21334 : checkPrefixCuts (2^48) 2800222209 9 Manual.Count131072.C021334.packed 128 cuts21334 = true := by
 decide +kernel
def pointBounds21334 : List (Nat × Nat × Nat) := [(2800271360,100856512553839,100856893410112)]
theorem point_links_checked21334 : (cuts21334.take 1).map (fun c => (2800222209-1+2*2^9*c.k,100856286388572+c.lower,100856667244715+c.upper)) = pointBounds21334 := by
 decide +kernel
def cuts21335 : List PrefixCut := [⟨6,28344938,28344954⟩,
⟨92,435118085,435118342⟩,
⟨128,603673397,603673750⟩]
theorem checked21335 : checkPrefixCuts (2^48) 2800353281 9 Manual.Count131072.C021335.packed 128 cuts21335 = true := by
 decide +kernel
def pointBounds21335 : List (Nat × Nat × Nat) := [(2800359424,100856918033032,100857298889541),(2800447488,100857324806179,100857705662929)]
theorem point_links_checked21335 : (cuts21335.take 2).map (fun c => (2800353281-1+2*2^9*c.k,100856889688094+c.lower,100857270544587+c.upper)) = pointBounds21335 := by
 decide +kernel
def cuts21336 : List PrefixCut := [⟨50,236697394,236697530⟩,
⟨128,605353740,605354094⟩]
theorem checked21336 : checkPrefixCuts (2^48) 2800484353 9 Manual.Count131072.C021336.packed 128 cuts21336 = true := by
 decide +kernel
def pointBounds21336 : List (Nat × Nat × Nat) := [(2800535552,100857730058885,100858110915867)]
theorem point_links_checked21336 : (cuts21336.take 1).map (fun c => (2800484353-1+2*2^9*c.k,100857493361491+c.lower,100857874218337+c.upper)) = pointBounds21336 := by
 decide +kernel
def cuts21337 : List PrefixCut := [⟨8,36985660,36985683⟩,
⟨94,445026941,445027197⟩,
⟨128,604822861,604823209⟩]
theorem checked21337 : checkPrefixCuts (2^48) 2800615425 9 Manual.Count131072.C021337.packed 128 cuts21337 = true := by
 decide +kernel
def pointBounds21337 : List (Nat × Nat × Nat) := [(2800623616,100858135700891,100858516558114),(2800711680,100858543742172,100858924599628)]
theorem point_links_checked21337 : (cuts21337.take 2).map (fun c => (2800615425-1+2*2^9*c.k,100858098715231+c.lower,100858479572431+c.upper)) = pointBounds21337 := by
 decide +kernel
def cuts21338 : List PrefixCut := [⟨52,249137044,249137190⟩,
⟨128,607307049,607307402⟩]
theorem checked21338 : checkPrefixCuts (2^48) 2800746497 9 Manual.Count131072.C021338.packed 128 cuts21338 = true := by
 decide +kernel
def pointBounds21338 : List (Nat × Nat × Nat) := [(2800799744,100858952675136,100859333532830)]
theorem point_links_checked21338 : (cuts21338.take 1).map (fun c => (2800746497-1+2*2^9*c.k,100858703538092+c.lower,100859084395640+c.upper)) = pointBounds21338 := by
 decide +kernel
def cuts21339 : List PrefixCut := [⟨10,44217825,44217851⟩,
⟨96,449507330,449507584⟩,
⟨128,600143545,600143884⟩]
theorem checked21339 : checkPrefixCuts (2^48) 2800877569 9 Manual.Count131072.C021339.packed 128 cuts21339 = true := by
 decide +kernel
def pointBounds21339 : List (Nat × Nat × Nat) := [(2800887808,100859355062966,100859735920893),(2800975872,100859760352471,100860141210626)]
theorem point_links_checked21339 : (cuts21339.take 2).map (fun c => (2800877569-1+2*2^9*c.k,100859310845141+c.lower,100859691703042+c.upper)) = pointBounds21339 := by
 decide +kernel
def cuts21340 : List PrefixCut := [⟨54,256449357,256449501⟩,
⟨128,610968208,610968555⟩]
theorem checked21340 : checkPrefixCuts (2^48) 2801008641 9 Manual.Count131072.C021340.packed 128 cuts21340 = true := by
 decide +kernel
def pointBounds21340 : List (Nat × Nat × Nat) := [(2801063936,100860167438043,100860548296427)]
theorem point_links_checked21340 : (cuts21340.take 1).map (fun c => (2801008641-1+2*2^9*c.k,100859910988686+c.lower,100860291846926+c.upper)) = pointBounds21340 := by
 decide +kernel
def cuts21341 : List PrefixCut := [⟨12,55870009,55870040⟩,
⟨98,455293169,455293432⟩,
⟨128,598680557,598680903⟩]
theorem checked21341 : checkPrefixCuts (2^48) 2801139713 9 Manual.Count131072.C021341.packed 128 cuts21341 = true := by
 decide +kernel
def pointBounds21341 : List (Nat × Nat × Nat) := [(2801152000,100860577826903,100860958685521),(2801240064,100860977250063,100861358108913)]
theorem point_links_checked21341 : (cuts21341.take 2).map (fun c => (2801139713-1+2*2^9*c.k,100860521956894+c.lower,100860902815481+c.upper)) = pointBounds21341 := by
 decide +kernel
def cuts21342 : List PrefixCut := [⟨56,269789161,269789322⟩,
⟨128,614829803,614830162⟩]
theorem checked21342 : checkPrefixCuts (2^48) 2801270785 9 Manual.Count131072.C021342.packed 128 cuts21342 = true := by
 decide +kernel
def pointBounds21342 : List (Nat × Nat × Nat) := [(2801328128,100861390426612,100861771285706)]
theorem point_links_checked21342 : (cuts21342.take 1).map (fun c => (2801270785-1+2*2^9*c.k,100861120637451+c.lower,100861501496384+c.upper)) = pointBounds21342 := by
 decide +kernel
def cuts21343 : List PrefixCut := [⟨14,66515234,66515272⟩,
⟨100,475345403,475345662⟩,
⟨128,610179172,610179507⟩]
theorem checked21343 : checkPrefixCuts (2^48) 2801401857 9 Manual.Count131072.C021343.packed 128 cuts21343 = true := by
 decide +kernel
def pointBounds21343 : List (Nat × Nat × Nat) := [(2801416192,100861801982488,100862182841818),(2801504256,100862210812657,100862591672208)]
theorem point_links_checked21343 : (cuts21343.take 2).map (fun c => (2801401857-1+2*2^9*c.k,100861735467254+c.lower,100862116326546+c.upper)) = pointBounds21343 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000041
