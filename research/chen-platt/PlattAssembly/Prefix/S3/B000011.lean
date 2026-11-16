import PlattAssemblyKernel
import PlattCertificates.Count131072.C020352
import PlattCertificates.Count131072.C020353
import PlattCertificates.Count131072.C020354
import PlattCertificates.Count131072.C020355
import PlattCertificates.Count131072.C020356
import PlattCertificates.Count131072.C020357
import PlattCertificates.Count131072.C020358
import PlattCertificates.Count131072.C020359
import PlattCertificates.Count131072.C020360
import PlattCertificates.Count131072.C020361
import PlattCertificates.Count131072.C020362
import PlattCertificates.Count131072.C020363
import PlattCertificates.Count131072.C020364
import PlattCertificates.Count131072.C020365
import PlattCertificates.Count131072.C020366
import PlattCertificates.Count131072.C020367
import PlattCertificates.Count131072.C020368
import PlattCertificates.Count131072.C020369
import PlattCertificates.Count131072.C020370
import PlattCertificates.Count131072.C020371
import PlattCertificates.Count131072.C020372
import PlattCertificates.Count131072.C020373
import PlattCertificates.Count131072.C020374
import PlattCertificates.Count131072.C020375
import PlattCertificates.Count131072.C020376
import PlattCertificates.Count131072.C020377
import PlattCertificates.Count131072.C020378
import PlattCertificates.Count131072.C020379
import PlattCertificates.Count131072.C020380
import PlattCertificates.Count131072.C020381
import PlattCertificates.Count131072.C020382
import PlattCertificates.Count131072.C020383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20352 : List PrefixCut := [⟨36,176374357,176374460⟩,
⟨118,582215838,582216176⟩,
⟨128,630890669,630891034⟩]
theorem checked20352 : checkPrefixCuts (2^48) 2671509505 9 Manual.Count131072.C020352.packed 128 cuts20352 = true := by
 decide +kernel
def pointBounds20352 : List (Nat × Nat × Nat) := [(2671546368,100246988941687,100247369444021),(2671630336,100247394783168,100247775285737)]
theorem point_links_checked20352 : (cuts20352.take 2).map (fun c => (2671509505-1+2*2^9*c.k,100246812567330+c.lower,100247193069561+c.upper)) = pointBounds20352 := by
 decide +kernel
def cuts20353 : List PrefixCut := [⟨72,353782539,353782747⟩,
⟨128,629174084,629174457⟩]
theorem checked20353 : checkPrefixCuts (2^48) 2671640577 9 Manual.Count131072.C020353.packed 128 cuts20353 = true := by
 decide +kernel
def pointBounds20353 : List (Nat × Nat × Nat) := [(2671714304,100247797240538,100248177743342)]
theorem point_links_checked20353 : (cuts20353.take 1).map (fun c => (2671640577-1+2*2^9*c.k,100247443457999+c.lower,100247823960595+c.upper)) = pointBounds20353 := by
 decide +kernel
def cuts20354 : List PrefixCut := [⟨26,130213690,130213764⟩,
⟨108,535384817,535385127⟩,
⟨128,633357196,633357566⟩]
theorem checked20354 : checkPrefixCuts (2^48) 2671771649 9 Manual.Count131072.C020354.packed 128 cuts20354 = true := by
 decide +kernel
def pointBounds20354 : List (Nat × Nat × Nat) := [(2671798272,100248202845773,100248583348816),(2671882240,100248608016900,100248988520179)]
theorem point_links_checked20354 : (cuts20354.take 2).map (fun c => (2671771649-1+2*2^9*c.k,100248072632083+c.lower,100248453135052+c.upper)) = pointBounds20354 := by
 decide +kernel
def cuts20355 : List PrefixCut := [⟨62,306343225,306343406⟩,
⟨128,635222164,635222537⟩]
theorem checked20355 : checkPrefixCuts (2^48) 2671902721 9 Manual.Count131072.C020355.packed 128 cuts20355 = true := by
 decide +kernel
def pointBounds20355 : List (Nat × Nat × Nat) := [(2671966208,100249012332504,100249392836024)]
theorem point_links_checked20355 : (cuts20355.take 1).map (fun c => (2671902721-1+2*2^9*c.k,100248705989279+c.lower,100249086492618+c.upper)) = pointBounds20355 := by
 decide +kernel
def cuts20356 : List PrefixCut := [⟨16,78373513,78373559⟩,
⟨98,487509224,487509507⟩,
⟨128,636560368,636560736⟩]
theorem checked20356 : checkPrefixCuts (2^48) 2672033793 9 Manual.Count131072.C020356.packed 128 cuts20356 = true := by
 decide +kernel
def pointBounds20356 : List (Nat × Nat × Nat) := [(2672050176,100249419584956,100249800088714),(2672134144,100249828720667,100250209224662)]
theorem point_links_checked20356 : (cuts20356.take 2).map (fun c => (2672033793-1+2*2^9*c.k,100249341211443+c.lower,100249721715155+c.upper)) = pointBounds20356 := by
 decide +kernel
def cuts20357 : List PrefixCut := [⟨52,258702389,258702540⟩,
⟨128,639373147,639373519⟩]
theorem checked20357 : checkPrefixCuts (2^48) 2672164865 9 Manual.Count131072.C020357.packed 128 cuts20357 = true := by
 decide +kernel
def pointBounds20357 : List (Nat × Nat × Nat) := [(2672218112,100250236474200,100250616978431)]
theorem point_links_checked20357 : (cuts20357.take 1).map (fun c => (2672164865-1+2*2^9*c.k,100249977771811+c.lower,100250358275891+c.upper)) = pointBounds20357 := by
 decide +kernel
def cuts20358 : List PrefixCut := [⟨6,27807281,27807298⟩,
⟨88,437747203,437747458⟩,
⟨128,636919384,636919752⟩]
theorem checked20358 : checkPrefixCuts (2^48) 2672295937 9 Manual.Count131072.C020358.packed 128 cuts20358 = true := by
 decide +kernel
def pointBounds20358 : List (Nat × Nat × Nat) := [(2672302080,100250644952239,100251025456708),(2672386048,100251054892161,100251435396868)]
theorem point_links_checked20358 : (cuts20358.take 2).map (fun c => (2672295937-1+2*2^9*c.k,100250617144958+c.lower,100250997649410+c.upper)) = pointBounds20358 := by
 decide +kernel
def cuts20359 : List PrefixCut := [⟨42,209174894,209175017⟩,
⟨124,616034575,616034936⟩,
⟨128,636677389,636677763⟩]
theorem checked20359 : checkPrefixCuts (2^48) 2672427009 9 Manual.Count131072.C020359.packed 128 cuts20359 = true := by
 decide +kernel
def pointBounds20359 : List (Nat × Nat × Nat) := [(2672470016,100251463239236,100251843744179),(2672553984,100251870098917,100252250604098)]
theorem point_links_checked20359 : (cuts20359.take 2).map (fun c => (2672427009-1+2*2^9*c.k,100251254064342+c.lower,100251634569162+c.upper)) = pointBounds20359 := by
 decide +kernel
def cuts20360 : List PrefixCut := [⟨78,387889214,387889439⟩,
⟨128,636014325,636014695⟩]
theorem checked20360 : checkPrefixCuts (2^48) 2672558081 9 Manual.Count131072.C020360.packed 128 cuts20360 = true := by
 decide +kernel
def pointBounds20360 : List (Nat × Nat × Nat) := [(2672637952,100252278630945,100252659136364)]
theorem point_links_checked20360 : (cuts20360.take 1).map (fun c => (2672558081-1+2*2^9*c.k,100251890741731+c.lower,100252271246925+c.upper)) = pointBounds20360 := by
 decide +kernel
def cuts20361 : List PrefixCut := [⟨32,157866570,157866662⟩,
⟨114,562476338,562476669⟩,
⟨128,629243102,629243472⟩]
theorem checked20361 : checkPrefixCuts (2^48) 2672689153 9 Manual.Count131072.C020361.packed 128 cuts20361 = true := by
 decide +kernel
def pointBounds20361 : List (Nat × Nat × Nat) := [(2672721920,100252684622626,100253065128282),(2672805888,100253089232394,100253469738289)]
theorem point_links_checked20361 : (cuts20361.take 2).map (fun c => (2672689153-1+2*2^9*c.k,100252526756056+c.lower,100252907261620+c.upper)) = pointBounds20361 := by
 decide +kernel
def cuts20362 : List PrefixCut := [⟨68,339409948,339410145⟩,
⟨128,641217270,641217642⟩]
theorem checked20362 : checkPrefixCuts (2^48) 2672820225 9 Manual.Count131072.C020362.packed 128 cuts20362 = true := by
 decide +kernel
def pointBounds20362 : List (Nat × Nat × Nat) := [(2672889856,100253495409106,100253875915237)]
theorem point_links_checked20362 : (cuts20362.take 1).map (fun c => (2672820225-1+2*2^9*c.k,100253155999158+c.lower,100253536505092+c.upper)) = pointBounds20362 := by
 decide +kernel
def cuts20363 : List PrefixCut := [⟨22,103514297,103514358⟩,
⟨104,511455754,511456056⟩,
⟨128,633498711,633499081⟩]
theorem checked20363 : checkPrefixCuts (2^48) 2672951297 9 Manual.Count131072.C020363.packed 128 cuts20363 = true := by
 decide +kernel
def pointBounds20363 : List (Nat × Nat × Nat) := [(2672973824,100253900730725,100254281237092),(2673057792,100254308672182,100254689178790)]
theorem point_links_checked20363 : (cuts20363.take 2).map (fun c => (2672951297-1+2*2^9*c.k,100253797216428+c.lower,100254177722734+c.upper)) = pointBounds20363 := by
 decide +kernel
def cuts20364 : List PrefixCut := [⟨58,290939977,290940150⟩,
⟨128,638522054,638522425⟩]
theorem checked20364 : checkPrefixCuts (2^48) 2673082369 9 Manual.Count131072.C020364.packed 128 cuts20364 = true := by
 decide +kernel
def pointBounds20364 : List (Nat × Nat × Nat) := [(2673141760,100254721655116,100255102161965)]
theorem point_links_checked20364 : (cuts20364.take 1).map (fun c => (2673082369-1+2*2^9*c.k,100254430715139+c.lower,100254811221815+c.upper)) = pointBounds20364 := by
 decide +kernel
def cuts20365 : List PrefixCut := [⟨12,59175419,59175454⟩,
⟨94,465814893,465815168⟩,
⟨128,637964226,637964602⟩]
theorem checked20365 : checkPrefixCuts (2^48) 2673213441 9 Manual.Count131072.C020365.packed 128 cuts20365 = true := by
 decide +kernel
def pointBounds20365 : List (Nat × Nat × Nat) := [(2673225728,100255128412612,100255508919694),(2673309696,100255535052086,100255915559408)]
theorem point_links_checked20365 : (cuts20365.take 2).map (fun c => (2673213441-1+2*2^9*c.k,100255069237193+c.lower,100255449744240+c.upper)) = pointBounds20365 := by
 decide +kernel
def cuts20366 : List PrefixCut := [⟨48,237004282,237004426⟩,
⟨128,629931125,629931498⟩]
theorem checked20366 : checkPrefixCuts (2^48) 2673344513 9 Manual.Count131072.C020366.packed 128 cuts20366 = true := by
 decide +kernel
def pointBounds20366 : List (Nat × Nat × Nat) := [(2673393664,100255944205701,100256324713268)]
theorem point_links_checked20366 : (cuts20366.take 1).map (fun c => (2673344513-1+2*2^9*c.k,100255707201419+c.lower,100256087708842+c.upper)) = pointBounds20366 := by
 decide +kernel
def cuts20367 : List PrefixCut := [⟨2,10002000,10002006⟩,
⟨84,412391797,412392037⟩,
⟨128,633269180,633269550⟩]
theorem checked20367 : checkPrefixCuts (2^48) 2673475585 9 Manual.Count131072.C020367.packed 128 cuts20367 = true := by
 decide +kernel
def pointBounds20367 : List (Nat × Nat × Nat) := [(2673477632,100256347134544,100256727642346),(2673561600,100256749524341,100257130032377)]
theorem point_links_checked20367 : (cuts20367.take 2).map (fun c => (2673475585-1+2*2^9*c.k,100256337132544+c.lower,100256717640340+c.upper)) = pointBounds20367 := by
 decide +kernel
def cuts20368 : List PrefixCut := [⟨38,191185459,191185569⟩,
⟨120,607867508,607867859⟩,
⟨128,647240020,647240394⟩]
theorem checked20368 : checkPrefixCuts (2^48) 2673606657 9 Manual.Count131072.C020368.packed 128 cuts20368 = true := by
 decide +kernel
def pointBounds20368 : List (Nat × Nat × Nat) := [(2673645568,100257161587183,100257542095459),(2673729536,100257578269232,100257958777749)]
theorem point_links_checked20368 : (cuts20368.take 2).map (fun c => (2673606657-1+2*2^9*c.k,100256970401724+c.lower,100257350909890+c.upper)) = pointBounds20368 := by
 decide +kernel
def cuts20369 : List PrefixCut := [⟨74,374032964,374033181⟩,
⟨128,638997201,638997577⟩]
theorem checked20369 : checkPrefixCuts (2^48) 2673737729 9 Manual.Count131072.C020369.packed 128 cuts20369 = true := by
 decide +kernel
def pointBounds20369 : List (Nat × Nat × Nat) := [(2673813504,100257991674708,100258372183465)]
theorem point_links_checked20369 : (cuts20369.take 1).map (fun c => (2673737729-1+2*2^9*c.k,100257617641744+c.lower,100257998150284+c.upper)) = pointBounds20369 := by
 decide +kernel
def cuts20370 : List PrefixCut := [⟨28,139375110,139375194⟩,
⟨110,548754609,548754934⟩,
⟨128,636755293,636755668⟩]
theorem checked20370 : checkPrefixCuts (2^48) 2673868801 9 Manual.Count131072.C020370.packed 128 cuts20370 = true := by
 decide +kernel
def pointBounds20370 : List (Nat × Nat × Nat) := [(2673897472,100258396014055,100258776523055),(2673981440,100258805393554,100259185902795)]
theorem point_links_checked20370 : (cuts20370.take 2).map (fun c => (2673868801-1+2*2^9*c.k,100258256638945+c.lower,100258637147861+c.upper)) = pointBounds20370 := by
 decide +kernel
def cuts20371 : List PrefixCut := [⟨64,320207984,320208173⟩,
⟨128,634829405,634829776⟩]
theorem checked20371 : checkPrefixCuts (2^48) 2673999873 9 Manual.Count131072.C020371.packed 128 cuts20371 = true := by
 decide +kernel
def pointBounds20371 : List (Nat × Nat × Nat) := [(2674065408,100259213602222,100259594111702)]
theorem point_links_checked20371 : (cuts20371.take 1).map (fun c => (2673999873-1+2*2^9*c.k,100258893394238+c.lower,100259273903529+c.upper)) = pointBounds20371 := by
 decide +kernel
def cuts20372 : List PrefixCut := [⟨18,91469284,91469337⟩,
⟨100,501547059,501547353⟩,
⟨128,640376897,640377268⟩]
theorem checked20372 : checkPrefixCuts (2^48) 2674130945 9 Manual.Count131072.C020372.packed 128 cuts20372 = true := by
 decide +kernel
def pointBounds20372 : List (Nat × Nat × Nat) := [(2674149376,100259619692927,100260000202642),(2674233344,100260029770702,100260410280658)]
theorem point_links_checked20372 : (cuts20372.take 2).map (fun c => (2674130945-1+2*2^9*c.k,100259528223643+c.lower,100259908733305+c.upper)) = pointBounds20372 := by
 decide +kernel
def cuts20373 : List PrefixCut := [⟨54,268603650,268603803⟩,
⟨128,634767158,634767528⟩]
theorem checked20373 : checkPrefixCuts (2^48) 2674262017 9 Manual.Count131072.C020373.packed 128 cuts20373 = true := by
 decide +kernel
def pointBounds20373 : List (Nat × Nat × Nat) := [(2674317312,100260437204190,100260817714376)]
theorem point_links_checked20373 : (cuts20373.take 1).map (fun c => (2674262017-1+2*2^9*c.k,100260168600540+c.lower,100260549110573+c.upper)) = pointBounds20373 := by
 decide +kernel
def cuts20374 : List PrefixCut := [⟨8,37994522,37994545⟩,
⟨90,450138482,450138746⟩,
⟨128,637472345,637472721⟩]
theorem checked20374 : checkPrefixCuts (2^48) 2674393089 9 Manual.Count131072.C020374.packed 128 cuts20374 = true := by
 decide +kernel
def pointBounds20374 : List (Nat × Nat × Nat) := [(2674401280,100260841362220,100261221872646),(2674485248,100261253506180,100261634016847)]
theorem point_links_checked20374 : (cuts20374.take 2).map (fun c => (2674393089-1+2*2^9*c.k,100260803367698+c.lower,100261183878101+c.upper)) = pointBounds20374 := by
 decide +kernel
def cuts20375 : List PrefixCut := [⟨44,223218483,223218609⟩,
⟨126,627969790,627970154⟩,
⟨128,636704532,636704902⟩]
theorem checked20375 : checkPrefixCuts (2^48) 2674524161 9 Manual.Count131072.C020375.packed 128 cuts20375 = true := by
 decide +kernel
def pointBounds20375 : List (Nat × Nat × Nat) := [(2674569216,100261664058526,100262044569431),(2674653184,100262068809833,100262449320976)]
theorem point_links_checked20375 : (cuts20375.take 2).map (fun c => (2674524161-1+2*2^9*c.k,100261440840043+c.lower,100261821350822+c.upper)) = pointBounds20375 := by
 decide +kernel
def cuts20376 : List PrefixCut := [⟨80,398424341,398424574⟩,
⟨128,632884832,632885204⟩]
theorem checked20376 : checkPrefixCuts (2^48) 2674655233 9 Manual.Count131072.C020376.packed 128 cuts20376 = true := by
 decide +kernel
def pointBounds20376 : List (Nat × Nat × Nat) := [(2674737152,100262475968916,100262856480298)]
theorem point_links_checked20376 : (cuts20376.take 1).map (fun c => (2674655233-1+2*2^9*c.k,100262077544575+c.lower,100262458055724+c.upper)) = pointBounds20376 := by
 decide +kernel
def cuts20377 : List PrefixCut := [⟨34,172896159,172896263⟩,
⟨116,578766910,578767249⟩,
⟨128,638010128,638010501⟩]
theorem checked20377 : checkPrefixCuts (2^48) 2674786305 9 Manual.Count131072.C020377.packed 128 cuts20377 = true := by
 decide +kernel
def pointBounds20377 : List (Nat × Nat × Nat) := [(2674821120,100262883325566,100263263837191),(2674905088,100263289196317,100263669708177)]
theorem point_links_checked20377 : (cuts20377.take 2).map (fun c => (2674786305-1+2*2^9*c.k,100262710429407+c.lower,100263090940928+c.upper)) = pointBounds20377 := by
 decide +kernel
def cuts20378 : List PrefixCut := [⟨70,345036389,345036589⟩,
⟨128,633874966,633875336⟩]
theorem checked20378 : checkPrefixCuts (2^48) 2674917377 9 Manual.Count131072.C020378.packed 128 cuts20378 = true := by
 decide +kernel
def pointBounds20378 : List (Nat × Nat × Nat) := [(2674989056,100263693475924,100264073988018)]
theorem point_links_checked20378 : (cuts20378.take 1).map (fun c => (2674917377-1+2*2^9*c.k,100263348439535+c.lower,100263728951429+c.upper)) = pointBounds20378 := by
 decide +kernel
def cuts20379 : List PrefixCut := [⟨24,117532818,117532884⟩,
⟨106,519261713,519262020⟩,
⟨128,628688060,628688431⟩]
theorem checked20379 : checkPrefixCuts (2^48) 2675048449 9 Manual.Count131072.C020379.packed 128 cuts20379 = true := by
 decide +kernel
def pointBounds20379 : List (Nat × Nat × Nat) := [(2675073024,100264099847319,100264480359649),(2675156992,100264501576214,100264882088785)]
theorem point_links_checked20379 : (cuts20379.take 2).map (fun c => (2675048449-1+2*2^9*c.k,100263982314501+c.lower,100264362826765+c.upper)) = pointBounds20379 := by
 decide +kernel
def cuts20380 : List PrefixCut := [⟨60,294394389,294394563⟩,
⟨128,627815673,627816040⟩]
theorem checked20380 : checkPrefixCuts (2^48) 2675179521 9 Manual.Count131072.C020380.packed 128 cuts20380 = true := by
 decide +kernel
def pointBounds20380 : List (Nat × Nat × Nat) := [(2675240960,100264905396950,100265285909759)]
theorem point_links_checked20380 : (cuts20380.take 1).map (fun c => (2675179521-1+2*2^9*c.k,100264611002561+c.lower,100264991515196+c.upper)) = pointBounds20380 := by
 decide +kernel
def cuts20381 : List PrefixCut := [⟨14,71964847,71964888⟩,
⟨96,480810264,480810542⟩,
⟨128,645986083,645986455⟩]
theorem checked20381 : checkPrefixCuts (2^48) 2675310593 9 Manual.Count131072.C020381.packed 128 cuts20381 = true := by
 decide +kernel
def pointBounds20381 : List (Nat × Nat × Nat) := [(2675324928,100265310783081,100265691296124),(2675408896,100265719628498,100266100141778)]
theorem point_links_checked20381 : (cuts20381.take 2).map (fun c => (2675310593-1+2*2^9*c.k,100265238818234+c.lower,100265619331236+c.upper)) = pointBounds20381 := by
 decide +kernel
def cuts20382 : List PrefixCut := [⟨50,245866143,245866288⟩,
⟨128,631225897,631226271⟩]
theorem checked20382 : checkPrefixCuts (2^48) 2675441665 9 Manual.Count131072.C020382.packed 128 cuts20382 = true := by
 decide +kernel
def pointBounds20382 : List (Nat × Nat × Nat) := [(2675492864,100266130670460,100266511183979)]
theorem point_links_checked20382 : (cuts20382.take 1).map (fun c => (2675441665-1+2*2^9*c.k,100265884804317+c.lower,100266265317691+c.upper)) = pointBounds20382 := by
 decide +kernel
def cuts20383 : List PrefixCut := [⟨4,19462306,19462318⟩,
⟨86,429742049,429742297⟩,
⟨128,640662925,640663295⟩]
theorem checked20383 : checkPrefixCuts (2^48) 2675572737 9 Manual.Count131072.C020383.packed 128 cuts20383 = true := by
 decide +kernel
def pointBounds20383 : List (Nat × Nat × Nat) := [(2675576832,100266535492520,100266916006280),(2675660800,100266945772263,100267326286259)]
theorem point_links_checked20383 : (cuts20383.take 2).map (fun c => (2675572737-1+2*2^9*c.k,100266516030214+c.lower,100266896543962+c.upper)) = pointBounds20383 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000011
