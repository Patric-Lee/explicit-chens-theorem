import PlattAssemblyKernel
import PlattCertificates.Count131072.C014320
import PlattCertificates.Count131072.C014321
import PlattCertificates.Count131072.C014322
import PlattCertificates.Count131072.C014323
import PlattCertificates.Count131072.C014324
import PlattCertificates.Count131072.C014325
import PlattCertificates.Count131072.C014326
import PlattCertificates.Count131072.C014327
import PlattCertificates.Count131072.C014328
import PlattCertificates.Count131072.C014329
import PlattCertificates.Count131072.C014330
import PlattCertificates.Count131072.C014331
import PlattCertificates.Count131072.C014332
import PlattCertificates.Count131072.C014333
import PlattCertificates.Count131072.C014334
import PlattCertificates.Count131072.C014335
import PlattCertificates.Count131072.C014336
import PlattCertificates.Count131072.C014337
import PlattCertificates.Count131072.C014338
import PlattCertificates.Count131072.C014339
import PlattCertificates.Count131072.C014340
import PlattCertificates.Count131072.C014341
import PlattCertificates.Count131072.C014342
import PlattCertificates.Count131072.C014343
import PlattCertificates.Count131072.C014344
import PlattCertificates.Count131072.C014345
import PlattCertificates.Count131072.C014346
import PlattCertificates.Count131072.C014347
import PlattCertificates.Count131072.C014348
import PlattCertificates.Count131072.C014349
import PlattCertificates.Count131072.C014350
import PlattCertificates.Count131072.C014351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000135
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14320 : List PrefixCut := [⟨4,29181792,29181811⟩,
⟨62,435774496,435774798⟩,
⟨120,855373330,855373915⟩,
⟨128,912386275,912386900⟩]
theorem checked14320 : checkPrefixCuts (2^48) 1880883201 9 Manual.Count131072.C014320.packed 128 cuts14320 = true := by
 decide +kernel
def pointBounds14320 : List (Nat × Nat × Nat) := [(1880887296,95659240201313,95659617824128),(1880946688,95659646794017,95660024417115),(1881006080,95660066392851,95660444016232)]
theorem point_links_checked14320 : (cuts14320.take 3).map (fun c => (1880883201-1+2*2^9*c.k,95659211019521+c.lower,95659588642317+c.upper)) = pointBounds14320 := by
 decide +kernel
def cuts14321 : List PrefixCut := [⟨50,369755242,369755491⟩,
⟨108,786933534,786934070⟩,
⟨128,932523859,932524492⟩]
theorem checked14321 : checkPrefixCuts (2^48) 1881014273 9 Manual.Count131072.C014321.packed 128 cuts14321 = true := by
 decide +kernel
def pointBounds14321 : List (Nat × Nat × Nat) := [(1881065472,95660493161038,95660870784708),(1881124864,95660910339330,95661287963287)]
theorem point_links_checked14321 : (cuts14321.take 2).map (fun c => (1881014273-1+2*2^9*c.k,95660123405796+c.lower,95660501029217+c.upper)) = pointBounds14321 := by
 decide +kernel
def cuts14322 : List PrefixCut := [⟨38,278308049,278308236⟩,
⟨96,693215538,693216010⟩,
⟨128,923930219,923930848⟩]
theorem checked14322 : checkPrefixCuts (2^48) 1881145345 9 Manual.Count131072.C014322.packed 128 cuts14322 = true := by
 decide +kernel
def pointBounds14322 : List (Nat × Nat × Nat) := [(1881184256,95661334237704,95661711861945),(1881243648,95661749145193,95662126769719)]
theorem point_links_checked14322 : (cuts14322.take 2).map (fun c => (1881145345-1+2*2^9*c.k,95661055929655+c.lower,95661433553709+c.upper)) = pointBounds14322 := by
 decide +kernel
def cuts14323 : List PrefixCut := [⟨26,191062239,191062371⟩,
⟨84,604746686,604747101⟩,
⟨128,912944243,912944873⟩]
theorem checked14323 : checkPrefixCuts (2^48) 1881276417 9 Manual.Count131072.C014323.packed 128 cuts14323 = true := by
 decide +kernel
def pointBounds14323 : List (Nat × Nat × Nat) := [(1881303040,95662170922113,95662548546928),(1881362432,95662584606560,95662962231658)]
theorem point_links_checked14323 : (cuts14323.take 2).map (fun c => (1881276417-1+2*2^9*c.k,95661979859874+c.lower,95662357484557+c.upper)) = pointBounds14323 := by
 decide +kernel
def cuts14324 : List PrefixCut := [⟨14,102182328,102182396⟩,
⟨72,506714784,506715133⟩,
⟨128,911084966,911085589⟩]
theorem checked14324 : checkPrefixCuts (2^48) 1881407489 9 Manual.Count131072.C014324.packed 128 cuts14324 = true := by
 decide +kernel
def pointBounds14324 : List (Nat × Nat × Nat) := [(1881421824,95662994986445,95663372611826),(1881481216,95663399518901,95663777144563)]
theorem point_links_checked14324 : (cuts14324.take 2).map (fun c => (1881407489-1+2*2^9*c.k,95662892804117+c.lower,95663270429430+c.upper)) = pointBounds14324 := by
 decide +kernel
def cuts14325 : List PrefixCut := [⟨2,14062228,14062238⟩,
⟨60,429938337,429938633⟩,
⟨118,842959076,842959656⟩,
⟨128,913115961,913116591⟩]
theorem checked14325 : checkPrefixCuts (2^48) 1881538561 9 Manual.Count131072.C014325.packed 128 cuts14325 = true := by
 decide +kernel
def pointBounds14325 : List (Nat × Nat × Nat) := [(1881540608,95663817951311,95664195577257),(1881600000,95664233827420,95664611453652),(1881659392,95664646848159,95665024474675)]
theorem point_links_checked14325 : (cuts14325.take 3).map (fun c => (1881538561-1+2*2^9*c.k,95663803889083+c.lower,95664181515019+c.upper)) = pointBounds14325 := by
 decide +kernel
def cuts14326 : List PrefixCut := [⟨48,338363258,338363491⟩,
⟨106,751806688,751807209⟩,
⟨128,910808444,910809074⟩]
theorem checked14326 : checkPrefixCuts (2^48) 1881669633 9 Manual.Count131072.C014326.packed 128 cuts14326 = true := by
 decide +kernel
def pointBounds14326 : List (Nat × Nat × Nat) := [(1881718784,95665055368302,95665432995101),(1881778176,95665468811732,95665846438819)]
theorem point_links_checked14326 : (cuts14326.take 2).map (fun c => (1881669633-1+2*2^9*c.k,95664717005044+c.lower,95665094631610+c.upper)) = pointBounds14326 := by
 decide +kernel
def cuts14327 : List PrefixCut := [⟨36,263851996,263852173⟩,
⟨94,679213768,679214233⟩,
⟨128,920168416,920169049⟩]
theorem checked14327 : checkPrefixCuts (2^48) 1881800705 9 Manual.Count131072.C014327.packed 128 cuts14327 = true := by
 decide +kernel
def pointBounds14327 : List (Nat × Nat × Nat) := [(1881837568,95665891665484,95666269292857),(1881896960,95666307027256,95666684654917)]
theorem point_links_checked14327 : (cuts14327.take 2).map (fun c => (1881800705-1+2*2^9*c.k,95665627813488+c.lower,95666005440684+c.upper)) = pointBounds14327 := by
 decide +kernel
def cuts14328 : List PrefixCut := [⟨24,175889639,175889759⟩,
⟨82,592272178,592272582⟩,
⟨128,917860957,917861586⟩]
theorem checked14328 : checkPrefixCuts (2^48) 1881931777 9 Manual.Count131072.C014328.packed 128 cuts14328 = true := by
 decide +kernel
def pointBounds14328 : List (Nat × Nat × Nat) := [(1881956352,95666723871543,95667101499492),(1882015744,95667140254082,95667517882315)]
theorem point_links_checked14328 : (cuts14328.take 2).map (fun c => (1881931777-1+2*2^9*c.k,95666547981904+c.lower,95666925609733+c.upper)) = pointBounds14328 := by
 decide +kernel
def cuts14329 : List PrefixCut := [⟨12,84947852,84947912⟩,
⟨70,504594320,504594672⟩,
⟨128,913160891,913161525⟩]
theorem checked14329 : checkPrefixCuts (2^48) 1882062849 9 Manual.Count131072.C014329.packed 128 cuts14329 = true := by
 decide +kernel
def pointBounds14329 : List (Nat × Nat × Nat) := [(1882075136,95667550790713,95667928419231),(1882134528,95667970437181,95668348065991),(1882193920,95668379003752,95668756632844)]
theorem point_links_checked14329 : (cuts14329.take 3).map (fun c => (1882062849-1+2*2^9*c.k,95667465842861+c.lower,95667843471319+c.upper)) = pointBounds14329 := by
 decide +kernel
def cuts14330 : List PrefixCut := [⟨58,410348209,410348487⟩,
⟨116,829506323,829506884⟩,
⟨128,911452185,911452804⟩]
theorem checked14330 : checkPrefixCuts (2^48) 1882193921 9 Manual.Count131072.C014330.packed 128 cuts14330 = true := by
 decide +kernel
def pointBounds14330 : List (Nat × Nat × Nat) := [(1882253312,95668789351961,95669166981331),(1882312704,95669208510075,95669586139728)]
theorem point_links_checked14330 : (cuts14330.take 2).map (fun c => (1882193921-1+2*2^9*c.k,95668379003752+c.lower,95668756632844+c.upper)) = pointBounds14330 := by
 decide +kernel
def cuts14331 : List PrefixCut := [⟨46,328526009,328526235⟩,
⟨104,744816542,744817056⟩,
⟨128,915874630,915875260⟩]
theorem checked14331 : checkPrefixCuts (2^48) 1882324993 9 Manual.Count131072.C014331.packed 128 cuts14331 = true := by
 decide +kernel
def pointBounds14331 : List (Nat × Nat × Nat) := [(1882372096,95669618981946,95669996611883),(1882431488,95670035272479,95670412902704)]
theorem point_links_checked14331 : (cuts14331.take 2).map (fun c => (1882324993-1+2*2^9*c.k,95669290455937+c.lower,95669668085648+c.upper)) = pointBounds14331 := by
 decide +kernel
def cuts14332 : List PrefixCut := [⟨34,245069729,245069896⟩,
⟨92,648923800,648924248⟩,
⟨128,908932848,908933472⟩]
theorem checked14332 : checkPrefixCuts (2^48) 1882456065 9 Manual.Count131072.C014332.packed 128 cuts14332 = true := by
 decide +kernel
def pointBounds14332 : List (Nat × Nat × Nat) := [(1882490880,95670451400296,95670829030804),(1882550272,95670855254367,95671232885156)]
theorem point_links_checked14332 : (cuts14332.take 2).map (fun c => (1882456065-1+2*2^9*c.k,95670206330567+c.lower,95670583960908+c.upper)) = pointBounds14332 := by
 decide +kernel
def cuts14333 : List PrefixCut := [⟨22,154747003,154747112⟩,
⟨80,575769390,575769790⟩,
⟨128,919634241,919634875⟩]
theorem checked14333 : checkPrefixCuts (2^48) 1882587137 9 Manual.Count131072.C014333.packed 128 cuts14333 = true := by
 decide +kernel
def pointBounds14333 : List (Nat × Nat × Nat) := [(1882609664,95671270010418,95671647641492),(1882669056,95671691032805,95672068664170)]
theorem point_links_checked14333 : (cuts14333.take 2).map (fun c => (1882587137-1+2*2^9*c.k,95671115263415+c.lower,95671492894380+c.upper)) = pointBounds14333 := by
 decide +kernel
def cuts14334 : List PrefixCut := [⟨10,71761979,71762027⟩,
⟨68,493804295,493804623⟩,
⟨126,907909895,907910499⟩,
⟨128,923158303,923158917⟩]
theorem checked14334 : checkPrefixCuts (2^48) 1882718209 9 Manual.Count131072.C014334.packed 128 cuts14334 = true := by
 decide +kernel
def pointBounds14334 : List (Nat × Nat × Nat) := [(1882728448,95672106659635,95672484291282),(1882787840,95672528701951,95672906333878),(1882847232,95672942807551,95673320439754)]
theorem point_links_checked14334 : (cuts14334.take 3).map (fun c => (1882718209-1+2*2^9*c.k,95672034897656+c.lower,95672412529255+c.upper)) = pointBounds14334 := by
 decide +kernel
def cuts14335 : List PrefixCut := [⟨56,402282427,402282702⟩,
⟨114,813372229,813372787⟩,
⟨128,919356570,919357199⟩]
theorem checked14335 : checkPrefixCuts (2^48) 1882849281 9 Manual.Count131072.C014335.packed 128 cuts14335 = true := by
 decide +kernel
def pointBounds14335 : List (Nat × Nat × Nat) := [(1882906624,95673360338386,95673737970874),(1882966016,95673771428188,95674149060959)]
theorem point_links_checked14335 : (cuts14335.take 2).map (fun c => (1882849281-1+2*2^9*c.k,95672958055959+c.lower,95673335688172+c.upper)) = pointBounds14335 := by
 decide +kernel
def cuts14336 : List PrefixCut := [⟨44,319293302,319293514⟩,
⟨102,731702453,731702945⟩,
⟨128,916901169,916901786⟩]
theorem checked14336 : checkPrefixCuts (2^48) 1882980353 9 Manual.Count131072.C014336.packed 128 cuts14336 = true := by
 decide +kernel
def pointBounds14336 : List (Nat × Nat × Nat) := [(1883025408,95674196705831,95674574338885),(1883084800,95674609114982,95674986748316)]
theorem point_links_checked14336 : (cuts14336.take 2).map (fun c => (1882980353-1+2*2^9*c.k,95673877412529+c.lower,95674255045371+c.upper)) = pointBounds14336 := by
 decide +kernel
def cuts14337 : List PrefixCut := [⟨32,237361540,237361699⟩,
⟨90,669026066,669026512⟩,
⟨128,938659913,938660541⟩]
theorem checked14337 : checkPrefixCuts (2^48) 1883111425 9 Manual.Count131072.C014337.packed 128 cuts14337 = true := by
 decide +kernel
def pointBounds14337 : List (Nat × Nat × Nat) := [(1883144192,95675031675238,95675409308856),(1883203584,95675463339764,95675840973669)]
theorem point_links_checked14337 : (cuts14337.take 2).map (fun c => (1883111425-1+2*2^9*c.k,95674794313698+c.lower,95675171947157+c.upper)) = pointBounds14337 := by
 decide +kernel
def cuts14338 : List PrefixCut := [⟨20,145426589,145426690⟩,
⟨78,564808334,564808720⟩,
⟨128,917371550,917372181⟩]
theorem checked14338 : checkPrefixCuts (2^48) 1883242497 9 Manual.Count131072.C014338.packed 128 cuts14338 = true := by
 decide +kernel
def pointBounds14338 : List (Nat × Nat × Nat) := [(1883262976,95675878400200,95676256034388),(1883322368,95676297781945,95676675416418)]
theorem point_links_checked14338 : (cuts14338.take 2).map (fun c => (1883242497-1+2*2^9*c.k,95675732973611+c.lower,95676110607698+c.upper)) = pointBounds14338 := by
 decide +kernel
def cuts14339 : List PrefixCut := [⟨8,60528131,60528171⟩,
⟨66,471215268,471215591⟩,
⟨124,883981732,883982337⟩,
⟨128,913421859,913422484⟩]
theorem checked14339 : checkPrefixCuts (2^48) 1883373569 9 Manual.Count131072.C014339.packed 128 cuts14339 = true := by
 decide +kernel
def pointBounds14339 : List (Nat × Nat × Nat) := [(1883381760,95676710873292,95677088508050),(1883441152,95677121560429,95677499195470),(1883500544,95677534326893,95677911962216)]
theorem point_links_checked14339 : (cuts14339.take 3).map (fun c => (1883373569-1+2*2^9*c.k,95676650345161+c.lower,95677027979879+c.upper)) = pointBounds14339 := by
 decide +kernel
def cuts14340 : List PrefixCut := [⟨54,382416721,382416985⟩,
⟨112,800088493,800089043⟩,
⟨128,911714448,911715076⟩]
theorem checked14340 : checkPrefixCuts (2^48) 1883504641 9 Manual.Count131072.C014340.packed 128 cuts14340 = true := by
 decide +kernel
def pointBounds14340 : List (Nat × Nat × Nat) := [(1883559936,95677946183741,95678323819348),(1883619328,95678363855513,95678741491406)]
theorem point_links_checked14340 : (cuts14340.take 2).map (fun c => (1883504641-1+2*2^9*c.k,95677563767020+c.lower,95677941402363+c.upper)) = pointBounds14340 := by
 decide +kernel
def cuts14341 : List PrefixCut := [⟨42,298860021,298860225⟩,
⟨100,711723757,711724242⟩,
⟨128,910007322,910007945⟩]
theorem checked14341 : checkPrefixCuts (2^48) 1883635713 9 Manual.Count131072.C014341.packed 128 cuts14341 = true := by
 decide +kernel
def pointBounds14341 : List (Nat × Nat × Nat) := [(1883678720,95678774341489,95679151977664),(1883738112,95679187205225,95679564841681)]
theorem point_links_checked14341 : (cuts14341.take 2).map (fun c => (1883635713-1+2*2^9*c.k,95678475481468+c.lower,95678853117439+c.upper)) = pointBounds14341 := by
 decide +kernel
def cuts14342 : List PrefixCut := [⟨30,213820136,213820283⟩,
⟨88,622922497,622922927⟩,
⟨128,908300429,908301052⟩]
theorem checked14342 : checkPrefixCuts (2^48) 1883766785 9 Manual.Count131072.C014342.packed 128 cuts14342 = true := by
 decide +kernel
def pointBounds14342 : List (Nat × Nat × Nat) := [(1883797504,95679599308926,95679976945667),(1883856896,95680008411287,95680386048311)]
theorem point_links_checked14342 : (cuts14342.take 2).map (fun c => (1883766785-1+2*2^9*c.k,95679385488790+c.lower,95679763125384+c.upper)) = pointBounds14342 := by
 decide +kernel
def cuts14343 : List PrefixCut := [⟨18,137606781,137606872⟩,
⟨76,553854981,553855356⟩,
⟨128,923925334,923925959⟩]
theorem checked14343 : checkPrefixCuts (2^48) 1883897857 9 Manual.Count131072.C014343.packed 128 cuts14343 = true := by
 decide +kernel
def pointBounds14343 : List (Nat × Nat × Nat) := [(1883916288,95680431396000,95680809033308),(1883975680,95680847644200,95681225281792)]
theorem point_links_checked14343 : (cuts14343.take 2).map (fun c => (1883897857-1+2*2^9*c.k,95680293789219+c.lower,95680671426436+c.upper)) = pointBounds14343 := by
 decide +kernel
def cuts14344 : List PrefixCut := [⟨6,42429680,42429709⟩,
⟨64,454468518,454468824⟩,
⟨122,875906075,875906671⟩,
⟨128,915942691,915943315⟩]
theorem checked14344 : checkPrefixCuts (2^48) 1884028929 9 Manual.Count131072.C014344.packed 128 cuts14344 = true := by
 decide +kernel
def pointBounds14344 : List (Nat × Nat × Nat) := [(1884035072,95681260144233,95681637782104),(1884094464,95681672183071,95682049821219),(1884153856,95682093620628,95682471259066)]
theorem point_links_checked14344 : (cuts14344.take 3).map (fun c => (1884028929-1+2*2^9*c.k,95681217714553+c.lower,95681595352395+c.upper)) = pointBounds14344 := by
 decide +kernel
def cuts14345 : List PrefixCut := [⟨52,373768807,373769059⟩,
⟨110,786515535,786516071⟩,
⟨128,917522178,917522802⟩]
theorem checked14345 : checkPrefixCuts (2^48) 1884160001 9 Manual.Count131072.C014345.packed 128 cuts14345 = true := by
 decide +kernel
def pointBounds14345 : List (Nat × Nat × Nat) := [(1884213248,95682507426051,95682885064769),(1884272640,95682920172779,95683297811781)]
theorem point_links_checked14345 : (cuts14345.take 2).map (fun c => (1884160001-1+2*2^9*c.k,95682133657244+c.lower,95682511295710+c.upper)) = pointBounds14345 := by
 decide +kernel
def cuts14346 : List PrefixCut := [⟨40,282324601,282324796⟩,
⟨98,689817216,689817692⟩,
⟨128,903267729,903268357⟩]
theorem checked14346 : checkPrefixCuts (2^48) 1884291073 9 Manual.Count131072.C014346.packed 128 cuts14346 = true := by
 decide +kernel
def pointBounds14346 : List (Nat × Nat × Nat) := [(1884332032,95683333504023,95683711143308),(1884391424,95683740996638,95684118636204)]
theorem point_links_checked14346 : (cuts14346.take 2).map (fun c => (1884291073-1+2*2^9*c.k,95683051179422+c.lower,95683428818512+c.upper)) = pointBounds14346 := by
 decide +kernel
def cuts14347 : List PrefixCut := [⟨28,199705298,199705437⟩,
⟨86,609113946,609114366⟩,
⟨128,906042934,906043557⟩]
theorem checked14347 : checkPrefixCuts (2^48) 1884422145 9 Manual.Count131072.C014347.packed 128 cuts14347 = true := by
 decide +kernel
def pointBounds14347 : List (Nat × Nat × Nat) := [(1884450816,95684154152449,95684531792306),(1884510208,95684563561097,95684941201235)]
theorem point_links_checked14347 : (cuts14347.take 2).map (fun c => (1884422145-1+2*2^9*c.k,95683954447151+c.lower,95684332086869+c.upper)) = pointBounds14347 := by
 decide +kernel
def cuts14348 : List PrefixCut := [⟨16,114259099,114259177⟩,
⟨74,528570660,528571023⟩,
⟨128,915538460,915539087⟩]
theorem checked14348 : checkPrefixCuts (2^48) 1884553217 9 Manual.Count131072.C014348.packed 128 cuts14348 = true := by
 decide +kernel
def pointBounds14348 : List (Nat × Nat × Nat) := [(1884569600,95684974749184,95685352389603),(1884628992,95685389060745,95685766701449)]
theorem point_links_checked14348 : (cuts14348.take 2).map (fun c => (1884553217-1+2*2^9*c.k,95684860490085+c.lower,95685238130426+c.upper)) = pointBounds14348 := by
 decide +kernel
def cuts14349 : List PrefixCut := [⟨4,29421636,29421655⟩,
⟨62,435941135,435941433⟩,
⟨120,849018913,849019492⟩,
⟨128,910845051,910845672⟩]
theorem checked14349 : checkPrefixCuts (2^48) 1884684289 9 Manual.Count131072.C014349.packed 128 cuts14349 = true := by
 decide +kernel
def pointBounds14349 : List (Nat × Nat × Nat) := [(1884688384,95685805450181,95686183091168),(1884747776,95686211969680,95686589610946),(1884807168,95686625047458,95687002689005)]
theorem point_links_checked14349 : (cuts14349.take 3).map (fun c => (1884684289-1+2*2^9*c.k,95685776028545+c.lower,95686153669513+c.upper)) = pointBounds14349 := by
 decide +kernel
def cuts14350 : List PrefixCut := [⟨50,357809437,357809678⟩,
⟨108,785196991,785197523⟩,
⟨128,930792369,930793000⟩]
theorem checked14350 : checkPrefixCuts (2^48) 1884815361 9 Manual.Count131072.C014350.packed 128 cuts14350 = true := by
 decide +kernel
def pointBounds14350 : List (Nat × Nat × Nat) := [(1884866560,95687044683033,95687422324863),(1884925952,95687472070587,95687849712708)]
theorem point_links_checked14350 : (cuts14350.take 2).map (fun c => (1884815361-1+2*2^9*c.k,95686686873596+c.lower,95687064515185+c.upper)) = pointBounds14350 := by
 decide +kernel
def cuts14351 : List PrefixCut := [⟨38,268040637,268040821⟩,
⟨96,680469029,680469497⟩,
⟨128,910718482,910719103⟩]
theorem checked14351 : checkPrefixCuts (2^48) 1884946433 9 Manual.Count131072.C014351.packed 128 cuts14351 = true := by
 decide +kernel
def pointBounds14351 : List (Nat × Nat × Nat) := [(1884985344,95687885706602,95688263349006),(1885044736,95688298134994,95688675777682)]
theorem point_links_checked14351 : (cuts14351.take 2).map (fun c => (1884946433-1+2*2^9*c.k,95687617665965+c.lower,95687995308185+c.upper)) = pointBounds14351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000135
