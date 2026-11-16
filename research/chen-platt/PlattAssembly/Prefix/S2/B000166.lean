import PlattAssemblyKernel
import PlattCertificates.Count131072.C015312
import PlattCertificates.Count131072.C015313
import PlattCertificates.Count131072.C015314
import PlattCertificates.Count131072.C015315
import PlattCertificates.Count131072.C015316
import PlattCertificates.Count131072.C015317
import PlattCertificates.Count131072.C015318
import PlattCertificates.Count131072.C015319
import PlattCertificates.Count131072.C015320
import PlattCertificates.Count131072.C015321
import PlattCertificates.Count131072.C015322
import PlattCertificates.Count131072.C015323
import PlattCertificates.Count131072.C015324
import PlattCertificates.Count131072.C015325
import PlattCertificates.Count131072.C015326
import PlattCertificates.Count131072.C015327
import PlattCertificates.Count131072.C015328
import PlattCertificates.Count131072.C015329
import PlattCertificates.Count131072.C015330
import PlattCertificates.Count131072.C015331
import PlattCertificates.Count131072.C015332
import PlattCertificates.Count131072.C015333
import PlattCertificates.Count131072.C015334
import PlattCertificates.Count131072.C015335
import PlattCertificates.Count131072.C015336
import PlattCertificates.Count131072.C015337
import PlattCertificates.Count131072.C015338
import PlattCertificates.Count131072.C015339
import PlattCertificates.Count131072.C015340
import PlattCertificates.Count131072.C015341
import PlattCertificates.Count131072.C015342
import PlattCertificates.Count131072.C015343
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000166
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15312 : List PrefixCut := [⟨46,301920680,301920881⟩,
⟨108,720146954,720147427⟩,
⟨128,847095838,847096398⟩]
theorem checked15312 : checkPrefixCuts (2^48) 2010906625 9 Manual.Count131072.C015312.packed 128 cuts15312 = true := by
 decide +kernel
def pointBounds15312 : List (Nat × Nat × Nat) := [(2010953728,96539232005849,96539610218921),(2011017216,96539650232123,96540028445467)]
theorem point_links_checked15312 : (cuts15312.take 2).map (fun c => (2010906625-1+2*2^9*c.k,96538930085169+c.lower,96539308298040+c.upper)) = pointBounds15312 := by
 decide +kernel
def cuts15313 : List PrefixCut := [⟨42,281746528,281746713⟩,
⟨104,698546764,698547221⟩,
⟨128,854038687,854039250⟩]
theorem checked15313 : checkPrefixCuts (2^48) 2011037697 9 Manual.Count131072.C015313.packed 128 cuts15313 = true := by
 decide +kernel
def pointBounds15313 : List (Nat × Nat × Nat) := [(2011080704,96540058927535,96540437141151),(2011144192,96540475727771,96540853941659)]
theorem point_links_checked15313 : (cuts15313.take 2).map (fun c => (2011037697-1+2*2^9*c.k,96539777181007+c.lower,96540155394438+c.upper)) = pointBounds15313 := by
 decide +kernel
def cuts15314 : List PrefixCut := [⟨38,248139366,248139532⟩,
⟨100,665193178,665193618⟩,
⟨128,858321066,858321630⟩]
theorem checked15314 : checkPrefixCuts (2^48) 2011168769 9 Manual.Count131072.C015314.packed 128 cuts15314 = true := by
 decide +kernel
def pointBounds15314 : List (Nat × Nat × Nat) := [(2011207680,96540879359060,96541257573220),(2011271168,96541296412872,96541674627306)]
theorem point_links_checked15314 : (cuts15314.take 2).map (fun c => (2011168769-1+2*2^9*c.k,96540631219694+c.lower,96541009433688+c.upper)) = pointBounds15314 := by
 decide +kernel
def cuts15315 : List PrefixCut := [⟨34,229510632,229510782⟩,
⟨96,652695576,652696010⟩,
⟨128,864003123,864003698⟩]
theorem checked15315 : checkPrefixCuts (2^48) 2011299841 9 Manual.Count131072.C015315.packed 128 cuts15315 = true := by
 decide +kernel
def pointBounds15315 : List (Nat × Nat × Nat) := [(2011334656,96541719051392,96542097266100),(2011398144,96542142236336,96542520451328)]
theorem point_links_checked15315 : (cuts15315.take 2).map (fun c => (2011299841-1+2*2^9*c.k,96541489540760+c.lower,96541867755318+c.upper)) = pointBounds15315 := by
 decide +kernel
def cuts15316 : List PrefixCut := [⟨30,197590428,197590557⟩,
⟨92,607315111,607315510⟩,
⟨128,851632540,851633101⟩]
theorem checked15316 : checkPrefixCuts (2^48) 2011430913 9 Manual.Count131072.C015316.packed 128 cuts15316 = true := by
 decide +kernel
def pointBounds15316 : List (Nat × Nat × Nat) := [(2011461632,96542551134311,96542929349573),(2011525120,96542960858994,96543339074526)]
theorem point_links_checked15316 : (cuts15316.take 2).map (fun c => (2011430913-1+2*2^9*c.k,96542353543883+c.lower,96542731759016+c.upper)) = pointBounds15316 := by
 decide +kernel
def cuts15317 : List PrefixCut := [⟨26,175609143,175609258⟩,
⟨88,588806022,588806403⟩,
⟨128,853816097,853816650⟩]
theorem checked15317 : checkPrefixCuts (2^48) 2011561985 9 Manual.Count131072.C015317.packed 128 cuts15317 = true := by
 decide +kernel
def pointBounds15317 : List (Nat × Nat × Nat) := [(2011588608,96543380785566,96543759001375),(2011652096,96543793982445,96544172198520)]
theorem point_links_checked15317 : (cuts15317.take 2).map (fun c => (2011561985-1+2*2^9*c.k,96543205176423+c.lower,96543583392117+c.upper)) = pointBounds15317 := by
 decide +kernel
def cuts15318 : List PrefixCut := [⟨22,147614141,147614239⟩,
⟨84,562323962,562324333⟩,
⟨128,861875261,861875825⟩]
theorem checked15318 : checkPrefixCuts (2^48) 2011693057 9 Manual.Count131072.C015318.packed 128 cuts15318 = true := by
 decide +kernel
def pointBounds15318 : List (Nat × Nat × Nat) := [(2011715584,96544206606661,96544584823006),(2011779072,96544621316482,96544999533100)]
theorem point_links_checked15318 : (cuts15318.take 2).map (fun c => (2011693057-1+2*2^9*c.k,96544058992520+c.lower,96544437208767+c.upper)) = pointBounds15318 := by
 decide +kernel
def cuts15319 : List PrefixCut := [⟨18,119622733,119622810⟩,
⟨80,530109334,530109680⟩,
⟨128,853704688,853705246⟩]
theorem checked15319 : checkPrefixCuts (2^48) 2011824129 9 Manual.Count131072.C015319.packed 128 cuts15319 = true := by
 decide +kernel
def pointBounds15319 : List (Nat × Nat × Nat) := [(2011842560,96545040490514,96545418707402),(2011906048,96545450977115,96545829194272)]
theorem point_links_checked15319 : (cuts15319.take 2).map (fun c => (2011824129-1+2*2^9*c.k,96544920867781+c.lower,96545299084592+c.upper)) = pointBounds15319 := by
 decide +kernel
def cuts15320 : List PrefixCut := [⟨14,94992550,94992612⟩,
⟨76,520562175,520562519⟩,
⟨128,873234699,873235283⟩]
theorem checked15320 : checkPrefixCuts (2^48) 2011955201 9 Manual.Count131072.C015320.packed 128 cuts15320 = true := by
 decide +kernel
def pointBounds15320 : List (Nat × Nat × Nat) := [(2011969536,96545869565019,96546247782450),(2012033024,96546295134644,96546673352357)]
theorem point_links_checked15320 : (cuts15320.take 2).map (fun c => (2011955201-1+2*2^9*c.k,96545774572469+c.lower,96546152789838+c.upper)) = pointBounds15320 := by
 decide +kernel
def cuts15321 : List PrefixCut := [⟨10,71204878,71204925⟩,
⟨72,481499652,481499971⟩,
⟨128,854852548,854853114⟩]
theorem checked15321 : checkPrefixCuts (2^48) 2012086273 9 Manual.Count131072.C015321.packed 128 cuts15321 = true := by
 decide +kernel
def pointBounds15321 : List (Nat × Nat × Nat) := [(2012096512,96546719012046,96547097230046),(2012160000,96547129306820,96547507525092)]
theorem point_links_checked15321 : (cuts15321.take 2).map (fun c => (2012086273-1+2*2^9*c.k,96546647807168+c.lower,96547026025121+c.upper)) = pointBounds15321 := by
 decide +kernel
def cuts15322 : List PrefixCut := [⟨6,39307048,39307073⟩,
⟨68,452373617,452373920⟩,
⟨128,850600399,850600964⟩]
theorem checked15322 : checkPrefixCuts (2^48) 2012217345 9 Manual.Count131072.C015322.packed 128 cuts15322 = true := by
 decide +kernel
def pointBounds15322 : List (Nat × Nat × Nat) := [(2012223488,96547541966764,96547920185308),(2012286976,96547955033333,96548333252155)]
theorem point_links_checked15322 : (cuts15322.take 2).map (fun c => (2012217345-1+2*2^9*c.k,96547502659716+c.lower,96547880878235+c.upper)) = pointBounds15322 := by
 decide +kernel
def cuts15323 : List PrefixCut := [⟨2,11329775,11329782⟩,
⟨64,427027799,427028082⟩,
⟨126,838237028,838237577⟩,
⟨128,851524184,851524741⟩]
theorem checked15323 : checkPrefixCuts (2^48) 2012348417 9 Manual.Count131072.C015323.packed 128 cuts15323 = true := by
 decide +kernel
def pointBounds15323 : List (Nat × Nat × Nat) := [(2012350464,96548364589890,96548742808981),(2012413952,96548780287914,96549158507281),(2012477440,96549191497143,96549569716776)]
theorem point_links_checked15323 : (cuts15323.take 3).map (fun c => (2012348417-1+2*2^9*c.k,96548353260115+c.lower,96548731479199+c.upper)) = pointBounds15323 := by
 decide +kernel
def cuts15324 : List PrefixCut := [⟨60,392734126,392734382⟩,
⟨122,804896403,804896931⟩,
⟨128,843356755,843357308⟩]
theorem checked15324 : checkPrefixCuts (2^48) 2012479489 9 Manual.Count131072.C015324.packed 128 cuts15324 = true := by
 decide +kernel
def pointBounds15324 : List (Nat × Nat × Nat) := [(2012540928,96549597518425,96549975738322),(2012604416,96550009680702,96550387900871)]
theorem point_links_checked15324 : (cuts15324.take 2).map (fun c => (2012479489-1+2*2^9*c.k,96549204784299+c.lower,96549583003940+c.upper)) = pointBounds15324 := by
 decide +kernel
def cuts15325 : List PrefixCut := [⟨56,386275679,386275931⟩,
⟨118,806383392,806383918⟩,
⟨128,874488814,874489387⟩]
theorem checked15325 : checkPrefixCuts (2^48) 2012610561 9 Manual.Count131072.C015325.packed 128 cuts15325 = true := by
 decide +kernel
def pointBounds15325 : List (Nat × Nat × Nat) := [(2012667904,96550434416733,96550812637179),(2012731392,96550854524446,96551232745166)]
theorem point_links_checked15325 : (cuts15325.take 2).map (fun c => (2012610561-1+2*2^9*c.k,96550048141054+c.lower,96550426361248+c.upper)) = pointBounds15325 := by
 decide +kernel
def cuts15326 : List PrefixCut := [⟨52,353667125,353667360⟩,
⟨114,763260333,763260838⟩,
⟨128,855972855,855973420⟩]
theorem checked15326 : checkPrefixCuts (2^48) 2012741633 9 Manual.Count131072.C015326.packed 128 cuts15326 = true := by
 decide +kernel
def pointBounds15326 : List (Nat × Nat × Nat) := [(2012794880,96551276296993,96551654517995),(2012858368,96551685890201,96552064111473)]
theorem point_links_checked15326 : (cuts15326.take 2).map (fun c => (2012741633-1+2*2^9*c.k,96550922629868+c.lower,96551300850635+c.upper)) = pointBounds15326 := by
 decide +kernel
def cuts15327 : List PrefixCut := [⟨48,320363604,320363813⟩,
⟨110,737621723,737622204⟩,
⟨128,861090666,861091228⟩]
theorem checked15327 : checkPrefixCuts (2^48) 2012872705 9 Manual.Count131072.C015327.packed 128 cuts15327 = true := by
 decide +kernel
def pointBounds15327 : List (Nat × Nat × Nat) := [(2012921856,96552098966327,96552477187868),(2012985344,96552516224446,96552894446259)]
theorem point_links_checked15327 : (cuts15327.take 2).map (fun c => (2012872705-1+2*2^9*c.k,96551778602723+c.lower,96552156824055+c.upper)) = pointBounds15327 := by
 decide +kernel
def cuts15328 : List PrefixCut := [⟨44,289860817,289861009⟩,
⟨106,703876457,703876927⟩,
⟨128,850687419,850687985⟩]
theorem checked15328 : checkPrefixCuts (2^48) 2013003777 9 Manual.Count131072.C015328.packed 128 cuts15328 = true := by
 decide +kernel
def pointBounds15328 : List (Nat × Nat × Nat) := [(2013048832,96552929554206,96553307776292),(2013112320,96553343569846,96553721792210)]
theorem point_links_checked15328 : (cuts15328.take 2).map (fun c => (2013003777-1+2*2^9*c.k,96552639693389+c.lower,96553017915283+c.upper)) = pointBounds15328 := by
 decide +kernel
def cuts15329 : List PrefixCut := [⟨40,274182655,274182832⟩,
⟨102,694603751,694604205⟩,
⟨128,867410126,867410695⟩]
theorem checked15329 : checkPrefixCuts (2^48) 2013134849 9 Manual.Count131072.C015329.packed 128 cuts15329 = true := by
 decide +kernel
def pointBounds15329 : List (Nat × Nat × Nat) := [(2013175808,96553764563463,96554142786100),(2013239296,96554184984559,96554563207473)]
theorem point_links_checked15329 : (cuts15329.take 2).map (fun c => (2013134849-1+2*2^9*c.k,96553490380808+c.lower,96553868603268+c.upper)) = pointBounds15329 := by
 decide +kernel
def cuts15330 : List PrefixCut := [⟨36,241729407,241729565⟩,
⟨98,657091068,657091494⟩,
⟨128,858126406,858126963⟩]
theorem checked15330 : checkPrefixCuts (2^48) 2013265921 9 Manual.Count131072.C015330.packed 128 cuts15330 = true := by
 decide +kernel
def pointBounds15330 : List (Nat × Nat × Nat) := [(2013302784,96554599520341,96554977743528),(2013366272,96555014882002,96555393105457)]
theorem point_links_checked15330 : (cuts15330.take 2).map (fun c => (2013265921-1+2*2^9*c.k,96554357790934+c.lower,96554736013963+c.upper)) = pointBounds15330 := by
 decide +kernel
def cuts15331 : List PrefixCut := [⟨32,218786763,218786904⟩,
⟨94,636219094,636219513⟩,
⟨128,861705374,861705942⟩]
theorem checked15331 : checkPrefixCuts (2^48) 2013396993 9 Manual.Count131072.C015331.packed 128 cuts15331 = true := by
 decide +kernel
def pointBounds15331 : List (Nat × Nat × Nat) := [(2013429760,96555434704103,96555812927830),(2013493248,96555852136434,96556230360439)]
theorem point_links_checked15331 : (cuts15331.take 2).map (fun c => (2013396993-1+2*2^9*c.k,96555215917340+c.lower,96555594140926+c.upper)) = pointBounds15331 := by
 decide +kernel
def cuts15332 : List PrefixCut := [⟨28,190115630,190115753⟩,
⟨90,612833629,612834030⟩,
⟨128,862348298,862348865⟩]
theorem checked15332 : checkPrefixCuts (2^48) 2013528065 9 Manual.Count131072.C015332.packed 128 cuts15332 = true := by
 decide +kernel
def pointBounds15332 : List (Nat × Nat × Nat) := [(2013556736,96556267738344,96556645962621),(2013620224,96556690456343,96557068680898)]
theorem point_links_checked15332 : (cuts15332.take 2).map (fun c => (2013528065-1+2*2^9*c.k,96556077622714+c.lower,96556455846868+c.upper)) = pointBounds15332 := by
 decide +kernel
def cuts15333 : List PrefixCut := [⟨24,162706152,162706261⟩,
⟨86,580505269,580505650⟩,
⟨128,866485349,866485914⟩]
theorem checked15333 : checkPrefixCuts (2^48) 2013659137 9 Manual.Count131072.C015333.packed 128 cuts15333 = true := by
 decide +kernel
def pointBounds15333 : List (Nat × Nat × Nat) := [(2013683712,96557102677164,96557480901994),(2013747200,96557520476281,96557898701383)]
theorem point_links_checked15333 : (cuts15333.take 2).map (fun c => (2013659137-1+2*2^9*c.k,96556939971012+c.lower,96557318195733+c.upper)) = pointBounds15333 := by
 decide +kernel
def cuts15334 : List PrefixCut := [⟨20,135719543,135719631⟩,
⟨82,552094539,552094900⟩,
⟨128,854408897,854409459⟩]
theorem checked15334 : checkPrefixCuts (2^48) 2013790209 9 Manual.Count131072.C015334.packed 128 cuts15334 = true := by
 decide +kernel
def pointBounds15334 : List (Nat × Nat × Nat) := [(2013810688,96557942175904,96558320401278),(2013874176,96558358550900,96558736776547)]
theorem point_links_checked15334 : (cuts15334.take 2).map (fun c => (2013790209-1+2*2^9*c.k,96557806456361+c.lower,96558184681647+c.upper)) = pointBounds15334 := by
 decide +kernel
def cuts15335 : List PrefixCut := [⟨16,105801369,105801438⟩,
⟨78,520752502,520752844⟩,
⟨128,861201176,861201737⟩]
theorem checked15335 : checkPrefixCuts (2^48) 2013921281 9 Manual.Count131072.C015335.packed 128 cuts15335 = true := by
 decide +kernel
def pointBounds15335 : List (Nat × Nat × Nat) := [(2013937664,96558766666627,96559144892544),(2014001152,96559181617760,96559559843950)]
theorem point_links_checked15335 : (cuts15335.take 2).map (fun c => (2013921281-1+2*2^9*c.k,96558660865258+c.lower,96559039091106+c.upper)) = pointBounds15335 := by
 decide +kernel
def cuts15336 : List PrefixCut := [⟨12,83154262,83154317⟩,
⟨74,498358761,498359089⟩,
⟨128,856673461,856674027⟩]
theorem checked15336 : checkPrefixCuts (2^48) 2014052353 9 Manual.Count131072.C015336.packed 128 cuts15336 = true := by
 decide +kernel
def pointBounds15336 : List (Nat × Nat × Nat) := [(2014064640,96559605220696,96559983447160),(2014128128,96560020425195,96560398651932)]
theorem point_links_checked15336 : (cuts15336.take 2).map (fun c => (2014052353-1+2*2^9*c.k,96559522066434+c.lower,96559900292843+c.upper)) = pointBounds15336 := by
 decide +kernel
def cuts15337 : List PrefixCut := [⟨8,53802256,53802291⟩,
⟨70,468840915,468841220⟩,
⟨128,857036879,857037443⟩]
theorem checked15337 : checkPrefixCuts (2^48) 2014183425 9 Manual.Count131072.C015337.packed 128 cuts15337 = true := by
 decide +kernel
def pointBounds15337 : List (Nat × Nat × Nat) := [(2014191616,96560432542151,96560810769161),(2014255104,96560847580810,96561225808090)]
theorem point_links_checked15337 : (cuts15337.take 2).map (fun c => (2014183425-1+2*2^9*c.k,96560378739895+c.lower,96560756966870+c.upper)) = pointBounds15337 := by
 decide +kernel
def cuts15338 : List PrefixCut := [⟨4,25571902,25571919⟩,
⟨66,440304866,440305155⟩,
⟨128,848038156,848038718⟩]
theorem checked15338 : checkPrefixCuts (2^48) 2014314497 9 Manual.Count131072.C015338.packed 128 cuts15338 = true := by
 decide +kernel
def pointBounds15338 : List (Nat × Nat × Nat) := [(2014318592,96561261348676,96561639576232),(2014382080,96561676081640,96562054309468),(2014445568,96562083814930,96562462043031)]
theorem point_links_checked15338 : (cuts15338.take 3).map (fun c => (2014314497-1+2*2^9*c.k,96561235776774+c.lower,96561614004313+c.upper)) = pointBounds15338 := by
 decide +kernel
def cuts15339 : List PrefixCut := [⟨62,417641074,417641353⟩,
⟨124,834290932,834291485⟩,
⟨128,860977312,860977883⟩]
theorem checked15339 : checkPrefixCuts (2^48) 2014445569 9 Manual.Count131072.C015339.packed 128 cuts15339 = true := by
 decide +kernel
def pointBounds15339 : List (Nat × Nat × Nat) := [(2014509056,96562501456004,96562879684384),(2014572544,96562918105862,96563296334516)]
theorem point_links_checked15339 : (cuts15339.take 2).map (fun c => (2014445569-1+2*2^9*c.k,96562083814930+c.lower,96562462043031+c.upper)) = pointBounds15339 := by
 decide +kernel
def cuts15340 : List PrefixCut := [⟨58,381427562,381427811⟩,
⟨120,789109475,789109994⟩,
⟨128,842059687,842060241⟩]
theorem checked15340 : checkPrefixCuts (2^48) 2014576641 9 Manual.Count131072.C015340.packed 128 cuts15340 = true := by
 decide +kernel
def pointBounds15340 : List (Nat × Nat × Nat) := [(2014636032,96563326219804,96563704448725),(2014699520,96563733901717,96564112130908)]
theorem point_links_checked15340 : (cuts15340.take 2).map (fun c => (2014576641-1+2*2^9*c.k,96562944792242+c.lower,96563323020914+c.upper)) = pointBounds15340 := by
 decide +kernel
def cuts15341 : List PrefixCut := [⟨54,360586702,360586936⟩,
⟨116,782632485,782632994⟩,
⟨128,865335695,865336258⟩]
theorem checked15341 : checkPrefixCuts (2^48) 2014707713 9 Manual.Count131072.C015341.packed 128 cuts15341 = true := by
 decide +kernel
def pointBounds15341 : List (Nat × Nat × Nat) := [(2014763008,96564147438631,96564525668091),(2014826496,96564569484414,96564947714149)]
theorem point_links_checked15341 : (cuts15341.take 2).map (fun c => (2014707713-1+2*2^9*c.k,96563786851929+c.lower,96564165081155+c.upper)) = pointBounds15341 := by
 decide +kernel
def cuts15342 : List PrefixCut := [⟨50,330388499,330388717⟩,
⟨112,743746618,743747112⟩,
⟨128,851728870,851729436⟩]
theorem checked15342 : checkPrefixCuts (2^48) 2014838785 9 Manual.Count131072.C015342.packed 128 cuts15342 = true := by
 decide +kernel
def pointBounds15342 : List (Nat × Nat × Nat) := [(2014889984,96564982576123,96565360806130),(2014953472,96565395934242,96565774164525)]
theorem point_links_checked15342 : (cuts15342.take 2).map (fun c => (2014838785-1+2*2^9*c.k,96564652187624+c.lower,96565030417413+c.upper)) = pointBounds15342 := by
 decide +kernel
def cuts15343 : List PrefixCut := [⟨46,315560202,315560411⟩,
⟨108,729450990,729451472⟩,
⟨128,863128090,863128660⟩]
theorem checked15343 : checkPrefixCuts (2^48) 2014969857 9 Manual.Count131072.C015343.packed 128 cuts15343 = true := by
 decide +kernel
def pointBounds15343 : List (Nat × Nat × Nat) := [(2015016960,96565819476696,96566197707260),(2015080448,96566233367484,96566611598321)]
theorem point_links_checked15343 : (cuts15343.take 2).map (fun c => (2014969857-1+2*2^9*c.k,96565503916494+c.lower,96565882146849+c.upper)) = pointBounds15343 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000166
