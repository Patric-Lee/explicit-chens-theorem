import PlattAssemblyKernel
import PlattCertificates.Count131072.C060320
import PlattCertificates.Count131072.C060321
import PlattCertificates.Count131072.C060322
import PlattCertificates.Count131072.C060323
import PlattCertificates.Count131072.C060324
import PlattCertificates.Count131072.C060325
import PlattCertificates.Count131072.C060326
import PlattCertificates.Count131072.C060327
import PlattCertificates.Count131072.C060328
import PlattCertificates.Count131072.C060329
import PlattCertificates.Count131072.C060330
import PlattCertificates.Count131072.C060331
import PlattCertificates.Count131072.C060332
import PlattCertificates.Count131072.C060333
import PlattCertificates.Count131072.C060334
import PlattCertificates.Count131072.C060335
import PlattCertificates.Count131072.C060336
import PlattCertificates.Count131072.C060337
import PlattCertificates.Count131072.C060338
import PlattCertificates.Count131072.C060339
import PlattCertificates.Count131072.C060340
import PlattCertificates.Count131072.C060341
import PlattCertificates.Count131072.C060342
import PlattCertificates.Count131072.C060343
import PlattCertificates.Count131072.C060344
import PlattCertificates.Count131072.C060345
import PlattCertificates.Count131072.C060346
import PlattCertificates.Count131072.C060347
import PlattCertificates.Count131072.C060348
import PlattCertificates.Count131072.C060349
import PlattCertificates.Count131072.C060350
import PlattCertificates.Count131072.C060351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60320 : List PrefixCut := [⟨24,77145464,77145511⟩,
⟨64,210440907,210441029⟩]
theorem checked60320 : checkPrefixCuts (2^48) 7910195201 10 Manual.Count131072.C060320.packed 64 cuts60320 = true := by
 decide +kernel
def pointBounds60320 : List (Nat × Nat × Nat) := [(7910244352,113982555021141,113982943465936)]
theorem point_links_checked60320 : (cuts60320.take 1).map (fun c => (7910195201-1+2*2^10*c.k,113982477875677+c.lower,113982866320425+c.upper)) = pointBounds60320 := by
 decide +kernel
def cuts60321 : List PrefixCut := [⟨64,203534347,203534464⟩]
theorem checked60321 : checkPrefixCuts (2^48) 7910326273 10 Manual.Count131072.C060321.packed 64 cuts60321 = true := by
 decide +kernel
def cuts60322 : List PrefixCut := [⟨17,54619221,54619250⟩,
⟨64,205310099,205310212⟩]
theorem checked60322 : checkPrefixCuts (2^48) 7910457345 10 Manual.Count131072.C060322.packed 64 cuts60322 = true := by
 decide +kernel
def pointBounds60322 : List (Nat × Nat × Nat) := [(7910492160,113982946470152,113983334915168)]
theorem point_links_checked60322 : (cuts60322.take 1).map (fun c => (7910457345-1+2*2^10*c.k,113982891850931+c.lower,113983280295918+c.upper)) = pointBounds60322 := by
 decide +kernel
def cuts60323 : List PrefixCut := [⟨64,206231812,206231931⟩]
theorem checked60323 : checkPrefixCuts (2^48) 7910588417 10 Manual.Count131072.C060323.packed 64 cuts60323 = true := by
 decide +kernel
def cuts60324 : List PrefixCut := [⟨10,32130009,32130028⟩,
⟨64,203880030,203880143⟩]
theorem checked60324 : checkPrefixCuts (2^48) 7910719489 10 Manual.Count131072.C060324.packed 64 cuts60324 = true := by
 decide +kernel
def pointBounds60324 : List (Nat × Nat × Nat) := [(7910739968,113983335522851,113983723968089)]
theorem point_links_checked60324 : (cuts60324.take 1).map (fun c => (7910719489-1+2*2^10*c.k,113983303392842+c.lower,113983691838061+c.upper)) = pointBounds60324 := by
 decide +kernel
def cuts60325 : List PrefixCut := [⟨64,203200635,203200752⟩]
theorem checked60325 : checkPrefixCuts (2^48) 7910850561 10 Manual.Count131072.C060325.packed 64 cuts60325 = true := by
 decide +kernel
def cuts60326 : List PrefixCut := [⟨3,9250868,9250873⟩,
⟨64,203232856,203232974⟩]
theorem checked60326 : checkPrefixCuts (2^48) 7910981633 10 Manual.Count131072.C060326.packed 64 cuts60326 = true := by
 decide +kernel
def pointBounds60326 : List (Nat × Nat × Nat) := [(7910987776,113983719724375,113984108169829)]
theorem point_links_checked60326 : (cuts60326.take 1).map (fun c => (7910981633-1+2*2^10*c.k,113983710473507+c.lower,113984098918956+c.upper)) = pointBounds60326 := by
 decide +kernel
def cuts60327 : List PrefixCut := [⟨60,187716954,187717063⟩,
⟨64,200134065,200134182⟩]
theorem checked60327 : checkPrefixCuts (2^48) 7911112705 10 Manual.Count131072.C060327.packed 64 cuts60327 = true := by
 decide +kernel
def pointBounds60327 : List (Nat × Nat × Nat) := [(7911235584,113984101423317,113984489868993)]
theorem point_links_checked60327 : (cuts60327.take 1).map (fun c => (7911112705-1+2*2^10*c.k,113983913706363+c.lower,113984302151930+c.upper)) = pointBounds60327 := by
 decide +kernel
def cuts60328 : List PrefixCut := [⟨64,204542507,204542625⟩]
theorem checked60328 : checkPrefixCuts (2^48) 7911243777 10 Manual.Count131072.C060328.packed 64 cuts60328 = true := by
 decide +kernel
def cuts60329 : List PrefixCut := [⟨53,170562188,170562287⟩,
⟨64,206353625,206353743⟩]
theorem checked60329 : checkPrefixCuts (2^48) 7911374849 10 Manual.Count131072.C060329.packed 64 cuts60329 = true := by
 decide +kernel
def pointBounds60329 : List (Nat × Nat × Nat) := [(7911483392,113984488945123,113984877391024)]
theorem point_links_checked60329 : (cuts60329.take 1).map (fun c => (7911374849-1+2*2^10*c.k,113984318382935+c.lower,113984706828737+c.upper)) = pointBounds60329 := by
 decide +kernel
def cuts60330 : List PrefixCut := [⟨64,203468433,203468547⟩]
theorem checked60330 : checkPrefixCuts (2^48) 7911505921 10 Manual.Count131072.C060330.packed 64 cuts60330 = true := by
 decide +kernel
def cuts60331 : List PrefixCut := [⟨46,147289253,147289336⟩,
⟨64,204745820,204745935⟩]
theorem checked60331 : checkPrefixCuts (2^48) 7911636993 10 Manual.Count131072.C060331.packed 64 cuts60331 = true := by
 decide +kernel
def pointBounds60331 : List (Nat × Nat × Nat) := [(7911731200,113984875494246,113985263940363)]
theorem point_links_checked60331 : (cuts60331.take 1).map (fun c => (7911636993-1+2*2^10*c.k,113984728204993+c.lower,113985116651027+c.upper)) = pointBounds60331 := by
 decide +kernel
def cuts60332 : List PrefixCut := [⟨64,205453967,205454084⟩]
theorem checked60332 : checkPrefixCuts (2^48) 7911768065 10 Manual.Count131072.C060332.packed 64 cuts60332 = true := by
 decide +kernel
def cuts60333 : List PrefixCut := [⟨39,123164002,123164073⟩,
⟨64,203066967,203067082⟩]
theorem checked60333 : checkPrefixCuts (2^48) 7911899137 10 Manual.Count131072.C060333.packed 64 cuts60333 = true := by
 decide +kernel
def pointBounds60333 : List (Nat × Nat × Nat) := [(7911979008,113985261568782,113985650015119)]
theorem point_links_checked60333 : (cuts60333.take 1).map (fun c => (7911899137-1+2*2^10*c.k,113985138404780+c.lower,113985526851046+c.upper)) = pointBounds60333 := by
 decide +kernel
def cuts60334 : List PrefixCut := [⟨64,206300960,206301078⟩]
theorem checked60334 : checkPrefixCuts (2^48) 7912030209 10 Manual.Count131072.C060334.packed 64 cuts60334 = true := by
 decide +kernel
def cuts60335 : List PrefixCut := [⟨32,102491054,102491117⟩,
⟨64,202668921,202669042⟩]
theorem checked60335 : checkPrefixCuts (2^48) 7912161281 10 Manual.Count131072.C060335.packed 64 cuts60335 = true := by
 decide +kernel
def pointBounds60335 : List (Nat × Nat × Nat) := [(7912226816,113985650263761,113986038710323)]
theorem point_links_checked60335 : (cuts60335.take 1).map (fun c => (7912161281-1+2*2^10*c.k,113985547772707+c.lower,113985936219206+c.upper)) = pointBounds60335 := by
 decide +kernel
def cuts60336 : List PrefixCut := [⟨64,204977881,204978003⟩]
theorem checked60336 : checkPrefixCuts (2^48) 7912292353 10 Manual.Count131072.C060336.packed 64 cuts60336 = true := by
 decide +kernel
def cuts60337 : List PrefixCut := [⟨25,81606016,81606062⟩,
⟨64,206077273,206077394⟩]
theorem checked60337 : checkPrefixCuts (2^48) 7912423425 10 Manual.Count131072.C060337.packed 64 cuts60337 = true := by
 decide +kernel
def pointBounds60337 : List (Nat × Nat × Nat) := [(7912474624,113986037025525,113986425472313)]
theorem point_links_checked60337 : (cuts60337.take 1).map (fun c => (7912423425-1+2*2^10*c.k,113985955419509+c.lower,113986343866251+c.upper)) = pointBounds60337 := by
 decide +kernel
def cuts60338 : List PrefixCut := [⟨64,204224051,204224164⟩]
theorem checked60338 : checkPrefixCuts (2^48) 7912554497 10 Manual.Count131072.C060338.packed 64 cuts60338 = true := by
 decide +kernel
def cuts60339 : List PrefixCut := [⟨18,58445665,58445702⟩,
⟨64,205608002,205608121⟩]
theorem checked60339 : checkPrefixCuts (2^48) 7912685569 10 Manual.Count131072.C060339.packed 64 cuts60339 = true := by
 decide +kernel
def pointBounds60339 : List (Nat × Nat × Nat) := [(7912722432,113986424166498,113986812613511)]
theorem point_links_checked60339 : (cuts60339.take 1).map (fun c => (7912685569-1+2*2^10*c.k,113986365720833+c.lower,113986754167809+c.upper)) = pointBounds60339 := by
 decide +kernel
def cuts60340 : List PrefixCut := [⟨64,205248873,205248993⟩]
theorem checked60340 : checkPrefixCuts (2^48) 7912816641 10 Manual.Count131072.C060340.packed 64 cuts60340 = true := by
 decide +kernel
def cuts60341 : List PrefixCut := [⟨11,34468673,34468691⟩,
⟨64,206063601,206063718⟩]
theorem checked60341 : checkPrefixCuts (2^48) 7912947713 10 Manual.Count131072.C060341.packed 64 cuts60341 = true := by
 decide +kernel
def pointBounds60341 : List (Nat × Nat × Nat) := [(7912970240,113986811046381,113987199493614)]
theorem point_links_checked60341 : (cuts60341.take 1).map (fun c => (7912947713-1+2*2^10*c.k,113986776577708+c.lower,113987165024923+c.upper)) = pointBounds60341 := by
 decide +kernel
def cuts60342 : List PrefixCut := [⟨64,204601834,204601945⟩]
theorem checked60342 : checkPrefixCuts (2^48) 7913078785 10 Manual.Count131072.C060342.packed 64 cuts60342 = true := by
 decide +kernel
def cuts60343 : List PrefixCut := [⟨4,12271732,12271739⟩,
⟨64,208013116,208013232⟩]
theorem checked60343 : checkPrefixCuts (2^48) 7913209857 10 Manual.Count131072.C060343.packed 64 cuts60343 = true := by
 decide +kernel
def pointBounds60343 : List (Nat × Nat × Nat) := [(7913218048,113987199514875,113987587962325)]
theorem point_links_checked60343 : (cuts60343.take 1).map (fun c => (7913209857-1+2*2^10*c.k,113987187243143+c.lower,113987575690586+c.upper)) = pointBounds60343 := by
 decide +kernel
def cuts60344 : List PrefixCut := [⟨61,192359242,192359353⟩,
⟨64,202318587,202318704⟩]
theorem checked60344 : checkPrefixCuts (2^48) 7913340929 10 Manual.Count131072.C060344.packed 64 cuts60344 = true := by
 decide +kernel
def pointBounds60344 : List (Nat × Nat × Nat) := [(7913465856,113987587615501,113987976063171)]
theorem point_links_checked60344 : (cuts60344.take 1).map (fun c => (7913340929-1+2*2^10*c.k,113987395256259+c.lower,113987783703818+c.upper)) = pointBounds60344 := by
 decide +kernel
def cuts60345 : List PrefixCut := [⟨64,204413797,204413910⟩]
theorem checked60345 : checkPrefixCuts (2^48) 7913472001 10 Manual.Count131072.C060345.packed 64 cuts60345 = true := by
 decide +kernel
def cuts60346 : List PrefixCut := [⟨54,169980604,169980699⟩,
⟨64,201493803,201493917⟩]
theorem checked60346 : checkPrefixCuts (2^48) 7913603073 10 Manual.Count131072.C060346.packed 64 cuts60346 = true := by
 decide +kernel
def pointBounds60346 : List (Nat × Nat × Nat) := [(7913713664,113987971969247,113988360417131)]
theorem point_links_checked60346 : (cuts60346.take 1).map (fun c => (7913603073-1+2*2^10*c.k,113987801988643+c.lower,113988190436432+c.upper)) = pointBounds60346 := by
 decide +kernel
def cuts60347 : List PrefixCut := [⟨64,202095143,202095263⟩]
theorem checked60347 : checkPrefixCuts (2^48) 7913734145 10 Manual.Count131072.C060347.packed 64 cuts60347 = true := by
 decide +kernel
def cuts60348 : List PrefixCut := [⟨47,148848287,148848377⟩,
⟨64,204119094,204119215⟩]
theorem checked60348 : checkPrefixCuts (2^48) 7913865217 10 Manual.Count131072.C060348.packed 64 cuts60348 = true := by
 decide +kernel
def pointBounds60348 : List (Nat × Nat × Nat) := [(7913961472,113988354425876,113988742873989)]
theorem point_links_checked60348 : (cuts60348.take 1).map (fun c => (7913865217-1+2*2^10*c.k,113988205577589+c.lower,113988594025612+c.upper)) = pointBounds60348 := by
 decide +kernel
def cuts60349 : List PrefixCut := [⟨64,203048732,203048842⟩]
theorem checked60349 : checkPrefixCuts (2^48) 7913996289 10 Manual.Count131072.C060349.packed 64 cuts60349 = true := by
 decide +kernel
def cuts60350 : List PrefixCut := [⟨40,125832318,125832389⟩,
⟨64,201978380,201978494⟩]
theorem checked60350 : checkPrefixCuts (2^48) 7914127361 10 Manual.Count131072.C060350.packed 64 cuts60350 = true := by
 decide +kernel
def pointBounds60350 : List (Nat × Nat × Nat) := [(7914209280,113988738577733,113989127026058)]
theorem point_links_checked60350 : (cuts60350.take 1).map (fun c => (7914127361-1+2*2^10*c.k,113988612745415+c.lower,113989001193669+c.upper)) = pointBounds60350 := by
 decide +kernel
def cuts60351 : List PrefixCut := [⟨64,204073398,204073515⟩]
theorem checked60351 : checkPrefixCuts (2^48) 7914258433 10 Manual.Count131072.C060351.packed 64 cuts60351 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000010
