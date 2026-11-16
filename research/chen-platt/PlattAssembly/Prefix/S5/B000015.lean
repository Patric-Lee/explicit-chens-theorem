import PlattAssemblyKernel
import PlattCertificates.Count131072.C040480
import PlattCertificates.Count131072.C040481
import PlattCertificates.Count131072.C040482
import PlattCertificates.Count131072.C040483
import PlattCertificates.Count131072.C040484
import PlattCertificates.Count131072.C040485
import PlattCertificates.Count131072.C040486
import PlattCertificates.Count131072.C040487
import PlattCertificates.Count131072.C040488
import PlattCertificates.Count131072.C040489
import PlattCertificates.Count131072.C040490
import PlattCertificates.Count131072.C040491
import PlattCertificates.Count131072.C040492
import PlattCertificates.Count131072.C040493
import PlattCertificates.Count131072.C040494
import PlattCertificates.Count131072.C040495
import PlattCertificates.Count131072.C040496
import PlattCertificates.Count131072.C040497
import PlattCertificates.Count131072.C040498
import PlattCertificates.Count131072.C040499
import PlattCertificates.Count131072.C040500
import PlattCertificates.Count131072.C040501
import PlattCertificates.Count131072.C040502
import PlattCertificates.Count131072.C040503
import PlattCertificates.Count131072.C040504
import PlattCertificates.Count131072.C040505
import PlattCertificates.Count131072.C040506
import PlattCertificates.Count131072.C040507
import PlattCertificates.Count131072.C040508
import PlattCertificates.Count131072.C040509
import PlattCertificates.Count131072.C040510
import PlattCertificates.Count131072.C040511
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40480 : List PrefixCut := [⟨13,61068731,61068767⟩,
⟨64,307143003,307143183⟩]
theorem checked40480 : checkPrefixCuts (2^48) 5309726721 10 Manual.Count131072.C040480.packed 64 cuts40480 = true := by
 decide +kernel
def pointBounds40480 : List (Nat × Nat × Nat) := [(5309753344,109016164732298,109016550326877)]
theorem point_links_checked40480 : (cuts40480.take 1).map (fun c => (5309726721-1+2*2^10*c.k,109016103663567+c.lower,109016489258110+c.upper)) = pointBounds40480 := by
 decide +kernel
def cuts40481 : List PrefixCut := [⟨31,150388126,150388213⟩,
⟨64,310687049,310687230⟩]
theorem checked40481 : checkPrefixCuts (2^48) 5309857793 10 Manual.Count131072.C040481.packed 64 cuts40481 = true := by
 decide +kernel
def pointBounds40481 : List (Nat × Nat × Nat) := [(5309921280,109016561194696,109016946789506)]
theorem point_links_checked40481 : (cuts40481.take 1).map (fun c => (5309857793-1+2*2^10*c.k,109016410806570+c.lower,109016796401293+c.upper)) = pointBounds40481 := by
 decide +kernel
def cuts40482 : List PrefixCut := [⟨49,235514829,235514970⟩,
⟨64,310997376,310997562⟩]
theorem checked40482 : checkPrefixCuts (2^48) 5309988865 10 Manual.Count131072.C040482.packed 64 cuts40482 = true := by
 decide +kernel
def pointBounds40482 : List (Nat × Nat × Nat) := [(5310089216,109016957008448,109017342603493)]
theorem point_links_checked40482 : (cuts40482.take 1).map (fun c => (5309988865-1+2*2^10*c.k,109016721493619+c.lower,109017107088523+c.upper)) = pointBounds40482 := by
 decide +kernel
def cuts40483 : List PrefixCut := [⟨64,314329139,314329324⟩]
theorem checked40483 : checkPrefixCuts (2^48) 5310119937 10 Manual.Count131072.C040483.packed 64 cuts40483 = true := by
 decide +kernel
def cuts40484 : List PrefixCut := [⟨3,13834545,13834552⟩,
⟨64,307642721,307642904⟩]
theorem checked40484 : checkPrefixCuts (2^48) 5310251009 10 Manual.Count131072.C040484.packed 64 cuts40484 = true := by
 decide +kernel
def pointBounds40484 : List (Nat × Nat × Nat) := [(5310257152,109017360654679,109017746249961)]
theorem point_links_checked40484 : (cuts40484.take 1).map (fun c => (5310251009-1+2*2^10*c.k,109017346820134+c.lower,109017732415409+c.upper)) = pointBounds40484 := by
 decide +kernel
def cuts40485 : List PrefixCut := [⟨21,102192533,102192593⟩,
⟨64,313306563,313306746⟩]
theorem checked40485 : checkPrefixCuts (2^48) 5310382081 10 Manual.Count131072.C040485.packed 64 cuts40485 = true := by
 decide +kernel
def pointBounds40485 : List (Nat × Nat × Nat) := [(5310425088,109017756655388,109018142250906)]
theorem point_links_checked40485 : (cuts40485.take 1).map (fun c => (5310382081-1+2*2^10*c.k,109017654462855+c.lower,109018040058313+c.upper)) = pointBounds40485 := by
 decide +kernel
def cuts40486 : List PrefixCut := [⟨39,188213424,188213536⟩,
⟨64,310595693,310595879⟩]
theorem checked40486 : checkPrefixCuts (2^48) 5310513153 10 Manual.Count131072.C040486.packed 64 cuts40486 = true := by
 decide +kernel
def pointBounds40486 : List (Nat × Nat × Nat) := [(5310593024,109018155982842,109018541578595)]
theorem point_links_checked40486 : (cuts40486.take 1).map (fun c => (5310513153-1+2*2^10*c.k,109017967769418+c.lower,109018353365059+c.upper)) = pointBounds40486 := by
 decide +kernel
def cuts40487 : List PrefixCut := [⟨57,272586431,272586593⟩,
⟨64,308255961,308256144⟩]
theorem checked40487 : checkPrefixCuts (2^48) 5310644225 10 Manual.Count131072.C040487.packed 64 cuts40487 = true := by
 decide +kernel
def pointBounds40487 : List (Nat × Nat × Nat) := [(5310760960,109018550951542,109018936547531)]
theorem point_links_checked40487 : (cuts40487.take 1).map (fun c => (5310644225-1+2*2^10*c.k,109018278365111+c.lower,109018663960938+c.upper)) = pointBounds40487 := by
 decide +kernel
def cuts40488 : List PrefixCut := [⟨64,312488378,312488564⟩]
theorem checked40488 : checkPrefixCuts (2^48) 5310775297 10 Manual.Count131072.C040488.packed 64 cuts40488 = true := by
 decide +kernel
def cuts40489 : List PrefixCut := [⟨11,52098308,52098339⟩,
⟨64,311685672,311685858⟩]
theorem checked40489 : checkPrefixCuts (2^48) 5310906369 10 Manual.Count131072.C040489.packed 64 cuts40489 = true := by
 decide +kernel
def pointBounds40489 : List (Nat × Nat × Nat) := [(5310928896,109018951207758,109019336803985)]
theorem point_links_checked40489 : (cuts40489.take 1).map (fun c => (5310906369-1+2*2^10*c.k,109018899109450+c.lower,109019284705646+c.upper)) = pointBounds40489 := by
 decide +kernel
def cuts40490 : List PrefixCut := [⟨29,142299113,142299200⟩,
⟨64,309187142,309187329⟩]
theorem checked40490 : checkPrefixCuts (2^48) 5311037441 10 Manual.Count131072.C040490.packed 64 cuts40490 = true := by
 decide +kernel
def pointBounds40490 : List (Nat × Nat × Nat) := [(5311096832,109019353094235,109019738690704)]
theorem point_links_checked40490 : (cuts40490.take 1).map (fun c => (5311037441-1+2*2^10*c.k,109019210795122+c.lower,109019596391504+c.upper)) = pointBounds40490 := by
 decide +kernel
def cuts40491 : List PrefixCut := [⟨47,228202124,228202261⟩,
⟨64,310186408,310186594⟩]
theorem checked40491 : checkPrefixCuts (2^48) 5311168513 10 Manual.Count131072.C040491.packed 64 cuts40491 = true := by
 decide +kernel
def pointBounds40491 : List (Nat × Nat × Nat) := [(5311264768,109019748184388,109020133781094)]
theorem point_links_checked40491 : (cuts40491.take 1).map (fun c => (5311168513-1+2*2^10*c.k,109019519982264+c.lower,109019905578833+c.upper)) = pointBounds40491 := by
 decide +kernel
def cuts40492 : List PrefixCut := [⟨64,308747885,308748074⟩]
theorem checked40492 : checkPrefixCuts (2^48) 5311299585 10 Manual.Count131072.C040492.packed 64 cuts40492 = true := by
 decide +kernel
def cuts40493 : List PrefixCut := [⟨1,4610492,4610495⟩,
⟨64,311972860,311973045⟩]
theorem checked40493 : checkPrefixCuts (2^48) 5311430657 10 Manual.Count131072.C040493.packed 64 cuts40493 = true := by
 decide +kernel
def pointBounds40493 : List (Nat × Nat × Nat) := [(5311432704,109020143527049,109020529123996)]
theorem point_links_checked40493 : (cuts40493.take 1).map (fun c => (5311430657-1+2*2^10*c.k,109020138916557+c.lower,109020524513501+c.upper)) = pointBounds40493 := by
 decide +kernel
def cuts40494 : List PrefixCut := [⟨19,93744040,93744096⟩,
⟨64,308785680,308785868⟩]
theorem checked40494 : checkPrefixCuts (2^48) 5311561729 10 Manual.Count131072.C040494.packed 64 cuts40494 = true := by
 decide +kernel
def pointBounds40494 : List (Nat × Nat × Nat) := [(5311600640,109020544633457,109020930230642)]
theorem point_links_checked40494 : (cuts40494.take 1).map (fun c => (5311561729-1+2*2^10*c.k,109020450889417+c.lower,109020836486546+c.upper)) = pointBounds40494 := by
 decide +kernel
def cuts40495 : List PrefixCut := [⟨37,180381972,180382082⟩,
⟨64,306022524,306022712⟩]
theorem checked40495 : checkPrefixCuts (2^48) 5311692801 10 Manual.Count131072.C040495.packed 64 cuts40495 = true := by
 decide +kernel
def pointBounds40495 : List (Nat × Nat × Nat) := [(5311768576,109020940057069,109021325654496)]
theorem point_links_checked40495 : (cuts40495.take 1).map (fun c => (5311692801-1+2*2^10*c.k,109020759675097+c.lower,109021145272414+c.upper)) = pointBounds40495 := by
 decide +kernel
def cuts40496 : List PrefixCut := [⟨55,265478343,265478499⟩,
⟨64,308717398,308717579⟩]
theorem checked40496 : checkPrefixCuts (2^48) 5311823873 10 Manual.Count131072.C040496.packed 64 cuts40496 = true := by
 decide +kernel
def pointBounds40496 : List (Nat × Nat × Nat) := [(5311936512,109021331175964,109021716773625)]
theorem point_links_checked40496 : (cuts40496.take 1).map (fun c => (5311823873-1+2*2^10*c.k,109021065697621+c.lower,109021451295126+c.upper)) = pointBounds40496 := by
 decide +kernel
def cuts40497 : List PrefixCut := [⟨64,311253217,311253406⟩]
theorem checked40497 : checkPrefixCuts (2^48) 5311954945 10 Manual.Count131072.C040497.packed 64 cuts40497 = true := by
 decide +kernel
def cuts40498 : List PrefixCut := [⟨9,44350576,44350603⟩,
⟨64,308596210,308596390⟩]
theorem checked40498 : checkPrefixCuts (2^48) 5312086017 10 Manual.Count131072.C040498.packed 64 cuts40498 = true := by
 decide +kernel
def pointBounds40498 : List (Nat × Nat × Nat) := [(5312104448,109021730018812,109022115616714)]
theorem point_links_checked40498 : (cuts40498.take 1).map (fun c => (5312086017-1+2*2^10*c.k,109021685668236+c.lower,109022071266111+c.upper)) = pointBounds40498 := by
 decide +kernel
def cuts40499 : List PrefixCut := [⟨27,130716596,130716675⟩,
⟨64,312085631,312085819⟩]
theorem checked40499 : checkPrefixCuts (2^48) 5312217089 10 Manual.Count131072.C040499.packed 64 cuts40499 = true := by
 decide +kernel
def pointBounds40499 : List (Nat × Nat × Nat) := [(5312272384,109022124981042,109022510579176)]
theorem point_links_checked40499 : (cuts40499.take 1).map (fun c => (5312217089-1+2*2^10*c.k,109021994264446+c.lower,109022379862501+c.upper)) = pointBounds40499 := by
 decide +kernel
def cuts40500 : List PrefixCut := [⟨45,218773239,218773373⟩,
⟨64,312501776,312501965⟩]
theorem checked40500 : checkPrefixCuts (2^48) 5312348161 10 Manual.Count131072.C040500.packed 64 cuts40500 = true := by
 decide +kernel
def pointBounds40500 : List (Nat × Nat × Nat) := [(5312440320,109022525123316,109022910721693)]
theorem point_links_checked40500 : (cuts40500.take 1).map (fun c => (5312348161-1+2*2^10*c.k,109022306350077+c.lower,109022691948320+c.upper)) = pointBounds40500 := by
 decide +kernel
def cuts40501 : List PrefixCut := [⟨63,307513768,307513950⟩,
⟨64,312017274,312017458⟩]
theorem checked40501 : checkPrefixCuts (2^48) 5312479233 10 Manual.Count131072.C040501.packed 64 cuts40501 = true := by
 decide +kernel
def pointBounds40501 : List (Nat × Nat × Nat) := [(5312608256,109022926365621,109023311964235)]
theorem point_links_checked40501 : (cuts40501.take 1).map (fun c => (5312479233-1+2*2^10*c.k,109022618851853+c.lower,109023004450285+c.upper)) = pointBounds40501 := by
 decide +kernel
def cuts40502 : List PrefixCut := [⟨64,311267839,311268020⟩]
theorem checked40502 : checkPrefixCuts (2^48) 5312610305 10 Manual.Count131072.C040502.packed 64 cuts40502 = true := by
 decide +kernel
def cuts40503 : List PrefixCut := [⟨17,82385344,82385393⟩,
⟨64,310677312,310677499⟩]
theorem checked40503 : checkPrefixCuts (2^48) 5312741377 10 Manual.Count131072.C040503.packed 64 cuts40503 = true := by
 decide +kernel
def pointBounds40503 : List (Nat × Nat × Nat) := [(5312776192,109023324522310,109023710121156)]
theorem point_links_checked40503 : (cuts40503.take 1).map (fun c => (5312741377-1+2*2^10*c.k,109023242136966+c.lower,109023627735763+c.upper)) = pointBounds40503 := by
 decide +kernel
def cuts40504 : List PrefixCut := [⟨35,169163351,169163451⟩,
⟨64,307649885,307650068⟩]
theorem checked40504 : checkPrefixCuts (2^48) 5312872449 10 Manual.Count131072.C040504.packed 64 cuts40504 = true := by
 decide +kernel
def pointBounds40504 : List (Nat × Nat × Nat) := [(5312944128,109023721977629,109024107576713)]
theorem point_links_checked40504 : (cuts40504.take 1).map (fun c => (5312872449-1+2*2^10*c.k,109023552814278+c.lower,109023938413262+c.upper)) = pointBounds40504 := by
 decide +kernel
def cuts40505 : List PrefixCut := [⟨53,255194761,255194913⟩,
⟨64,309549462,309549648⟩]
theorem checked40505 : checkPrefixCuts (2^48) 5313003521 10 Manual.Count131072.C040505.packed 64 cuts40505 = true := by
 decide +kernel
def pointBounds40505 : List (Nat × Nat × Nat) := [(5313112064,109024115658924,109024501258243)]
theorem point_links_checked40505 : (cuts40505.take 1).map (fun c => (5313003521-1+2*2^10*c.k,109023860464163+c.lower,109024246063330+c.upper)) = pointBounds40505 := by
 decide +kernel
def cuts40506 : List PrefixCut := [⟨64,310601357,310601542⟩]
theorem checked40506 : checkPrefixCuts (2^48) 5313134593 10 Manual.Count131072.C040506.packed 64 cuts40506 = true := by
 decide +kernel
def cuts40507 : List PrefixCut := [⟨7,34010465,34010484⟩,
⟨64,310540763,310540947⟩]
theorem checked40507 : checkPrefixCuts (2^48) 5313265665 10 Manual.Count131072.C040507.packed 64 cuts40507 = true := by
 decide +kernel
def pointBounds40507 : List (Nat × Nat × Nat) := [(5313280000,109024514625447,109024900225004)]
theorem point_links_checked40507 : (cuts40507.take 1).map (fun c => (5313265665-1+2*2^10*c.k,109024480614982+c.lower,109024866214520+c.upper)) = pointBounds40507 := by
 decide +kernel
def cuts40508 : List PrefixCut := [⟨25,122370666,122370736⟩,
⟨64,309738480,309738663⟩]
theorem checked40508 : checkPrefixCuts (2^48) 5313396737 10 Manual.Count131072.C040508.packed 64 cuts40508 = true := by
 decide +kernel
def pointBounds40508 : List (Nat × Nat × Nat) := [(5313447936,109024913526411,109025299126203)]
theorem point_links_checked40508 : (cuts40508.take 1).map (fun c => (5313396737-1+2*2^10*c.k,109024791155745+c.lower,109025176755467+c.upper)) = pointBounds40508 := by
 decide +kernel
def cuts40509 : List PrefixCut := [⟨43,205428615,205428739⟩,
⟨64,306234649,306234831⟩]
theorem checked40509 : checkPrefixCuts (2^48) 5313527809 10 Manual.Count131072.C040509.packed 64 cuts40509 = true := by
 decide +kernel
def pointBounds40509 : List (Nat × Nat × Nat) := [(5313615872,109025306322840,109025691922869)]
theorem point_links_checked40509 : (cuts40509.take 1).map (fun c => (5313527809-1+2*2^10*c.k,109025100894225+c.lower,109025486494130+c.upper)) = pointBounds40509 := by
 decide +kernel
def cuts40510 : List PrefixCut := [⟨61,294149790,294149964⟩,
⟨64,308928608,308928791⟩]
theorem checked40510 : checkPrefixCuts (2^48) 5313658881 10 Manual.Count131072.C040510.packed 64 cuts40510 = true := by
 decide +kernel
def pointBounds40510 : List (Nat × Nat × Nat) := [(5313783808,109025701278664,109026086878925)]
theorem point_links_checked40510 : (cuts40510.take 1).map (fun c => (5313658881-1+2*2^10*c.k,109025407128874+c.lower,109025792728961+c.upper)) = pointBounds40510 := by
 decide +kernel
def cuts40511 : List PrefixCut := [⟨64,310933894,310934074⟩]
theorem checked40511 : checkPrefixCuts (2^48) 5313789953 10 Manual.Count131072.C040511.packed 64 cuts40511 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000015
