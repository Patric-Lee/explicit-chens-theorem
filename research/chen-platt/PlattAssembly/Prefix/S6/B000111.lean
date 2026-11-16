import PlattAssemblyKernel
import PlattCertificates.Count131072.C053552
import PlattCertificates.Count131072.C053553
import PlattCertificates.Count131072.C053554
import PlattCertificates.Count131072.C053555
import PlattCertificates.Count131072.C053556
import PlattCertificates.Count131072.C053557
import PlattCertificates.Count131072.C053558
import PlattCertificates.Count131072.C053559
import PlattCertificates.Count131072.C053560
import PlattCertificates.Count131072.C053561
import PlattCertificates.Count131072.C053562
import PlattCertificates.Count131072.C053563
import PlattCertificates.Count131072.C053564
import PlattCertificates.Count131072.C053565
import PlattCertificates.Count131072.C053566
import PlattCertificates.Count131072.C053567
import PlattCertificates.Count131072.C053568
import PlattCertificates.Count131072.C053569
import PlattCertificates.Count131072.C053570
import PlattCertificates.Count131072.C053571
import PlattCertificates.Count131072.C053572
import PlattCertificates.Count131072.C053573
import PlattCertificates.Count131072.C053574
import PlattCertificates.Count131072.C053575
import PlattCertificates.Count131072.C053576
import PlattCertificates.Count131072.C053577
import PlattCertificates.Count131072.C053578
import PlattCertificates.Count131072.C053579
import PlattCertificates.Count131072.C053580
import PlattCertificates.Count131072.C053581
import PlattCertificates.Count131072.C053582
import PlattCertificates.Count131072.C053583
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000111
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53552 : List PrefixCut := [⟨64,233214274,233214404⟩]
theorem checked53552 : checkPrefixCuts (2^48) 7023099905 10 Manual.Count131072.C053552.packed 64 cuts53552 = true := by
 decide +kernel
def cuts53553 : List PrefixCut := [⟨29,103720630,103720691⟩,
⟨64,232528583,232528716⟩]
theorem checked53553 : checkPrefixCuts (2^48) 7023230977 10 Manual.Count131072.C053553.packed 64 cuts53553 = true := by
 decide +kernel
def pointBounds53553 : List (Nat × Nat × Nat) := [(7023290368,112510004873012,112510392479926)]
theorem point_links_checked53553 : (cuts53553.take 1).map (fun c => (7023230977-1+2*2^10*c.k,112509901152382+c.lower,112510288759235+c.upper)) = pointBounds53553 := by
 decide +kernel
def cuts53554 : List PrefixCut := [⟨64,232564342,232564475⟩]
theorem checked53554 : checkPrefixCuts (2^48) 7023362049 10 Manual.Count131072.C053554.packed 64 cuts53554 = true := by
 decide +kernel
def cuts53555 : List PrefixCut := [⟨9,31459773,31459791⟩,
⟨64,231878696,231878825⟩]
theorem checked53555 : checkPrefixCuts (2^48) 7023493121 10 Manual.Count131072.C053555.packed 64 cuts53555 = true := by
 decide +kernel
def pointBounds53555 : List (Nat × Nat × Nat) := [(7023511552,112510397705080,112510785312217)]
theorem point_links_checked53555 : (cuts53555.take 1).map (fun c => (7023493121-1+2*2^10*c.k,112510366245307+c.lower,112510753852426+c.upper)) = pointBounds53555 := by
 decide +kernel
def cuts53556 : List PrefixCut := [⟨53,191999989,192000102⟩,
⟨64,232154905,232155041⟩]
theorem checked53556 : checkPrefixCuts (2^48) 7023624193 10 Manual.Count131072.C053556.packed 64 cuts53556 = true := by
 decide +kernel
def pointBounds53556 : List (Nat × Nat × Nat) := [(7023732736,112510790123992,112511177731353)]
theorem point_links_checked53556 : (cuts53556.take 1).map (fun c => (7023624193-1+2*2^10*c.k,112510598124003+c.lower,112510985731251+c.upper)) = pointBounds53556 := by
 decide +kernel
def cuts53557 : List PrefixCut := [⟨64,230707902,230708034⟩]
theorem checked53557 : checkPrefixCuts (2^48) 7023755265 10 Manual.Count131072.C053557.packed 64 cuts53557 = true := by
 decide +kernel
def cuts53558 : List PrefixCut := [⟨33,117536336,117536404⟩,
⟨64,231705415,231705544⟩]
theorem checked53558 : checkPrefixCuts (2^48) 7023886337 10 Manual.Count131072.C053558.packed 64 cuts53558 = true := by
 decide +kernel
def pointBounds53558 : List (Nat × Nat × Nat) := [(7023953920,112511178523146,112511566130730)]
theorem point_links_checked53558 : (cuts53558.take 1).map (fun c => (7023886337-1+2*2^10*c.k,112511060986810+c.lower,112511448594326+c.upper)) = pointBounds53558 := by
 decide +kernel
def cuts53559 : List PrefixCut := [⟨64,230859599,230859728⟩]
theorem checked53559 : checkPrefixCuts (2^48) 7024017409 10 Manual.Count131072.C053559.packed 64 cuts53559 = true := by
 decide +kernel
def cuts53560 : List PrefixCut := [⟨13,49449321,49449349⟩,
⟨64,231656755,231656886⟩]
theorem checked53560 : checkPrefixCuts (2^48) 7024148481 10 Manual.Count131072.C053560.packed 64 cuts53560 = true := by
 decide +kernel
def pointBounds53560 : List (Nat × Nat × Nat) := [(7024175104,112511573001145,112511960608947)]
theorem point_links_checked53560 : (cuts53560.take 1).map (fun c => (7024148481-1+2*2^10*c.k,112511523551824+c.lower,112511911159598+c.upper)) = pointBounds53560 := by
 decide +kernel
def cuts53561 : List PrefixCut := [⟨57,208411227,208411347⟩,
⟨64,234216952,234217087⟩]
theorem checked53561 : checkPrefixCuts (2^48) 7024279553 10 Manual.Count131072.C053561.packed 64 cuts53561 = true := by
 decide +kernel
def pointBounds53561 : List (Nat × Nat × Nat) := [(7024396288,112511963619806,112512351227831)]
theorem point_links_checked53561 : (cuts53561.take 1).map (fun c => (7024279553-1+2*2^10*c.k,112511755208579+c.lower,112512142816484+c.upper)) = pointBounds53561 := by
 decide +kernel
def cuts53562 : List PrefixCut := [⟨64,228682842,228682970⟩]
theorem checked53562 : checkPrefixCuts (2^48) 7024410625 10 Manual.Count131072.C053562.packed 64 cuts53562 = true := by
 decide +kernel
def cuts53563 : List PrefixCut := [⟨37,133673517,133673593⟩,
⟨64,230802293,230802424⟩]
theorem checked53563 : checkPrefixCuts (2^48) 7024541697 10 Manual.Count131072.C053563.packed 64 cuts53563 = true := by
 decide +kernel
def pointBounds53563 : List (Nat × Nat × Nat) := [(7024617472,112512351781890,112512739390134)]
theorem point_links_checked53563 : (cuts53563.take 1).map (fun c => (7024541697-1+2*2^10*c.k,112512218108373+c.lower,112512605716541+c.upper)) = pointBounds53563 := by
 decide +kernel
def cuts53564 : List PrefixCut := [⟨64,230156850,230156982⟩]
theorem checked53564 : checkPrefixCuts (2^48) 7024672769 10 Manual.Count131072.C053564.packed 64 cuts53564 = true := by
 decide +kernel
def cuts53565 : List PrefixCut := [⟨17,60784096,60784131⟩,
⟨64,235441592,235441724⟩]
theorem checked53565 : checkPrefixCuts (2^48) 7024803841 10 Manual.Count131072.C053565.packed 64 cuts53565 = true := by
 decide +kernel
def pointBounds53565 : List (Nat × Nat × Nat) := [(7024838656,112512739851612,112513127460078)]
theorem point_links_checked53565 : (cuts53565.take 1).map (fun c => (7024803841-1+2*2^10*c.k,112512679067516+c.lower,112513066675947+c.upper)) = pointBounds53565 := by
 decide +kernel
def cuts53566 : List PrefixCut := [⟨61,220652358,220652485⟩,
⟨64,231510581,231510714⟩]
theorem checked53566 : checkPrefixCuts (2^48) 7024934913 10 Manual.Count131072.C053566.packed 64 cuts53566 = true := by
 decide +kernel
def pointBounds53566 : List (Nat × Nat × Nat) := [(7025059840,112513135161466,112513522770156)]
theorem point_links_checked53566 : (cuts53566.take 1).map (fun c => (7024934913-1+2*2^10*c.k,112512914509108+c.lower,112513302117671+c.upper)) = pointBounds53566 := by
 decide +kernel
def cuts53567 : List PrefixCut := [⟨64,233429468,233429596⟩]
theorem checked53567 : checkPrefixCuts (2^48) 7025065985 10 Manual.Count131072.C053567.packed 64 cuts53567 = true := by
 decide +kernel
def cuts53568 : List PrefixCut := [⟨41,145921224,145921308⟩,
⟨64,227455258,227455389⟩]
theorem checked53568 : checkPrefixCuts (2^48) 7025197057 10 Manual.Count131072.C053568.packed 64 cuts53568 = true := by
 decide +kernel
def pointBounds53568 : List (Nat × Nat × Nat) := [(7025281024,112513525370381,112513912979289)]
theorem point_links_checked53568 : (cuts53568.take 1).map (fun c => (7025197057-1+2*2^10*c.k,112513379449157+c.lower,112513767057981+c.upper)) = pointBounds53568 := by
 decide +kernel
def cuts53569 : List PrefixCut := [⟨64,232258856,232258987⟩]
theorem checked53569 : checkPrefixCuts (2^48) 7025328129 10 Manual.Count131072.C053569.packed 64 cuts53569 = true := by
 decide +kernel
def cuts53570 : List PrefixCut := [⟨21,76644076,76644118⟩,
⟨64,232615115,232615244⟩]
theorem checked53570 : checkPrefixCuts (2^48) 7025459201 10 Manual.Count131072.C053570.packed 64 cuts53570 = true := by
 decide +kernel
def pointBounds53570 : List (Nat × Nat × Nat) := [(7025502208,112513915807347,112514303416475)]
theorem point_links_checked53570 : (cuts53570.take 1).map (fun c => (7025459201-1+2*2^10*c.k,112513839163271+c.lower,112514226772357+c.upper)) = pointBounds53570 := by
 decide +kernel
def cuts53571 : List PrefixCut := [⟨64,232811090,232811223⟩]
theorem checked53571 : checkPrefixCuts (2^48) 7025590273 10 Manual.Count131072.C053571.packed 64 cuts53571 = true := by
 decide +kernel
def cuts53572 : List PrefixCut := [⟨1,3685840,3685842⟩,
⟨64,235170469,235170602⟩]
theorem checked53572 : checkPrefixCuts (2^48) 7025721345 10 Manual.Count131072.C053572.packed 64 cuts53572 = true := by
 decide +kernel
def pointBounds53572 : List (Nat × Nat × Nat) := [(7025723392,112514308275316,112514695884666)]
theorem point_links_checked53572 : (cuts53572.take 1).map (fun c => (7025721345-1+2*2^10*c.k,112514304589476+c.lower,112514692198824+c.upper)) = pointBounds53572 := by
 decide +kernel
def cuts53573 : List PrefixCut := [⟨45,163615151,163615243⟩,
⟨64,236047434,236047566⟩]
theorem checked53573 : checkPrefixCuts (2^48) 7025852417 10 Manual.Count131072.C053573.packed 64 cuts53573 = true := by
 decide +kernel
def pointBounds53573 : List (Nat × Nat × Nat) := [(7025944576,112514703375096,112515090984669)]
theorem point_links_checked53573 : (cuts53573.take 1).map (fun c => (7025852417-1+2*2^10*c.k,112514539759945+c.lower,112514927369426+c.upper)) = pointBounds53573 := by
 decide +kernel
def cuts53574 : List PrefixCut := [⟨64,232477550,232477684⟩]
theorem checked53574 : checkPrefixCuts (2^48) 7025983489 10 Manual.Count131072.C053574.packed 64 cuts53574 = true := by
 decide +kernel
def cuts53575 : List PrefixCut := [⟨25,88855509,88855560⟩,
⟨64,229188218,229188351⟩]
theorem checked53575 : checkPrefixCuts (2^48) 7026114561 10 Manual.Count131072.C053575.packed 64 cuts53575 = true := by
 decide +kernel
def pointBounds53575 : List (Nat × Nat × Nat) := [(7026165760,112515097140438,112515484750236)]
theorem point_links_checked53575 : (cuts53575.take 1).map (fun c => (7026114561-1+2*2^10*c.k,112515008284929+c.lower,112515395894676+c.upper)) = pointBounds53575 := by
 decide +kernel
def cuts53576 : List PrefixCut := [⟨64,229744815,229744946⟩]
theorem checked53576 : checkPrefixCuts (2^48) 7026245633 10 Manual.Count131072.C053576.packed 64 cuts53576 = true := by
 decide +kernel
def cuts53577 : List PrefixCut := [⟨5,18667831,18667841⟩,
⟨64,230501658,230501788⟩]
theorem checked53577 : checkPrefixCuts (2^48) 7026376705 10 Manual.Count131072.C053577.packed 64 cuts53577 = true := by
 decide +kernel
def pointBounds53577 : List (Nat × Nat × Nat) := [(7026386944,112515485885793,112515873495814)]
theorem point_links_checked53577 : (cuts53577.take 1).map (fun c => (7026376705-1+2*2^10*c.k,112515467217962+c.lower,112515854827973+c.upper)) = pointBounds53577 := by
 decide +kernel
def cuts53578 : List PrefixCut := [⟨49,177860714,177860818⟩,
⟨64,233341520,233341654⟩]
theorem checked53578 : checkPrefixCuts (2^48) 7026507777 10 Manual.Count131072.C053578.packed 64 cuts53578 = true := by
 decide +kernel
def pointBounds53578 : List (Nat × Nat × Nat) := [(7026608128,112515875580334,112516263190579)]
theorem point_links_checked53578 : (cuts53578.take 1).map (fun c => (7026507777-1+2*2^10*c.k,112515697719620+c.lower,112516085329761+c.upper)) = pointBounds53578 := by
 decide +kernel
def cuts53579 : List PrefixCut := [⟨64,231254137,231254270⟩]
theorem checked53579 : checkPrefixCuts (2^48) 7026638849 10 Manual.Count131072.C053579.packed 64 cuts53579 = true := by
 decide +kernel
def cuts53580 : List PrefixCut := [⟨29,103788565,103788627⟩,
⟨64,228886468,228886601⟩]
theorem checked53580 : checkPrefixCuts (2^48) 7026769921 10 Manual.Count131072.C053580.packed 64 cuts53580 = true := by
 decide +kernel
def pointBounds53580 : List (Nat × Nat × Nat) := [(7026829312,112516266103842,112516653714312)]
theorem point_links_checked53580 : (cuts53580.take 1).map (fun c => (7026769921-1+2*2^10*c.k,112516162315277+c.lower,112516549925685+c.upper)) = pointBounds53580 := by
 decide +kernel
def cuts53581 : List PrefixCut := [⟨64,230163989,230164122⟩]
theorem checked53581 : checkPrefixCuts (2^48) 7026900993 10 Manual.Count131072.C053581.packed 64 cuts53581 = true := by
 decide +kernel
def cuts53582 : List PrefixCut := [⟨9,32285106,32285125⟩,
⟨64,227716309,227716440⟩]
theorem checked53582 : checkPrefixCuts (2^48) 7027032065 10 Manual.Count131072.C053582.packed 64 cuts53582 = true := by
 decide +kernel
def pointBounds53582 : List (Nat × Nat × Nat) := [(7027050496,112516653650840,112517041261533)]
theorem point_links_checked53582 : (cuts53582.take 1).map (fun c => (7027032065-1+2*2^10*c.k,112516621365734+c.lower,112517008976408+c.upper)) = pointBounds53582 := by
 decide +kernel
def cuts53583 : List PrefixCut := [⟨53,191863242,191863351⟩,
⟨64,231236895,231237026⟩]
theorem checked53583 : checkPrefixCuts (2^48) 7027163137 10 Manual.Count131072.C053583.packed 64 cuts53583 = true := by
 decide +kernel
def pointBounds53583 : List (Nat × Nat × Nat) := [(7027271680,112517040945285,112517428556199)]
theorem point_links_checked53583 : (cuts53583.take 1).map (fun c => (7027163137-1+2*2^10*c.k,112516849082043+c.lower,112517236692848+c.upper)) = pointBounds53583 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000111
