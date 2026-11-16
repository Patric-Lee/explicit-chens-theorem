import PlattAssemblyKernel
import PlattCertificates.Count131072.C052400
import PlattCertificates.Count131072.C052401
import PlattCertificates.Count131072.C052402
import PlattCertificates.Count131072.C052403
import PlattCertificates.Count131072.C052404
import PlattCertificates.Count131072.C052405
import PlattCertificates.Count131072.C052406
import PlattCertificates.Count131072.C052407
import PlattCertificates.Count131072.C052408
import PlattCertificates.Count131072.C052409
import PlattCertificates.Count131072.C052410
import PlattCertificates.Count131072.C052411
import PlattCertificates.Count131072.C052412
import PlattCertificates.Count131072.C052413
import PlattCertificates.Count131072.C052414
import PlattCertificates.Count131072.C052415
import PlattCertificates.Count131072.C052416
import PlattCertificates.Count131072.C052417
import PlattCertificates.Count131072.C052418
import PlattCertificates.Count131072.C052419
import PlattCertificates.Count131072.C052420
import PlattCertificates.Count131072.C052421
import PlattCertificates.Count131072.C052422
import PlattCertificates.Count131072.C052423
import PlattCertificates.Count131072.C052424
import PlattCertificates.Count131072.C052425
import PlattCertificates.Count131072.C052426
import PlattCertificates.Count131072.C052427
import PlattCertificates.Count131072.C052428
import PlattCertificates.Count131072.C052429
import PlattCertificates.Count131072.C052430
import PlattCertificates.Count131072.C052431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52400 : List PrefixCut := [⟨9,33914048,33914068⟩,
⟨64,239649112,239649250⟩]
theorem checked52400 : checkPrefixCuts (2^48) 6872104961 10 Manual.Count131072.C052400.packed 64 cuts52400 = true := by
 decide +kernel
def pointBounds52400 : List (Nat × Nat × Nat) := [(6872123392,112239748960947,112240136414407)]
theorem point_links_checked52400 : (cuts52400.take 1).map (fun c => (6872104961-1+2*2^10*c.k,112239715046899+c.lower,112240102500339+c.upper)) = pointBounds52400 := by
 decide +kernel
def cuts52401 : List PrefixCut := [⟨50,186153943,186154048⟩,
⟨64,239480706,239480840⟩]
theorem checked52401 : checkPrefixCuts (2^48) 6872236033 10 Manual.Count131072.C052401.packed 64 cuts52401 = true := by
 decide +kernel
def pointBounds52401 : List (Nat × Nat × Nat) := [(6872338432,112240140849954,112240528303637)]
theorem point_links_checked52401 : (cuts52401.take 1).map (fun c => (6872236033-1+2*2^10*c.k,112239954696011+c.lower,112240342149589+c.upper)) = pointBounds52401 := by
 decide +kernel
def cuts52402 : List PrefixCut := [⟨64,236281496,236281632⟩]
theorem checked52402 : checkPrefixCuts (2^48) 6872367105 10 Manual.Count131072.C052402.packed 64 cuts52402 = true := by
 decide +kernel
def cuts52403 : List PrefixCut := [⟨27,99442483,99442542⟩,
⟨64,235703609,235703744⟩]
theorem checked52403 : checkPrefixCuts (2^48) 6872498177 10 Manual.Count131072.C052403.packed 64 cuts52403 = true := by
 decide +kernel
def pointBounds52403 : List (Nat × Nat × Nat) := [(6872553472,112240529900696,112240917354603)]
theorem point_links_checked52403 : (cuts52403.take 1).map (fun c => (6872498177-1+2*2^10*c.k,112240430458213+c.lower,112240817912061+c.upper)) = pointBounds52403 := by
 decide +kernel
def cuts52404 : List PrefixCut := [⟨64,239180317,239180454⟩]
theorem checked52404 : checkPrefixCuts (2^48) 6872629249 10 Manual.Count131072.C052404.packed 64 cuts52404 = true := by
 decide +kernel
def cuts52405 : List PrefixCut := [⟨4,14252382,14252390⟩,
⟨64,234629793,234629924⟩]
theorem checked52405 : checkPrefixCuts (2^48) 6872760321 10 Manual.Count131072.C052405.packed 64 cuts52405 = true := by
 decide +kernel
def pointBounds52405 : List (Nat × Nat × Nat) := [(6872768512,112240919594521,112241307048649)]
theorem point_links_checked52405 : (cuts52405.take 1).map (fun c => (6872760321-1+2*2^10*c.k,112240905342139+c.lower,112241292796259+c.upper)) = pointBounds52405 := by
 decide +kernel
def cuts52406 : List PrefixCut := [⟨45,169672805,169672902⟩,
⟨64,241300828,241300965⟩]
theorem checked52406 : checkPrefixCuts (2^48) 6872891393 10 Manual.Count131072.C052406.packed 64 cuts52406 = true := by
 decide +kernel
def pointBounds52406 : List (Nat × Nat × Nat) := [(6872983552,112241309644737,112241697099085)]
theorem point_links_checked52406 : (cuts52406.take 1).map (fun c => (6872891393-1+2*2^10*c.k,112241139971932+c.lower,112241527426183+c.upper)) = pointBounds52406 := by
 decide +kernel
def cuts52407 : List PrefixCut := [⟨64,237610412,237610548⟩]
theorem checked52407 : checkPrefixCuts (2^48) 6873022465 10 Manual.Count131072.C052407.packed 64 cuts52407 = true := by
 decide +kernel
def cuts52408 : List PrefixCut := [⟨22,83133918,83133966⟩,
⟨64,237892577,237892713⟩]
theorem checked52408 : checkPrefixCuts (2^48) 6873153537 10 Manual.Count131072.C052408.packed 64 cuts52408 = true := by
 decide +kernel
def pointBounds52408 : List (Nat × Nat × Nat) := [(6873198592,112241702017090,112242089471662)]
theorem point_links_checked52408 : (cuts52408.take 1).map (fun c => (6873153537-1+2*2^10*c.k,112241618883172+c.lower,112242006337696+c.upper)) = pointBounds52408 := by
 decide +kernel
def cuts52409 : List PrefixCut := [⟨63,231827213,231827344⟩,
⟨64,235471874,235472007⟩]
theorem checked52409 : checkPrefixCuts (2^48) 6873284609 10 Manual.Count131072.C052409.packed 64 cuts52409 = true := by
 decide +kernel
def pointBounds52409 : List (Nat × Nat × Nat) := [(6873413632,112242088602962,112242476057753)]
theorem point_links_checked52409 : (cuts52409.take 1).map (fun c => (6873284609-1+2*2^10*c.k,112241856775749+c.lower,112242244230409+c.upper)) = pointBounds52409 := by
 decide +kernel
def cuts52410 : List PrefixCut := [⟨64,237473969,237474101⟩]
theorem checked52410 : checkPrefixCuts (2^48) 6873415681 10 Manual.Count131072.C052410.packed 64 cuts52410 = true := by
 decide +kernel
def cuts52411 : List PrefixCut := [⟨40,149304482,149304563⟩,
⟨64,237100903,237101033⟩]
theorem checked52411 : checkPrefixCuts (2^48) 6873546753 10 Manual.Count131072.C052411.packed 64 cuts52411 = true := by
 decide +kernel
def pointBounds52411 : List (Nat × Nat × Nat) := [(6873628672,112242479026074,112242866481080)]
theorem point_links_checked52411 : (cuts52411.take 1).map (fun c => (6873546753-1+2*2^10*c.k,112242329721592+c.lower,112242717176517+c.upper)) = pointBounds52411 := by
 decide +kernel
def cuts52412 : List PrefixCut := [⟨64,236850687,236850819⟩]
theorem checked52412 : checkPrefixCuts (2^48) 6873677825 10 Manual.Count131072.C052412.packed 64 cuts52412 = true := by
 decide +kernel
def cuts52413 : List PrefixCut := [⟨17,62528808,62528842⟩,
⟨64,236272886,236273020⟩]
theorem checked52413 : checkPrefixCuts (2^48) 6873808897 10 Manual.Count131072.C052413.packed 64 cuts52413 = true := by
 decide +kernel
def pointBounds52413 : List (Nat × Nat × Nat) := [(6873843712,112242866201990,112243253657211)]
theorem point_links_checked52413 : (cuts52413.take 1).map (fun c => (6873808897-1+2*2^10*c.k,112242803673182+c.lower,112243191128369+c.upper)) = pointBounds52413 := by
 decide +kernel
def cuts52414 : List PrefixCut := [⟨58,212764565,212764686⟩,
⟨64,234876146,234876280⟩]
theorem checked52414 : checkPrefixCuts (2^48) 6873939969 10 Manual.Count131072.C052414.packed 64 cuts52414 = true := by
 decide +kernel
def pointBounds52414 : List (Nat × Nat × Nat) := [(6874058752,112243252710633,112243640166075)]
theorem point_links_checked52414 : (cuts52414.take 1).map (fun c => (6873939969-1+2*2^10*c.k,112243039946068+c.lower,112243427401389+c.upper)) = pointBounds52414 := by
 decide +kernel
def cuts52415 : List PrefixCut := [⟨64,238761630,238761770⟩]
theorem checked52415 : checkPrefixCuts (2^48) 6874071041 10 Manual.Count131072.C052415.packed 64 cuts52415 = true := by
 decide +kernel
def cuts52416 : List PrefixCut := [⟨35,128817187,128817264⟩,
⟨64,235972740,235972877⟩]
theorem checked52416 : checkPrefixCuts (2^48) 6874202113 10 Manual.Count131072.C052416.packed 64 cuts52416 = true := by
 decide +kernel
def pointBounds52416 : List (Nat × Nat × Nat) := [(6874273792,112243642401031,112244029856703)]
theorem point_links_checked52416 : (cuts52416.take 1).map (fun c => (6874202113-1+2*2^10*c.k,112243513583844+c.lower,112243901039439+c.upper)) = pointBounds52416 := by
 decide +kernel
def cuts52417 : List PrefixCut := [⟨64,238384018,238384154⟩]
theorem checked52417 : checkPrefixCuts (2^48) 6874333185 10 Manual.Count131072.C052417.packed 64 cuts52417 = true := by
 decide +kernel
def cuts52418 : List PrefixCut := [⟨12,43033111,43033136⟩,
⟨64,236455081,236455218⟩]
theorem checked52418 : checkPrefixCuts (2^48) 6874464257 10 Manual.Count131072.C052418.packed 64 cuts52418 = true := by
 decide +kernel
def pointBounds52418 : List (Nat × Nat × Nat) := [(6874488832,112244030973713,112244418429606)]
theorem point_links_checked52418 : (cuts52418.take 1).map (fun c => (6874464257-1+2*2^10*c.k,112243987940602+c.lower,112244375396470+c.upper)) = pointBounds52418 := by
 decide +kernel
def cuts52419 : List PrefixCut := [⟨53,195466135,195466248⟩,
⟨64,235631708,235631844⟩]
theorem checked52419 : checkPrefixCuts (2^48) 6874595329 10 Manual.Count131072.C052419.packed 64 cuts52419 = true := by
 decide +kernel
def pointBounds52419 : List (Nat × Nat × Nat) := [(6874703872,112244419861818,112244807317936)]
theorem point_links_checked52419 : (cuts52419.take 1).map (fun c => (6874595329-1+2*2^10*c.k,112244224395683+c.lower,112244611851688+c.upper)) = pointBounds52419 := by
 decide +kernel
def cuts52420 : List PrefixCut := [⟨64,239353031,239353163⟩]
theorem checked52420 : checkPrefixCuts (2^48) 6874726401 10 Manual.Count131072.C052420.packed 64 cuts52420 = true := by
 decide +kernel
def cuts52421 : List PrefixCut := [⟨30,108947909,108947971⟩,
⟨64,235581748,235581879⟩]
theorem checked52421 : checkPrefixCuts (2^48) 6874857473 10 Manual.Count131072.C052421.packed 64 cuts52421 = true := by
 decide +kernel
def pointBounds52421 : List (Nat × Nat × Nat) := [(6874918912,112244808328331,112245195784666)]
theorem point_links_checked52421 : (cuts52421.take 1).map (fun c => (6874857473-1+2*2^10*c.k,112244699380422+c.lower,112245086836695+c.upper)) = pointBounds52421 := by
 decide +kernel
def cuts52422 : List PrefixCut := [⟨64,234717505,234717640⟩]
theorem checked52422 : checkPrefixCuts (2^48) 6874988545 10 Manual.Count131072.C052422.packed 64 cuts52422 = true := by
 decide +kernel
def cuts52423 : List PrefixCut := [⟨7,25547212,25547229⟩,
⟨64,238970854,238970990⟩]
theorem checked52423 : checkPrefixCuts (2^48) 6875119617 10 Manual.Count131072.C052423.packed 64 cuts52423 = true := by
 decide +kernel
def pointBounds52423 : List (Nat × Nat × Nat) := [(6875133952,112245195226887,112245582683443)]
theorem point_links_checked52423 : (cuts52423.take 1).map (fun c => (6875119617-1+2*2^10*c.k,112245169679675+c.lower,112245557136214+c.upper)) = pointBounds52423 := by
 decide +kernel
def cuts52424 : List PrefixCut := [⟨48,176574308,176574408⟩,
⟨64,236591802,236591935⟩]
theorem checked52424 : checkPrefixCuts (2^48) 6875250689 10 Manual.Count131072.C052424.packed 64 cuts52424 = true := by
 decide +kernel
def pointBounds52424 : List (Nat × Nat × Nat) := [(6875348992,112245585224837,112245972681612)]
theorem point_links_checked52424 : (cuts52424.take 1).map (fun c => (6875250689-1+2*2^10*c.k,112245408650529+c.lower,112245796107204+c.upper)) = pointBounds52424 := by
 decide +kernel
def cuts52425 : List PrefixCut := [⟨64,238511401,238511540⟩]
theorem checked52425 : checkPrefixCuts (2^48) 6875381761 10 Manual.Count131072.C052425.packed 64 cuts52425 = true := by
 decide +kernel
def cuts52426 : List PrefixCut := [⟨25,93135310,93135364⟩,
⟨64,238670636,238670776⟩]
theorem checked52426 : checkPrefixCuts (2^48) 6875512833 10 Manual.Count131072.C052426.packed 64 cuts52426 = true := by
 decide +kernel
def pointBounds52426 : List (Nat × Nat × Nat) := [(6875564032,112245976889042,112246364346043)]
theorem point_links_checked52426 : (cuts52426.take 1).map (fun c => (6875512833-1+2*2^10*c.k,112245883753732+c.lower,112246271210679+c.upper)) = pointBounds52426 := by
 decide +kernel
def cuts52427 : List PrefixCut := [⟨64,237192321,237192456⟩]
theorem checked52427 : checkPrefixCuts (2^48) 6875643905 10 Manual.Count131072.C052427.packed 64 cuts52427 = true := by
 decide +kernel
def cuts52428 : List PrefixCut := [⟨2,7859938,7859942⟩,
⟨64,237187835,237187970⟩]
theorem checked52428 : checkPrefixCuts (2^48) 6875774977 10 Manual.Count131072.C052428.packed 64 cuts52428 = true := by
 decide +kernel
def pointBounds52428 : List (Nat × Nat × Nat) := [(6875779072,112246367476627,112246754933853)]
theorem point_links_checked52428 : (cuts52428.take 1).map (fun c => (6875774977-1+2*2^10*c.k,112246359616689+c.lower,112246747073911+c.upper)) = pointBounds52428 := by
 decide +kernel
def cuts52429 : List PrefixCut := [⟨43,160183152,160183243⟩,
⟨64,238124835,238124972⟩]
theorem checked52429 : checkPrefixCuts (2^48) 6875906049 10 Manual.Count131072.C052429.packed 64 cuts52429 = true := by
 decide +kernel
def pointBounds52429 : List (Nat × Nat × Nat) := [(6875994112,112246756987676,112247144445124)]
theorem point_links_checked52429 : (cuts52429.take 1).map (fun c => (6875906049-1+2*2^10*c.k,112246596804524+c.lower,112246984261881+c.upper)) = pointBounds52429 := by
 decide +kernel
def cuts52430 : List PrefixCut := [⟨64,238488706,238488841⟩]
theorem checked52430 : checkPrefixCuts (2^48) 6876037121 10 Manual.Count131072.C052430.packed 64 cuts52430 = true := by
 decide +kernel
def cuts52431 : List PrefixCut := [⟨20,73109421,73109462⟩,
⟨64,234063209,234063343⟩]
theorem checked52431 : checkPrefixCuts (2^48) 6876168193 10 Manual.Count131072.C052431.packed 64 cuts52431 = true := by
 decide +kernel
def pointBounds52431 : List (Nat × Nat × Nat) := [(6876209152,112247146527486,112247533985156)]
theorem point_links_checked52431 : (cuts52431.take 1).map (fun c => (6876168193-1+2*2^10*c.k,112247073418065+c.lower,112247460875694+c.upper)) = pointBounds52431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000075
